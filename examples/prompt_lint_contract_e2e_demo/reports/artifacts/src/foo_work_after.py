# src/foo_work.py

"""
foo_work
--------

An idempotent request handler with JWT authorization, active-user checks,
and a 24-hour idempotency store. Uses only the Python standard library.

Public symbols:
    - RequestContext (dataclass)
    - UserProfile (dataclass)
    - HandlerResult (dataclass)
    - IdempotencyStore (class)
    - parse_bearer_jwt(authorization) -> (ok, claims, error)
    - is_active_user(user, at) -> bool
    - handle_request(ctx, user, store) -> HandlerResult
    - AUDIT_LOG (module-level list[str])
"""

from __future__ import annotations

import base64
import json
import threading
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from typing import Any, Optional

# --------------------------------------------------------------------------- #
# Module-level state
# --------------------------------------------------------------------------- #

AUDIT_LOG: list[str] = []

# TTL for idempotency records.
_IDEMPOTENCY_TTL = timedelta(hours=24)

# Required scope value for JWTs.
_REQUIRED_SCOPE = "foo:invoke"

# Lock to protect AUDIT_LOG appends and per-key lock dictionary creation.
_AUDIT_LOCK = threading.Lock()


# --------------------------------------------------------------------------- #
# Dataclasses
# --------------------------------------------------------------------------- #


@dataclass
class RequestContext:
    """Incoming request context."""
    authorization: Optional[str]
    idempotency_key: Optional[str]
    request_received_at: datetime
    body_bytes: Optional[bytes]


@dataclass
class UserProfile:
    """User profile information needed for active-user checks."""
    user_id: str
    last_login_at: datetime


@dataclass
class HandlerResult:
    """Result of handling a request."""
    status_code: int
    body: dict


# --------------------------------------------------------------------------- #
# IdempotencyStore
# --------------------------------------------------------------------------- #


class IdempotencyStore:
    """
    In-process idempotency store with 24-hour TTL.

    Records are evicted lazily on read and write whenever a key is touched.
    """

    def __init__(self) -> None:
        # key -> {"request_id": str, "recorded_at": datetime}
        self._records: dict[str, dict[str, Any]] = {}
        # Global lock for store-level dictionary mutations.
        self._lock = threading.Lock()
        # Per-key locks for atomic check-then-set semantics.
        self._key_locks: dict[str, threading.Lock] = {}

    # ------------------------ internal helpers ----------------------------- #

    def _now(self) -> datetime:
        return datetime.now(timezone.utc)

    def _is_expired(self, recorded_at: datetime, now: Optional[datetime] = None) -> bool:
        now = now or self._now()
        return (now - recorded_at) >= _IDEMPOTENCY_TTL

    def _evict_if_expired(self, key: str) -> None:
        rec = self._records.get(key)
        if rec is not None and self._is_expired(rec["recorded_at"]):
            self._records.pop(key, None)

    def get_key_lock(self, key: str) -> threading.Lock:
        """Obtain (or create) a lock dedicated to a single idempotency key."""
        with self._lock:
            lock = self._key_locks.get(key)
            if lock is None:
                lock = threading.Lock()
                self._key_locks[key] = lock
            return lock

    # ------------------------ public API ----------------------------------- #

    def has(self, key: str) -> bool:
        """Return True if a non-expired record exists for `key`."""
        with self._lock:
            self._evict_if_expired(key)
            return key in self._records

    def record(self, key: str, request_id: str) -> None:
        """Record a new (key -> request_id) entry with current timestamp."""
        with self._lock:
            self._evict_if_expired(key)
            self._records[key] = {
                "request_id": request_id,
                "recorded_at": self._now(),
            }

    def get_request_id(self, key: str) -> Optional[str]:
        """Return the stored request_id for `key` or None if absent/expired."""
        with self._lock:
            self._evict_if_expired(key)
            rec = self._records.get(key)
            return rec["request_id"] if rec is not None else None


# --------------------------------------------------------------------------- #
# JWT parsing (payload only, no signature verification)
# --------------------------------------------------------------------------- #


def _b64url_decode(segment: str) -> bytes:
    """Base64url-decode, adding padding as required."""
    # Ensure ASCII string
    segment_bytes = segment.encode("ascii")
    padding = b"=" * (-len(segment_bytes) % 4)
    return base64.urlsafe_b64decode(segment_bytes + padding)


def parse_bearer_jwt(
    authorization: Optional[str],
) -> tuple[bool, Optional[dict], Optional[str]]:
    """
    Parse and validate a 'Bearer <jwt>' authorization header.

    Returns:
        (ok, claims, error)
          ok=True if header is well-formed, payload decodes, contains 'exp'
          in the future, and includes 'foo:invoke' in scope.
          Otherwise ok=False with error message and claims=None.

    Note: This function does NOT verify the JWT signature.
    """
    if not authorization or not isinstance(authorization, str):
        return False, None, "missing_authorization"

    parts = authorization.split(" ", 1)
    if len(parts) != 2 or parts[0] != "Bearer" or not parts[1].strip():
        return False, None, "malformed_authorization"

    token = parts[1].strip()
    segments = token.split(".")
    if len(segments) < 2:
        return False, None, "malformed_jwt"

    payload_segment = segments[1]
    try:
        payload_bytes = _b64url_decode(payload_segment)
        claims = json.loads(payload_bytes.decode("utf-8"))
    except (ValueError, UnicodeDecodeError, json.JSONDecodeError, base64.binascii.Error):
        return False, None, "undecodable_payload"

    if not isinstance(claims, dict):
        return False, None, "invalid_claims"

    exp = claims.get("exp")
    if not isinstance(exp, (int, float)):
        return False, None, "missing_or_invalid_exp"

    now_ts = datetime.now(timezone.utc).timestamp()
    if exp <= now_ts:
        return False, None, "expired"

    scope = claims.get("scope")
    scopes: list[str]
    if isinstance(scope, str):
        scopes = scope.split()
    elif isinstance(scope, (list, tuple)):
        scopes = [str(s) for s in scope]
    else:
        return False, None, "missing_scope"

    if _REQUIRED_SCOPE not in scopes:
        return False, None, "insufficient_scope"

    return True, claims, None


# --------------------------------------------------------------------------- #
# Active user check
# --------------------------------------------------------------------------- #


def is_active_user(user: UserProfile, at: datetime) -> bool:
    """A user is active if last_login_at is within the last 5 days (inclusive)."""
    delta = at - user.last_login_at
    return delta.days <= 5


# --------------------------------------------------------------------------- #
# Handler
# --------------------------------------------------------------------------- #


def _audit_append(sub: Any, request_id: str, amount_cents: Optional[int]) -> bool:
    """
    Append an audit line. Returns True on success, False on failure.
    Failure leaves AUDIT_LOG unmodified.
    """
    try:
        line = f"sub={sub} request_id={request_id} amount_cents={amount_cents}"
        with _AUDIT_LOCK:
            AUDIT_LOG.append(line)
        return True
    except Exception:
        return False


def handle_request(
    ctx: RequestContext,
    user: UserProfile,
    store: IdempotencyStore,
) -> HandlerResult:
    """
    Process an incoming request idempotently with all checks.

    Processing order (do not reorder):
        auth -> idempotency key -> active user -> duplicate check
        -> body validation -> store write -> audit -> response.
    """
    # 1) Authorization
    ok, claims, _err = parse_bearer_jwt(ctx.authorization)
    if not ok:
        return HandlerResult(status_code=401, body={"reason": "unauthorized"})

    # 2) Idempotency key presence
    key = ctx.idempotency_key
    if not isinstance(key, str) or not key:
        return HandlerResult(
            status_code=400,
            body={"reason": "missing_idempotency_key"},
        )

    # 3) Active user check
    if not is_active_user(user, ctx.request_received_at):
        return HandlerResult(status_code=403, body={"reason": "inactive_user"})

    # 4 & 5 & 6) Duplicate check + body validation + store write
    # Use per-key lock to ensure check-then-set atomicity under concurrency.
    key_lock = store.get_key_lock(key)
    with key_lock:
        # Duplicate check (under lock).
        existing = store.get_request_id(key)
        if existing is not None:
            return HandlerResult(
                status_code=409,
                body={"reason": "duplicate", "original_request_id": existing},
            )

        # Body validation (under lock so that we don't accidentally write
        # to the store on a bad payload, and the per-key state is consistent).
        amount_cents: Optional[int] = None
        body_bytes = ctx.body_bytes
        if body_bytes is not None and len(body_bytes) > 0:
            try:
                parsed = json.loads(body_bytes.decode("utf-8"))
            except (ValueError, UnicodeDecodeError, json.JSONDecodeError):
                return HandlerResult(
                    status_code=400,
                    body={"reason": "invalid_json"},
                )

            if not isinstance(parsed, dict):
                return HandlerResult(
                    status_code=400,
                    body={"reason": "invalid_json_shape"},
                )

            if "amount_cents" in parsed:
                value = parsed["amount_cents"]
                if not isinstance(value, int) or isinstance(value, bool):
                    return HandlerResult(
                        status_code=422,
                        body={"reason": "invalid_amount_cents"},
                    )
                if value <= 0:
                    return HandlerResult(
                        status_code=422,
                        body={"reason": "non_positive_amount_cents"},
                    )
                amount_cents = value

        # Store write.
        request_id = str(uuid.uuid4())
        store.record(key, request_id)

    # 7) Audit (outside per-key lock to keep that critical section short).
    response_body: dict[str, Any] = {
        "result": "ok",
        "request_id": request_id,
        "amount_cents": amount_cents,
    }

    sub = claims.get("sub") if isinstance(claims, dict) else None
    if not _audit_append(sub, request_id, amount_cents):
        response_body["audit_failed"] = True

    # 8) Response
    return HandlerResult(status_code=200, body=response_body)