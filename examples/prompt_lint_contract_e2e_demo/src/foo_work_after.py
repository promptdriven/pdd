"""
foo_work.py

Idempotent request handler with JWT authorization, active-user checks,
and a 24-hour idempotency store. Standard library only.
"""

import base64
import json
import logging
import threading
import time
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from typing import Any, Dict, List, Optional, Tuple

logger = logging.getLogger(__name__)

# Module-level audit log (in-memory)
AUDIT_LOG: List[str] = []

# TTL for idempotency entries: 24 hours
_IDEMPOTENCY_TTL_SECONDS: int = 24 * 60 * 60

# Required JWT scope to invoke the handler
_REQUIRED_SCOPE: str = "foo:invoke"

# Active-user window in days (inclusive)
_ACTIVE_USER_MAX_DAYS: int = 5


# ----------------------------------------------------------------------------
# Dataclasses
# ----------------------------------------------------------------------------

@dataclass
class RequestContext:
    """Incoming HTTP-like request context."""
    authorization: Optional[str]
    idempotency_key: Optional[str]
    request_received_at: datetime
    body_bytes: Optional[bytes]


@dataclass
class UserProfile:
    """User profile information used for active-user checks."""
    user_id: str
    last_login_at: datetime


@dataclass
class HandlerResult:
    """Result of handling a request."""
    status_code: int
    body: Dict[str, Any]


# ----------------------------------------------------------------------------
# Idempotency Store
# ----------------------------------------------------------------------------

class IdempotencyStore:
    """
    In-process idempotency store with a 24-hour TTL per key.

    Each entry maps `key -> {"request_id": str, "recorded_at": float}` where
    `recorded_at` is the monotonic-ish wall-clock time (time.time()) at first
    acceptance. Entries older than TTL are evicted on read/write.

    Per-key locks are exposed via :meth:`lock_for` so callers can perform an
    atomic check-then-set for concurrent same-key requests.
    """

    def __init__(self, ttl_seconds: int = _IDEMPOTENCY_TTL_SECONDS) -> None:
        self._ttl_seconds: int = ttl_seconds
        self._entries: Dict[str, Dict[str, Any]] = {}
        self._key_locks: Dict[str, threading.Lock] = {}
        self._global_lock: threading.Lock = threading.Lock()

    # -- internal helpers -----------------------------------------------------

    def _evict_expired(self) -> None:
        """Remove any expired entries. Caller need not hold _global_lock."""
        now = time.time()
        with self._global_lock:
            expired_keys = [
                k for k, v in self._entries.items()
                if (now - v.get("recorded_at", 0.0)) > self._ttl_seconds
            ]
            for k in expired_keys:
                self._entries.pop(k, None)
                # Don't pop the lock; harmless to keep and avoids races.

    # -- public API -----------------------------------------------------------

    def lock_for(self, key: str) -> threading.Lock:
        """Return (creating if needed) a per-key lock for atomic check-then-set."""
        with self._global_lock:
            lock = self._key_locks.get(key)
            if lock is None:
                lock = threading.Lock()
                self._key_locks[key] = lock
            return lock

    def has(self, key: str) -> bool:
        """Return True iff a non-expired entry exists for `key`."""
        self._evict_expired()
        with self._global_lock:
            return key in self._entries

    def get_request_id(self, key: str) -> Optional[str]:
        """Return the stored request_id for `key`, or None if missing/expired."""
        self._evict_expired()
        with self._global_lock:
            entry = self._entries.get(key)
            if entry is None:
                return None
            return entry.get("request_id")

    def record(self, key: str, request_id: str) -> None:
        """
        Record a first-acceptance entry for `key`.

        This method does NOT overwrite an existing non-expired entry; callers
        should use :meth:`has` (under the per-key lock) before calling.
        """
        self._evict_expired()
        with self._global_lock:
            if key in self._entries:
                # Don't corrupt stored state on duplicate writes.
                return
            self._entries[key] = {
                "request_id": request_id,
                "recorded_at": time.time(),
            }


# ----------------------------------------------------------------------------
# JWT parsing (payload-only, base64url decode; no signature verification)
# ----------------------------------------------------------------------------

def _b64url_decode(segment: str) -> bytes:
    """Base64url-decode a JWT segment, adding padding as needed."""
    padding = "=" * (-len(segment) % 4)
    return base64.urlsafe_b64decode(segment + padding)


def parse_bearer_jwt(
    authorization: Optional[str],
) -> Tuple[bool, Optional[Dict[str, Any]], Optional[str]]:
    """
    Parse a `Bearer <jwt>` Authorization header.

    Returns (ok, claims, error):
      - ok=True, claims=<dict>, error=None on success
      - ok=False, claims=None,  error=<reason> on failure

    Validates:
      * Header presence and `Bearer ` prefix
      * Three-segment JWT structure
      * Decodable base64url payload that is a JSON object
      * `exp` claim present and in the future (unix seconds)
      * `scope` claim present and contains `foo:invoke`
    """
    if not authorization or not isinstance(authorization, str):
        return False, None, "missing_authorization"

    parts = authorization.strip().split(" ", 1)
    if len(parts) != 2 or parts[0].lower() != "bearer" or not parts[1].strip():
        return False, None, "malformed_authorization"

    token = parts[1].strip()
    segments = token.split(".")
    if len(segments) != 3:
        return False, None, "malformed_jwt"

    try:
        payload_bytes = _b64url_decode(segments[1])
        claims = json.loads(payload_bytes.decode("utf-8"))
    except Exception:
        return False, None, "malformed_jwt_payload"

    if not isinstance(claims, dict):
        return False, None, "malformed_jwt_payload"

    # exp must exist and be in the future
    exp = claims.get("exp")
    if not isinstance(exp, (int, float)):
        return False, None, "missing_exp"
    if exp <= time.time():
        return False, None, "expired_token"

    # scope must contain foo:invoke (string or list)
    scope = claims.get("scope")
    has_scope = False
    if isinstance(scope, str):
        has_scope = _REQUIRED_SCOPE in scope.split()
    elif isinstance(scope, (list, tuple)):
        has_scope = _REQUIRED_SCOPE in scope
    if not has_scope:
        return False, None, "insufficient_scope"

    return True, claims, None


# ----------------------------------------------------------------------------
# Active user check
# ----------------------------------------------------------------------------

def is_active_user(user: UserProfile, at: datetime) -> bool:
    """
    Return True iff (at - user.last_login_at).days <= 5.

    Both datetimes are expected to be timezone-aware.
    """
    delta = at - user.last_login_at
    return delta.days <= _ACTIVE_USER_MAX_DAYS


# ----------------------------------------------------------------------------
# Audit
# ----------------------------------------------------------------------------

def _append_audit(caller_id: str, request_id: str, amount_cents: Optional[int]) -> None:
    """
    Append a single audit line to AUDIT_LOG.

    May raise; the caller is responsible for handling failures gracefully.
    """
    if amount_cents is None:
        line = f"caller={caller_id} request_id={request_id} amount_cents=-"
    else:
        line = f"caller={caller_id} request_id={request_id} amount_cents={amount_cents}"
    AUDIT_LOG.append(line)


# ----------------------------------------------------------------------------
# Main handler
# ----------------------------------------------------------------------------

def handle_request(
    ctx: RequestContext,
    user: UserProfile,
    store: IdempotencyStore,
) -> HandlerResult:
    """
    Handle an incoming request idempotently.

    Processing order (strict):
        auth -> idempotency key -> active user -> duplicate check ->
        body validation -> store write -> audit -> response
    """
    # 1. Authorization
    ok, claims, auth_err = parse_bearer_jwt(ctx.authorization)
    if not ok:
        return HandlerResult(
            status_code=401,
            body={"reason": "unauthorized", "error": auth_err or "unauthorized"},
        )
    assert claims is not None  # for type-checkers

    caller_id = str(claims.get("sub", ""))

    # 2. Idempotency key presence
    idem_key = ctx.idempotency_key
    if not isinstance(idem_key, str) or not idem_key:
        return HandlerResult(
            status_code=400,
            body={"reason": "missing_idempotency_key"},
        )

    # 3. Active user
    if not is_active_user(user, ctx.request_received_at):
        return HandlerResult(
            status_code=403,
            body={"reason": "inactive_user"},
        )

    # 4 + 5 + 6. Duplicate check + body validation + store write must be
    # serialized per idempotency key to prevent two concurrent requests from
    # both being accepted.
    key_lock = store.lock_for(idem_key)
    with key_lock:
        # 4. Duplicate check (within TTL)
        if store.has(idem_key):
            original = store.get_request_id(idem_key)
            return HandlerResult(
                status_code=409,
                body={
                    "reason": "duplicate",
                    "original_request_id": original,
                },
            )

        # 5. Body validation (only after we know this key is new)
        amount_cents: Optional[int] = None
        if ctx.body_bytes is not None and len(ctx.body_bytes) > 0:
            try:
                parsed = json.loads(ctx.body_bytes.decode("utf-8"))
            except Exception:
                # Malformed JSON -> 400, no store mutation.
                return HandlerResult(
                    status_code=400,
                    body={"reason": "malformed_json"},
                )

            if not isinstance(parsed, dict):
                return HandlerResult(
                    status_code=400,
                    body={"reason": "malformed_json"},
                )

            raw_amount = parsed.get("amount_cents", None)
            if raw_amount is not None:
                if not isinstance(raw_amount, int) or isinstance(raw_amount, bool):
                    return HandlerResult(
                        status_code=422,
                        body={"reason": "invalid_amount_cents"},
                    )
                if raw_amount <= 0:
                    return HandlerResult(
                        status_code=422,
                        body={"reason": "invalid_amount_cents"},
                    )
                amount_cents = raw_amount

            # `note` is optional and unused beyond presence; ignore silently.

        # 6. Store write (first acceptance)
        request_id = str(uuid.uuid4())
        store.record(idem_key, request_id)

    # 7. Audit (HTTP 200 only). Failures must not break the success response.
    audit_failed = False
    try:
        _append_audit(caller_id, request_id, amount_cents)
    except Exception:
        logger.exception("audit log append failed")
        audit_failed = True

    # 8. Response
    body: Dict[str, Any] = {
        "result": "ok",
        "request_id": request_id,
        "amount_cents": amount_cents,
    }
    if audit_failed:
        body["audit_failed"] = True

    return HandlerResult(status_code=200, body=body)