"""
foo_work.py - Idempotent request handler with JWT authorization,
active-user checks, and a 24-hour idempotency store.

Standard library only.
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

# Configure logger
logger = logging.getLogger(__name__)

# Module-level audit log (append-only list of audit lines)
AUDIT_LOG: List[str] = []

# Constants
IDEMPOTENCY_TTL_SECONDS: int = 24 * 60 * 60  # 24 hours
ACTIVE_USER_MAX_DAYS: int = 5
REQUIRED_SCOPE: str = "foo:invoke"


# -----------------------------------------------------------------------------
# Data Classes
# -----------------------------------------------------------------------------

@dataclass
class RequestContext:
    """Encapsulates the incoming request's relevant fields."""
    authorization: Optional[str]
    idempotency_key: Optional[str]
    request_received_at: datetime
    body_bytes: Optional[bytes]


@dataclass
class UserProfile:
    """Represents the caller's user profile."""
    user_id: str
    last_login_at: datetime


@dataclass
class HandlerResult:
    """Represents the HTTP response from the handler."""
    status_code: int
    body: Dict[str, Any]


# -----------------------------------------------------------------------------
# Idempotency Store
# -----------------------------------------------------------------------------

class IdempotencyStore:
    """
    In-process idempotency store with 24-hour TTL.
    
    Entries are stored as {key: (request_id, recorded_at_epoch)}.
    TTL eviction occurs on every read or write operation.
    """

    def __init__(self, ttl_seconds: int = IDEMPOTENCY_TTL_SECONDS) -> None:
        self._ttl_seconds = ttl_seconds
        self._store: Dict[str, Tuple[str, float]] = {}
        self._global_lock = threading.Lock()
        self._key_locks: Dict[str, threading.Lock] = {}

    def _evict_expired(self) -> None:
        """Remove expired entries. Caller must hold _global_lock."""
        now = time.time()
        expired_keys = [
            k for k, (_, recorded_at) in self._store.items()
            if (now - recorded_at) >= self._ttl_seconds
        ]
        for k in expired_keys:
            self._store.pop(k, None)

    def has(self, key: str) -> bool:
        """Return True if a non-expired entry exists for `key`."""
        with self._global_lock:
            self._evict_expired()
            return key in self._store

    def record(self, key: str, request_id: str) -> None:
        """Record a new entry (request_id, current time) under `key`."""
        with self._global_lock:
            self._evict_expired()
            self._store[key] = (request_id, time.time())

    def get_request_id(self, key: str) -> Optional[str]:
        """Return the stored request_id for `key` or None if missing/expired."""
        with self._global_lock:
            self._evict_expired()
            entry = self._store.get(key)
            if entry is None:
                return None
            return entry[0]

    def get_key_lock(self, key: str) -> threading.Lock:
        """Return (creating if needed) a per-key lock for check-then-set semantics."""
        with self._global_lock:
            lock = self._key_locks.get(key)
            if lock is None:
                lock = threading.Lock()
                self._key_locks[key] = lock
            return lock


# -----------------------------------------------------------------------------
# JWT Parsing (payload only, no signature verification - demo only)
# -----------------------------------------------------------------------------

def _b64url_decode(segment: str) -> bytes:
    """Decode a base64url-encoded string, adding padding as needed."""
    padding = "=" * (-len(segment) % 4)
    return base64.urlsafe_b64decode(segment + padding)


def parse_bearer_jwt(
    authorization: Optional[str],
) -> Tuple[bool, Optional[Dict[str, Any]], Optional[str]]:
    """
    Parse and validate a Bearer JWT from the Authorization header.
    
    Validates:
    - Header presence and 'Bearer ' prefix
    - Token has three dot-separated segments
    - Payload is valid base64url-encoded JSON
    - `exp` claim is present and in the future
    - `scope` claim contains `foo:invoke`
    
    Does NOT verify the signature (this is a demo).
    
    Returns:
        (ok, claims, error): On success, (True, claims_dict, None).
                             On failure, (False, None, error_message).
    """
    if not authorization or not isinstance(authorization, str):
        return False, None, "missing_authorization"

    if not authorization.startswith("Bearer "):
        return False, None, "malformed_authorization"

    token = authorization[len("Bearer "):].strip()
    if not token:
        return False, None, "empty_token"

    parts = token.split(".")
    if len(parts) != 3:
        return False, None, "malformed_jwt"

    try:
        payload_bytes = _b64url_decode(parts[1])
        claims = json.loads(payload_bytes.decode("utf-8"))
    except (ValueError, UnicodeDecodeError, json.JSONDecodeError):
        return False, None, "malformed_payload"

    if not isinstance(claims, dict):
        return False, None, "invalid_claims"

    # Validate exp
    exp = claims.get("exp")
    if not isinstance(exp, (int, float)):
        return False, None, "missing_or_invalid_exp"

    now_epoch = time.time()
    if exp <= now_epoch:
        return False, None, "expired_token"

    # Validate scope
    scope = claims.get("scope")
    if scope is None:
        return False, None, "missing_scope"

    if isinstance(scope, str):
        scopes = scope.split()
    elif isinstance(scope, list):
        scopes = [str(s) for s in scope]
    else:
        return False, None, "invalid_scope"

    if REQUIRED_SCOPE not in scopes:
        return False, None, "insufficient_scope"

    return True, claims, None


# -----------------------------------------------------------------------------
# Active User Check
# -----------------------------------------------------------------------------

def is_active_user(user: UserProfile, at: datetime) -> bool:
    """
    Return True if the user's last login was within the active window.
    
    A user is active when (at - user.last_login_at).days <= ACTIVE_USER_MAX_DAYS.
    Both datetimes must be timezone-aware.
    """
    if user.last_login_at is None or at is None:
        return False

    delta = at - user.last_login_at
    return delta.days <= ACTIVE_USER_MAX_DAYS and delta.total_seconds() >= 0


# -----------------------------------------------------------------------------
# Audit Logging
# -----------------------------------------------------------------------------

def _append_audit(caller_id: str, request_id: str, amount_cents: Optional[int]) -> bool:
    """
    Append an audit line to AUDIT_LOG.
    
    Returns True on success, False if appending failed.
    """
    try:
        line = json.dumps({
            "caller_id": caller_id,
            "request_id": request_id,
            "amount_cents": amount_cents,
            "timestamp": datetime.now(timezone.utc).isoformat(),
        })
        AUDIT_LOG.append(line)
        return True
    except Exception as e:  # pragma: no cover - defensive
        logger.warning("Audit logging failed: %s", e)
        return False


# -----------------------------------------------------------------------------
# Main Handler
# -----------------------------------------------------------------------------

def handle_request(
    ctx: RequestContext,
    user: UserProfile,
    store: IdempotencyStore,
) -> HandlerResult:
    """
    Handle an incoming request with full processing order:
    auth -> idempotency key -> active user -> duplicate check ->
    body validation -> store write -> audit -> response.
    """

    # 1. Authorization
    ok, claims, err = parse_bearer_jwt(ctx.authorization)
    if not ok:
        logger.info("Unauthorized request: %s", err)
        return HandlerResult(
            status_code=401,
            body={"reason": "unauthorized", "error": err or "unauthorized"},
        )

    caller_id = str(claims.get("sub", "")) if claims else ""

    # 2. Idempotency key presence
    if not ctx.idempotency_key or not isinstance(ctx.idempotency_key, str):
        return HandlerResult(
            status_code=400,
            body={"reason": "missing_idempotency_key"},
        )

    idem_key = ctx.idempotency_key

    # 3. Active user check
    if not is_active_user(user, ctx.request_received_at):
        return HandlerResult(
            status_code=403,
            body={"reason": "inactive_user"},
        )

    # 4 + 5 + 6. Duplicate check + body validation + store write,
    # all under per-key lock for concurrency safety.
    key_lock = store.get_key_lock(idem_key)
    with key_lock:
        # Duplicate check (inside lock for check-then-set semantics)
        existing_request_id = store.get_request_id(idem_key)
        if existing_request_id is not None:
            return HandlerResult(
                status_code=409,
                body={
                    "reason": "duplicate",
                    "original_request_id": existing_request_id,
                },
            )

        # Body validation
        amount_cents: Optional[int] = None
        note: Optional[str] = None

        if ctx.body_bytes is not None and len(ctx.body_bytes) > 0:
            try:
                parsed = json.loads(ctx.body_bytes.decode("utf-8"))
            except (ValueError, UnicodeDecodeError):
                return HandlerResult(
                    status_code=400,
                    body={"reason": "malformed_json"},
                )

            if not isinstance(parsed, dict):
                return HandlerResult(
                    status_code=400,
                    body={"reason": "malformed_json"},
                )

            if "amount_cents" in parsed:
                ac = parsed.get("amount_cents")
                if not isinstance(ac, int) or isinstance(ac, bool):
                    return HandlerResult(
                        status_code=422,
                        body={"reason": "invalid_amount_cents"},
                    )
                if ac <= 0:
                    return HandlerResult(
                        status_code=422,
                        body={"reason": "invalid_amount_cents"},
                    )
                amount_cents = ac

            if "note" in parsed:
                n = parsed.get("note")
                if n is not None and not isinstance(n, str):
                    return HandlerResult(
                        status_code=422,
                        body={"reason": "invalid_note"},
                    )
                note = n

        # Store write (first acceptance for this key)
        request_id = str(uuid.uuid4())
        store.record(idem_key, request_id)

    # 7. Audit logging (outside per-key lock; only on successful store write)
    audit_ok = _append_audit(caller_id, request_id, amount_cents)

    # 8. Response
    response_body: Dict[str, Any] = {
        "result": "ok",
        "request_id": request_id,
        "amount_cents": amount_cents,
    }
    if not audit_ok:
        response_body["audit_failed"] = True

    # Include note in audit context but not the response (response shape is fixed)
    _ = note  # currently unused in response shape

    return HandlerResult(status_code=200, body=response_body)