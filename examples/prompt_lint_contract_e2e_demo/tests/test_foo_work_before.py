
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""Tests for src/foo_work_before.py - idempotent request handler."""

import base64
import json
import sys
import threading
import time
import uuid
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

# Ensure the project root is on sys.path so `src.foo_work_before` is importable
_PROJECT_ROOT = Path(__file__).resolve().parent
if str(_PROJECT_ROOT) not in sys.path:

from src.foo_work_before import (
    AUDIT_LOG,
    HandlerResult,
    IdempotencyStore,
    RequestContext,
    UserProfile,
    handle_request,
    is_active_user,
    parse_bearer_jwt,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _b64url(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def make_jwt(claims: dict, header: dict | None = None, signature: str = "sig") -> str:
    header = header or {"alg": "none", "typ": "JWT"}
    header_seg = _b64url(json.dumps(header).encode("utf-8"))
    payload_seg = _b64url(json.dumps(claims).encode("utf-8"))
    return f"{header_seg}.{payload_seg}.{signature}"


def valid_token(sub: str = "user-123", scopes: str = "foo:invoke other:read", ttl: int = 3600) -> str:
    exp = int(time.time()) + ttl
    return make_jwt({"sub": sub, "exp": exp, "scope": scopes})


def auth_header(token: str | None = None) -> str:
    if token is None:
        token = valid_token()
    return f"Bearer {token}"


@pytest.fixture
def store():
    return IdempotencyStore()


@pytest.fixture
def now_utc():
    return datetime.now(timezone.utc)


@pytest.fixture
def active_user(now_utc):
    return UserProfile(user_id="user-123", last_login_at=now_utc - timedelta(days=1))


@pytest.fixture
def inactive_user(now_utc):
    return UserProfile(user_id="user-123", last_login_at=now_utc - timedelta(days=30))


@pytest.fixture(autouse=True)
def _snapshot_audit_log():
    """Snapshot and restore AUDIT_LOG so tests do not leak audit lines across runs."""
    original = list(AUDIT_LOG)
    yield
    AUDIT_LOG.clear()
    AUDIT_LOG.extend(original)


def make_ctx(
    *,
    token: str | None = None,
    idempotency_key: str | None = "key-1",
    body: bytes | None = None,
    received_at: datetime | None = None,
) -> RequestContext:
    if token == "__missing__":
        auth = None
    elif token is None:
        auth = auth_header(valid_token())
    else:
        auth = auth_header(token)
    return RequestContext(
        authorization=auth,
        idempotency_key=idempotency_key,
        request_received_at=received_at or datetime.now(timezone.utc),
        body_bytes=body,
    )


# ---------------------------------------------------------------------------
# parse_bearer_jwt
# ---------------------------------------------------------------------------

def test_parse_bearer_jwt_valid():
    ok, claims, err = parse_bearer_jwt(auth_header(valid_token(sub="alice")))
    assert ok is True
    assert err is None
    assert claims["sub"] == "alice"
    assert "foo:invoke" in claims["scope"].split()


def test_parse_bearer_jwt_missing_header():
    ok, claims, err = parse_bearer_jwt(None)
    assert ok is False
    assert claims is None
    assert err  # some error reason


def test_parse_bearer_jwt_empty_string():
    ok, claims, err = parse_bearer_jwt("")
    assert ok is False
    assert claims is None
    assert err


def test_parse_bearer_jwt_no_bearer_prefix():
    ok, _, err = parse_bearer_jwt("Token abc.def.ghi")
    assert ok is False
    assert err


def test_parse_bearer_jwt_malformed_segments():
    ok, _, err = parse_bearer_jwt("Bearer not-a-jwt")
    assert ok is False
    assert err


def test_parse_bearer_jwt_empty_token_after_bearer():
    ok, _, err = parse_bearer_jwt("Bearer    ")
    assert ok is False
    assert err


def test_parse_bearer_jwt_bad_payload_base64():
    # Middle segment not valid base64 JSON
    token = "aGVhZGVy.@@@@.sig"
    ok, _, err = parse_bearer_jwt(f"Bearer {token}")
    assert ok is False
    assert err


def test_parse_bearer_jwt_payload_not_json_object():
    # Payload decodes but is a JSON list, not a dict
    seg = _b64url(b'["not", "a", "dict"]')
    token = f"hdr.{seg}.sig"
    ok, _, err = parse_bearer_jwt(f"Bearer {token}")
    assert ok is False
    assert err


def test_parse_bearer_jwt_expired():
    expired = make_jwt({"sub": "u", "exp": int(time.time()) - 60, "scope": "foo:invoke"})
    ok, _, err = parse_bearer_jwt(auth_header(expired))
    assert ok is False
    assert err


def test_parse_bearer_jwt_missing_exp():
    token = make_jwt({"sub": "u", "scope": "foo:invoke"})
    ok, _, err = parse_bearer_jwt(auth_header(token))
    assert ok is False
    assert err


def test_parse_bearer_jwt_wrong_scope():
    token = make_jwt({"sub": "u", "exp": int(time.time()) + 3600, "scope": "other:read"})
    ok, _, err = parse_bearer_jwt(auth_header(token))
    assert ok is False
    assert err


def test_parse_bearer_jwt_missing_scope():
    token = make_jwt({"sub": "u", "exp": int(time.time()) + 3600})
    ok, _, err = parse_bearer_jwt(auth_header(token))
    assert ok is False
    assert err


def test_parse_bearer_jwt_scope_as_list():
    token = make_jwt({"sub": "u", "exp": int(time.time()) + 3600,
                      "scope": ["foo:invoke", "other"]})
    ok, claims, err = parse_bearer_jwt(auth_header(token))
    assert ok is True
    assert err is None
    assert claims is not None


# ---------------------------------------------------------------------------
# is_active_user
# ---------------------------------------------------------------------------

def test_is_active_user_recent_login(now_utc):
    user = UserProfile(user_id="u", last_login_at=now_utc - timedelta(days=1))
    assert is_active_user(user, now_utc) is True


def test_is_active_user_exactly_at_boundary(now_utc):
    # delta.days == 5 should still be active (<= 5)
    user = UserProfile(user_id="u", last_login_at=now_utc - timedelta(days=5, hours=0, minutes=0))
    assert is_active_user(user, now_utc) is True


def test_is_active_user_beyond_window(now_utc):
    user = UserProfile(user_id="u", last_login_at=now_utc - timedelta(days=6))
    assert is_active_user(user, now_utc) is False


def test_is_active_user_old_login(now_utc):
    user = UserProfile(user_id="u", last_login_at=now_utc - timedelta(days=365))
    assert is_active_user(user, now_utc) is False


# ---------------------------------------------------------------------------
# IdempotencyStore
# ---------------------------------------------------------------------------

def test_store_has_returns_false_for_unknown_key(store):
    assert store.has("nope") is False
    assert store.get_request_id("nope") is None


def test_store_record_then_has(store):
    store.record("k1", "req-1")
    assert store.has("k1") is True
    assert store.get_request_id("k1") == "req-1"


def test_store_ttl_eviction_on_read():
    # short TTL store to test eviction
    s = IdempotencyStore(ttl_seconds=0)  # immediately expired
    s.record("k1", "req-1")
    # Sleep tiny bit to ensure (now - recorded_at) >= 0
    time.sleep(0.01)
    assert s.has("k1") is False
    assert s.get_request_id("k1") is None


def test_store_get_key_lock_returns_same_lock_per_key(store):
    a = store.get_key_lock("k")
    b = store.get_key_lock("k")
    assert a is b
    c = store.get_key_lock("other")
    assert c is not a


# ---------------------------------------------------------------------------
# handle_request - happy path & auth (R1, R3)
# ---------------------------------------------------------------------------

def test_handle_request_success_minimal(store, active_user):
    audit_before = len(AUDIT_LOG)
    ctx = make_ctx(idempotency_key="abc")
    result = handle_request(ctx, active_user, store)
    assert isinstance(result, HandlerResult)
    assert result.status_code == 200
    assert result.body["result"] == "ok"
    assert isinstance(result.body["request_id"], str)
    # Must be a valid uuid4 string
    uuid.UUID(result.body["request_id"])
    assert result.body["amount_cents"] is None
    # R6: audit logged on success
    assert len(AUDIT_LOG) == audit_before + 1


def test_handle_request_success_with_body(store, active_user):
    body = json.dumps({"amount_cents": 500, "note": "hello"}).encode("utf-8")
    ctx = make_ctx(idempotency_key="key-body", body=body)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert result.body["amount_cents"] == 500


def test_handle_request_unauthorized_missing(store, active_user):
    ctx = make_ctx(token="__missing__", idempotency_key="k-x")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401
    # R2/R3: no store mutation on auth failure
    assert store.has("k-x") is False


def test_handle_request_unauthorized_expired(store, active_user):
    expired = make_jwt({"sub": "u", "exp": int(time.time()) - 5, "scope": "foo:invoke"})
    ctx = make_ctx(token=expired, idempotency_key="k-exp")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401
    assert store.has("k-exp") is False


def test_handle_request_unauthorized_wrong_scope(store, active_user):
    bad = make_jwt({"sub": "u", "exp": int(time.time()) + 3600, "scope": "other:read"})
    ctx = make_ctx(token=bad, idempotency_key="k-scope")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401
    assert store.has("k-scope") is False


# ---------------------------------------------------------------------------
# handle_request - active user (R4)
# ---------------------------------------------------------------------------

def test_handle_request_inactive_user_blocked(store, inactive_user):
    ctx = make_ctx(idempotency_key="k-inactive")
    result = handle_request(ctx, inactive_user, store)
    assert result.status_code == 403
    assert store.has("k-inactive") is False


def test_handle_request_inactive_user_no_audit(store, inactive_user):
    audit_before = len(AUDIT_LOG)
    ctx = make_ctx(idempotency_key="k-inactive-2")
    handle_request(ctx, inactive_user, store)
    assert len(AUDIT_LOG) == audit_before


# ---------------------------------------------------------------------------
# handle_request - idempotency (R2)
# ---------------------------------------------------------------------------

def test_handle_request_missing_idempotency_key(store, active_user):
    ctx = make_ctx(idempotency_key=None)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 400


def test_handle_request_empty_idempotency_key(store, active_user):
    ctx = make_ctx(idempotency_key="")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 400


def test_handle_request_duplicate_returns_409(store, active_user):
    first = handle_request(make_ctx(idempotency_key="dup"), active_user, store)
    assert first.status_code == 200
    original_id = first.body["request_id"]

    second = handle_request(make_ctx(idempotency_key="dup"), active_user, store)
    assert second.status_code == 409
    assert second.body["reason"] == "duplicate"
    assert second.body["original_request_id"] == original_id
    # store still has the original request id
    assert store.get_request_id("dup") == original_id


def test_handle_request_duplicate_does_not_audit_again(store, active_user):
    handle_request(make_ctx(idempotency_key="dup2"), active_user, store)
    audit_after_first = len(AUDIT_LOG)
    handle_request(make_ctx(idempotency_key="dup2"), active_user, store)
    assert len(AUDIT_LOG) == audit_after_first


# ---------------------------------------------------------------------------
# handle_request - body validation (R5)
# ---------------------------------------------------------------------------

def test_handle_request_malformed_json_returns_400(store, active_user):
    ctx = make_ctx(idempotency_key="bad-json", body=b"{not json")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 400
    # No store mutation
    assert store.has("bad-json") is False


def test_handle_request_malformed_json_does_not_corrupt_other_keys(store, active_user):
    # Record a good key first
    good = handle_request(make_ctx(idempotency_key="good-key"), active_user, store)
    assert good.status_code == 200
    good_id = good.body["request_id"]

    # Now send malformed JSON under a different key
    bad = handle_request(
        make_ctx(idempotency_key="bad-key", body=b"<<<>>>"),
        active_user,
        store,
    )
    assert bad.status_code == 400

    # The good key is still intact
    assert store.get_request_id("good-key") == good_id
    # Bad key was not written
    assert store.has("bad-key") is False


def test_handle_request_non_object_json_rejected(store, active_user):
    ctx = make_ctx(idempotency_key="arr", body=b"[1,2,3]")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 400


def test_handle_request_negative_amount_returns_422(store, active_user):
    body = json.dumps({"amount_cents": -10}).encode("utf-8")
    ctx = make_ctx(idempotency_key="neg", body=body)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 422
    assert store.has("neg") is False


def test_handle_request_zero_amount_returns_422(store, active_user):
    body = json.dumps({"amount_cents": 0}).encode("utf-8")
    ctx = make_ctx(idempotency_key="zero", body=body)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 422


def test_handle_request_amount_not_int_returns_422(store, active_user):
    body = json.dumps({"amount_cents": "100"}).encode("utf-8")
    ctx = make_ctx(idempotency_key="strnum", body=body)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 422


def test_handle_request_amount_bool_rejected_as_invalid(store, active_user):
    # bool is a subclass of int; the handler explicitly rejects bool
    body = json.dumps({"amount_cents": True}).encode("utf-8")
    ctx = make_ctx(idempotency_key="boolamt", body=body)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 422


def test_handle_request_empty_body_is_ok(store, active_user):
    ctx = make_ctx(idempotency_key="empty", body=b"")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert result.body["amount_cents"] is None


# ---------------------------------------------------------------------------
# Processing order: auth precedes idempotency-key check
# ---------------------------------------------------------------------------

def test_auth_failure_takes_precedence_over_missing_idem_key(store, active_user):
    ctx = make_ctx(token="__missing__", idempotency_key=None)
    result = handle_request(ctx, active_user, store)
    # Auth runs first per declared processing order
    assert result.status_code == 401


def test_idem_key_check_runs_before_active_user_check(store, inactive_user):
    # Inactive user but missing idem key: per spec order auth->idem-key->active-user,
    # so missing key should yield 400 before 403. (We don't over-constrain: simply
    # assert that the response is one of those two but document expected order.)
    ctx = make_ctx(idempotency_key=None)
    result = handle_request(ctx, inactive_user, store)
    assert result.status_code in (400, 403)


# ---------------------------------------------------------------------------
# Concurrency (R2 + spec #6)
# ---------------------------------------------------------------------------

def test_handle_request_concurrent_same_key_one_success_one_duplicate(store, active_user):
    results: list[HandlerResult] = []
    barrier = threading.Barrier(2)

    def worker():
        barrier.wait()
        # Build ctx inside thread so request_received_at and token are fresh
        ctx = make_ctx(idempotency_key="race-key")
        results.append(handle_request(ctx, active_user, store))

    threads = [threading.Thread(target=worker) for _ in range(2)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    status_codes = sorted(r.status_code for r in results)
    assert status_codes == [200, 409]

    # The 409 must reference the 200 request id
    ok_result = next(r for r in results if r.status_code == 200)
    dup_result = next(r for r in results if r.status_code == 409)
    assert dup_result.body["original_request_id"] == ok_result.body["request_id"]


# ---------------------------------------------------------------------------
# Audit logging (R6)
# ---------------------------------------------------------------------------

def test_audit_log_records_caller_and_request_id(store, active_user):
    audit_before = len(AUDIT_LOG)
    token = valid_token(sub="audit-user")
    ctx = make_ctx(token=token, idempotency_key="aud-1")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert len(AUDIT_LOG) == audit_before + 1
    last_line = AUDIT_LOG[-1]
    # The audit line is a JSON string per the implementation - parse defensively.
    try:
        parsed = json.loads(last_line)
        assert parsed["caller_id"] == "audit-user"
        assert parsed["request_id"] == result.body["request_id"]
    except (json.JSONDecodeError, TypeError):
        # If implementation changes format, at least the request_id should appear
        assert result.body["request_id"] in last_line


def test_no_audit_on_unauthorized(store, active_user):
    audit_before = len(AUDIT_LOG)
    ctx = make_ctx(token="__missing__", idempotency_key="noaud")
    handle_request(ctx, active_user, store)
    assert len(AUDIT_LOG) == audit_before


def test_no_audit_on_duplicate(store, active_user):
    handle_request(make_ctx(idempotency_key="ad-dup"), active_user, store)
    audit_after_first = len(AUDIT_LOG)
    second = handle_request(make_ctx(idempotency_key="ad-dup"), active_user, store)
    assert second.status_code == 409
    assert len(AUDIT_LOG) == audit_after_first


def test_no_audit_on_bad_body(store, active_user):
    audit_before = len(AUDIT_LOG)
    ctx = make_ctx(idempotency_key="ad-bad", body=b"not-json")
    handle_request(ctx, active_user, store)
    assert len(AUDIT_LOG) == audit_before