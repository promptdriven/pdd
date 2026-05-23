
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""Tests for src/foo_work_after.py (idempotent request handler)."""

import base64
import json
import os
import sys
import threading
import time
import uuid
from datetime import datetime, timedelta, timezone
from unittest.mock import patch

import pytest

# Make `src/` importable so we can import the module under test.
_HERE = os.path.dirname(os.path.abspath(__file__))
_SRC = os.path.join(_HERE, "src")
if _SRC not in sys.path:

import foo_work_after as fw  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers / fixtures
# ---------------------------------------------------------------------------

def _b64url(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def make_jwt(
    sub: str = "user-123",
    scope="foo:invoke",
    exp_offset: int = 3600,
    extra_claims: dict | None = None,
    header: dict | None = None,
    bad_payload: bool = False,
) -> str:
    """Build a JWT-like string. Signature segment is dummy (not verified)."""
    hdr = header if header is not None else {"alg": "none", "typ": "JWT"}
    claims = {"sub": sub, "exp": int(time.time()) + exp_offset, "scope": scope}
    if extra_claims:
        claims.update(extra_claims)
    h = _b64url(json.dumps(hdr).encode("utf-8"))
    if bad_payload:
        p = "!!!not-base64!!!"
    else:
        p = _b64url(json.dumps(claims).encode("utf-8"))
    s = _b64url(b"signature")
    return f"{h}.{p}.{s}"


@pytest.fixture(autouse=True)
def _clear_audit_log():
    """Ensure each test starts with an empty AUDIT_LOG."""
    fw.AUDIT_LOG.clear()
    yield
    fw.AUDIT_LOG.clear()


@pytest.fixture
def store():
    return fw.IdempotencyStore()


@pytest.fixture
def now_utc():
    return datetime.now(timezone.utc)


@pytest.fixture
def active_user(now_utc):
    return fw.UserProfile(user_id="user-123", last_login_at=now_utc - timedelta(days=1))


@pytest.fixture
def inactive_user(now_utc):
    return fw.UserProfile(user_id="user-123", last_login_at=now_utc - timedelta(days=10))


def make_ctx(
    *,
    authorization=None,
    idempotency_key="key-1",
    received_at=None,
    body_bytes=None,
    jwt_kwargs=None,
):
    if authorization is None:
        authorization = "Bearer " + make_jwt(**(jwt_kwargs or {}))
    if received_at is None:
        received_at = datetime.now(timezone.utc)
    return fw.RequestContext(
        authorization=authorization,
        idempotency_key=idempotency_key,
        request_received_at=received_at,
        body_bytes=body_bytes,
    )


# ---------------------------------------------------------------------------
# parse_bearer_jwt
# ---------------------------------------------------------------------------

def test_parse_bearer_jwt_success():
    token = "Bearer " + make_jwt(sub="alice")
    ok, claims, err = fw.parse_bearer_jwt(token)
    assert ok is True
    assert err is None
    assert claims["sub"] == "alice"
    assert "foo:invoke" in (
        claims["scope"] if isinstance(claims["scope"], list) else claims["scope"].split()
    )


def test_parse_bearer_jwt_missing():
    ok, claims, err = fw.parse_bearer_jwt(None)
    assert ok is False
    assert claims is None
    assert err  # some error string


def test_parse_bearer_jwt_empty_string():
    ok, claims, err = fw.parse_bearer_jwt("")
    assert ok is False and claims is None and err


def test_parse_bearer_jwt_missing_bearer_prefix():
    token = make_jwt()
    ok, claims, err = fw.parse_bearer_jwt(token)  # no "Bearer "
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_wrong_scheme():
    ok, claims, err = fw.parse_bearer_jwt("Basic abc.def.ghi")
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_malformed_token_segments():
    ok, claims, err = fw.parse_bearer_jwt("Bearer notajwt")
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_bad_base64_payload():
    ok, claims, err = fw.parse_bearer_jwt("Bearer " + make_jwt(bad_payload=True))
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_expired():
    ok, claims, err = fw.parse_bearer_jwt("Bearer " + make_jwt(exp_offset=-10))
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_missing_exp():
    # Build a JWT without exp
    hdr = _b64url(json.dumps({"alg": "none"}).encode())
    payload = _b64url(json.dumps({"sub": "u", "scope": "foo:invoke"}).encode())
    sig = _b64url(b"x")
    ok, claims, err = fw.parse_bearer_jwt(f"Bearer {hdr}.{payload}.{sig}")
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_insufficient_scope():
    ok, claims, err = fw.parse_bearer_jwt(
        "Bearer " + make_jwt(scope="other:scope")
    )
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_scope_as_list():
    ok, claims, err = fw.parse_bearer_jwt(
        "Bearer " + make_jwt(scope=["read", "foo:invoke"])
    )
    assert ok is True
    assert err is None
    assert claims is not None


# ---------------------------------------------------------------------------
# is_active_user
# ---------------------------------------------------------------------------

def test_is_active_user_recent(now_utc):
    u = fw.UserProfile("u", now_utc - timedelta(days=1))
    assert fw.is_active_user(u, now_utc) is True


def test_is_active_user_boundary_5_days(now_utc):
    u = fw.UserProfile("u", now_utc - timedelta(days=5))
    assert fw.is_active_user(u, now_utc) is True


def test_is_active_user_inactive(now_utc):
    u = fw.UserProfile("u", now_utc - timedelta(days=6))
    assert fw.is_active_user(u, now_utc) is False


def test_is_active_user_far_past(now_utc):
    u = fw.UserProfile("u", now_utc - timedelta(days=365))
    assert fw.is_active_user(u, now_utc) is False


# ---------------------------------------------------------------------------
# IdempotencyStore (public API)
# ---------------------------------------------------------------------------

def test_store_has_false_for_unknown_key(store):
    assert store.has("nope") is False
    assert store.get_request_id("nope") is None


def test_store_record_and_retrieve(store):
    store.record("k1", "rid-1")
    assert store.has("k1") is True
    assert store.get_request_id("k1") == "rid-1"


def test_store_record_does_not_overwrite(store):
    store.record("k1", "rid-1")
    store.record("k1", "rid-2")
    assert store.get_request_id("k1") == "rid-1"


def test_store_ttl_eviction():
    # Use a tiny TTL to exercise eviction without sleeping for hours.
    s = fw.IdempotencyStore(ttl_seconds=0)
    s.record("k1", "rid-1")
    # With ttl=0, even a tiny wait should evict.
    time.sleep(0.01)
    assert s.has("k1") is False
    assert s.get_request_id("k1") is None


def test_store_independent_keys(store):
    store.record("a", "rid-a")
    store.record("b", "rid-b")
    assert store.get_request_id("a") == "rid-a"
    assert store.get_request_id("b") == "rid-b"


# ---------------------------------------------------------------------------
# handle_request - happy path
# ---------------------------------------------------------------------------

def test_handle_request_success_no_body(store, active_user):
    ctx = make_ctx()
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 200
    assert res.body["result"] == "ok"
    # request_id must be a valid uuid4 string
    parsed_uuid = uuid.UUID(res.body["request_id"])
    assert parsed_uuid.version == 4
    assert res.body["amount_cents"] is None
    assert "audit_failed" not in res.body


def test_handle_request_success_with_amount(store, active_user):
    ctx = make_ctx(body_bytes=json.dumps({"amount_cents": 4200, "note": "ok"}).encode())
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 200
    assert res.body["amount_cents"] == 4200
    assert res.body["result"] == "ok"


def test_handle_request_audit_log_on_success(store, active_user):
    ctx = make_ctx(
        jwt_kwargs={"sub": "alice"},
        body_bytes=json.dumps({"amount_cents": 100}).encode(),
    )
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 200
    assert len(fw.AUDIT_LOG) == 1
    line = fw.AUDIT_LOG[0]
    assert "alice" in line
    assert res.body["request_id"] in line
    assert "100" in line


def test_handle_request_audit_failure_still_200(store, active_user):
    ctx = make_ctx()
    # AUDIT_LOG.append is called from inside the module; raise from it.
    with patch.object(fw.AUDIT_LOG, "append", side_effect=RuntimeError("boom")):
        res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 200
    assert res.body.get("audit_failed") is True
    assert res.body["result"] == "ok"


# ---------------------------------------------------------------------------
# handle_request - auth errors
# ---------------------------------------------------------------------------

def test_handle_request_missing_authorization(store, active_user):
    ctx = make_ctx(authorization=None)
    # set explicitly because make_ctx defaults to a valid bearer
    ctx.authorization = None
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 401
    # No store mutation, no audit
    assert store.has("key-1") is False
    assert fw.AUDIT_LOG == []


def test_handle_request_expired_jwt(store, active_user):
    ctx = make_ctx(authorization="Bearer " + make_jwt(exp_offset=-10))
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 401
    assert store.has("key-1") is False
    assert fw.AUDIT_LOG == []


def test_handle_request_wrong_scope(store, active_user):
    ctx = make_ctx(authorization="Bearer " + make_jwt(scope="other:scope"))
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 401
    assert store.has("key-1") is False


def test_handle_request_auth_before_idempotency(store, active_user):
    # Even with a missing idempotency key, auth failure wins first.
    ctx = fw.RequestContext(
        authorization=None,
        idempotency_key=None,
        request_received_at=datetime.now(timezone.utc),
        body_bytes=None,
    )
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 401


# ---------------------------------------------------------------------------
# handle_request - idempotency key / active user
# ---------------------------------------------------------------------------

def test_handle_request_missing_idempotency_key(store, active_user):
    ctx = make_ctx(idempotency_key=None)
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 400
    assert fw.AUDIT_LOG == []


def test_handle_request_empty_idempotency_key(store, active_user):
    ctx = make_ctx(idempotency_key="")
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 400


def test_handle_request_inactive_user(store, inactive_user):
    ctx = make_ctx()
    res = fw.handle_request(ctx, inactive_user, store)
    assert res.status_code == 403
    # Inactive user should not have a record written for this key
    assert store.has("key-1") is False
    assert fw.AUDIT_LOG == []


# ---------------------------------------------------------------------------
# handle_request - duplicate (idempotency) behavior
# ---------------------------------------------------------------------------

def test_handle_request_duplicate_returns_409(store, active_user):
    ctx1 = make_ctx(idempotency_key="dup")
    res1 = fw.handle_request(ctx1, active_user, store)
    assert res1.status_code == 200
    original_rid = res1.body["request_id"]

    ctx2 = make_ctx(idempotency_key="dup")
    res2 = fw.handle_request(ctx2, active_user, store)
    assert res2.status_code == 409
    assert res2.body["reason"] == "duplicate"
    assert res2.body["original_request_id"] == original_rid
    # Only one audit line for the first request
    assert len(fw.AUDIT_LOG) == 1
    # Stored request_id unchanged
    assert store.get_request_id("dup") == original_rid


def test_handle_request_different_keys_both_succeed(store, active_user):
    ctx1 = make_ctx(idempotency_key="k-a")
    ctx2 = make_ctx(idempotency_key="k-b")
    r1 = fw.handle_request(ctx1, active_user, store)
    r2 = fw.handle_request(ctx2, active_user, store)
    assert r1.status_code == 200
    assert r2.status_code == 200
    assert r1.body["request_id"] != r2.body["request_id"]
    assert len(fw.AUDIT_LOG) == 2


# ---------------------------------------------------------------------------
# handle_request - body validation
# ---------------------------------------------------------------------------

def test_handle_request_malformed_json(store, active_user):
    ctx = make_ctx(body_bytes=b"{not json")
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 400
    # No store mutation on malformed JSON
    assert store.has("key-1") is False
    assert fw.AUDIT_LOG == []


def test_handle_request_malformed_json_does_not_corrupt_other_keys(store, active_user):
    # First, record a real successful key
    good = make_ctx(idempotency_key="good-key",
                    body_bytes=json.dumps({"amount_cents": 50}).encode())
    r_good = fw.handle_request(good, active_user, store)
    assert r_good.status_code == 200
    good_rid = r_good.body["request_id"]

    # Then, send a malformed JSON request with a *different* idempotency key
    bad = make_ctx(idempotency_key="bad-key", body_bytes=b"{bro")
    r_bad = fw.handle_request(bad, active_user, store)
    assert r_bad.status_code == 400

    # Original key is intact, bad key not stored
    assert store.get_request_id("good-key") == good_rid
    assert store.has("bad-key") is False


def test_handle_request_amount_zero_returns_422(store, active_user):
    ctx = make_ctx(body_bytes=json.dumps({"amount_cents": 0}).encode())
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 422
    assert store.has("key-1") is False
    assert fw.AUDIT_LOG == []


def test_handle_request_amount_negative_returns_422(store, active_user):
    ctx = make_ctx(body_bytes=json.dumps({"amount_cents": -1}).encode())
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 422


def test_handle_request_json_not_an_object(store, active_user):
    ctx = make_ctx(body_bytes=json.dumps([1, 2, 3]).encode())
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 400


def test_handle_request_empty_body_bytes_ok(store, active_user):
    ctx = make_ctx(body_bytes=b"")
    res = fw.handle_request(ctx, active_user, store)
    assert res.status_code == 200
    assert res.body["amount_cents"] is None


# ---------------------------------------------------------------------------
# Concurrency: parallel same-key requests
# ---------------------------------------------------------------------------

def test_handle_request_concurrent_duplicate_race(active_user):
    store = fw.IdempotencyStore()
    results = []
    barrier = threading.Barrier(8)

    def worker():
        ctx = make_ctx(idempotency_key="race-key")
        barrier.wait()
        results.append(fw.handle_request(ctx, active_user, store))

    threads = [threading.Thread(target=worker) for _ in range(8)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    statuses = sorted(r.status_code for r in results)
    assert statuses.count(200) == 1
    assert statuses.count(409) == 7
    # Stored request_id equals the one returned by the 200 response
    ok_result = next(r for r in results if r.status_code == 200)
    assert store.get_request_id("race-key") == ok_result.body["request_id"]
    # All 409s reference the same original_request_id
    for r in results:
        if r.status_code == 409:
            assert r.body["reason"] == "duplicate"
            assert r.body["original_request_id"] == ok_result.body["request_id"]
    # Exactly one audit entry
    assert len(fw.AUDIT_LOG) == 1


# ---------------------------------------------------------------------------
# Processing order spot-checks
# ---------------------------------------------------------------------------

def test_processing_order_auth_before_active_user(store, inactive_user):
    # Inactive user but bad auth -> 401 (not 403)
    ctx = make_ctx(authorization="Bearer not.a.jwt")
    res = fw.handle_request(ctx, inactive_user, store)
    assert res.status_code == 401


def test_processing_order_active_user_before_duplicate(store, active_user, inactive_user):
    # First call with active user records the key
    ctx_first = make_ctx(idempotency_key="shared")
    r1 = fw.handle_request(ctx_first, active_user, store)
    assert r1.status_code == 200

    # Same key but the new caller is inactive -> 403 wins over 409 per
    # documented order (active user check happens before duplicate check).
    ctx_second = make_ctx(idempotency_key="shared")
    r2 = fw.handle_request(ctx_second, inactive_user, store)
    assert r2.status_code == 403