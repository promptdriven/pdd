
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""Tests for foo_work_after module."""

from __future__ import annotations

import base64
import json
import sys
import threading
import uuid
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

# Make src/ importable regardless of pytest invocation directory.
_SRC_DIR = Path(__file__).parent / "src"
if str(_SRC_DIR) not in sys.path:

import foo_work_after as fw  # noqa: E402
from foo_work_after import (  # noqa: E402
    AUDIT_LOG,
    HandlerResult,
    IdempotencyStore,
    RequestContext,
    UserProfile,
    handle_request,
    is_active_user,
    parse_bearer_jwt,
)


# --------------------------------------------------------------------------- #
# Helpers / Fixtures
# --------------------------------------------------------------------------- #

def _b64url(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def make_jwt(payload: dict, *, header: dict | None = None, sig: str = "sig") -> str:
    header = header or {"alg": "none", "typ": "JWT"}
    h = _b64url(json.dumps(header).encode("utf-8"))
    p = _b64url(json.dumps(payload).encode("utf-8"))
    return f"{h}.{p}.{sig}"


def valid_token(sub: str = "u1", scope: str = "foo:invoke", ttl_seconds: int = 3600) -> str:
    exp = int(datetime.now(timezone.utc).timestamp()) + ttl_seconds
    return make_jwt({"sub": sub, "scope": scope, "exp": exp})


def bearer(token: str) -> str:
    return f"Bearer {token}"


@pytest.fixture(autouse=True)
def _clear_audit_log():
    # Always restore to a clean module-level list with the same identity policy:
    # we replace the module attribute, then restore the original at the end.
    original = fw.AUDIT_LOG
    fw.AUDIT_LOG = []
    try:
        yield
    finally:
        fw.AUDIT_LOG = original
        # Also ensure no stale entries leak when tests use the original list
        del original[:]


@pytest.fixture
def store():
    return IdempotencyStore()


@pytest.fixture
def now_utc():
    return datetime.now(timezone.utc)


@pytest.fixture
def active_user(now_utc):
    return UserProfile(user_id="u1", last_login_at=now_utc - timedelta(hours=1))


@pytest.fixture
def ctx_factory(now_utc):
    def _make(
        *,
        authorization: str | None = None,
        idempotency_key: str | None = "key-1",
        body: bytes | None = None,
        received_at: datetime | None = None,
    ) -> RequestContext:
        if authorization is None:
            authorization = bearer(valid_token())
        return RequestContext(
            authorization=authorization,
            idempotency_key=idempotency_key,
            request_received_at=received_at or now_utc,
            body_bytes=body,
        )

    return _make


# --------------------------------------------------------------------------- #
# parse_bearer_jwt
# --------------------------------------------------------------------------- #

def test_parse_bearer_jwt_valid():
    ok, claims, err = parse_bearer_jwt(bearer(valid_token(sub="alice")))
    assert ok is True
    assert err is None
    assert claims is not None
    assert claims["sub"] == "alice"
    assert "foo:invoke" in (claims["scope"].split() if isinstance(claims["scope"], str) else claims["scope"])


def test_parse_bearer_jwt_none():
    ok, claims, err = parse_bearer_jwt(None)
    assert ok is False
    assert claims is None
    assert err  # some error message


def test_parse_bearer_jwt_empty_string():
    ok, claims, _ = parse_bearer_jwt("")
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_not_bearer_scheme():
    ok, claims, _ = parse_bearer_jwt("Basic xyz")
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_missing_token_part():
    ok, claims, _ = parse_bearer_jwt("Bearer ")
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_malformed_jwt_not_enough_segments():
    ok, claims, _ = parse_bearer_jwt("Bearer onlyonesegment")
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_undecodable_payload():
    # A payload that is not valid base64url / not valid JSON
    token = "header.@@@notbase64@@@.sig"
    ok, claims, _ = parse_bearer_jwt(f"Bearer {token}")
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_expired():
    exp = int(datetime.now(timezone.utc).timestamp()) - 60
    token = make_jwt({"sub": "u", "scope": "foo:invoke", "exp": exp})
    ok, claims, _ = parse_bearer_jwt(bearer(token))
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_missing_exp():
    token = make_jwt({"sub": "u", "scope": "foo:invoke"})
    ok, claims, _ = parse_bearer_jwt(bearer(token))
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_wrong_scope():
    token = valid_token(scope="other:scope")
    ok, claims, _ = parse_bearer_jwt(bearer(token))
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_scope_as_list():
    exp = int(datetime.now(timezone.utc).timestamp()) + 3600
    token = make_jwt({"sub": "u", "scope": ["other", "foo:invoke"], "exp": exp})
    ok, claims, err = parse_bearer_jwt(bearer(token))
    assert ok is True
    assert err is None


def test_parse_bearer_jwt_missing_scope_field():
    exp = int(datetime.now(timezone.utc).timestamp()) + 3600
    token = make_jwt({"sub": "u", "exp": exp})
    ok, claims, _ = parse_bearer_jwt(bearer(token))
    assert ok is False
    assert claims is None


# --------------------------------------------------------------------------- #
# is_active_user
# --------------------------------------------------------------------------- #

def test_is_active_user_recent_login(now_utc):
    user = UserProfile(user_id="u", last_login_at=now_utc - timedelta(days=1))
    assert is_active_user(user, now_utc) is True


def test_is_active_user_exactly_5_days(now_utc):
    user = UserProfile(user_id="u", last_login_at=now_utc - timedelta(days=5))
    assert is_active_user(user, now_utc) is True


def test_is_active_user_6_days_inactive(now_utc):
    user = UserProfile(user_id="u", last_login_at=now_utc - timedelta(days=6))
    assert is_active_user(user, now_utc) is False


# --------------------------------------------------------------------------- #
# IdempotencyStore
# --------------------------------------------------------------------------- #

def test_store_has_returns_false_for_unknown(store):
    assert store.has("nope") is False
    assert store.get_request_id("nope") is None


def test_store_record_and_get(store):
    store.record("k1", "rid-1")
    assert store.has("k1") is True
    assert store.get_request_id("k1") == "rid-1"


def test_store_overwrite_via_record(store):
    # The contract doesn't forbid record being called directly, but `has`/`get`
    # must reflect the latest record after a write.
    store.record("k1", "rid-1")
    store.record("k1", "rid-2")
    assert store.get_request_id("k1") == "rid-2"


# --------------------------------------------------------------------------- #
# R1: Successful first request
# --------------------------------------------------------------------------- #

def test_R1_first_request_returns_200_and_records_key(store, active_user, ctx_factory):
    ctx = ctx_factory(body=json.dumps({"amount_cents": 100}).encode("utf-8"))
    result = handle_request(ctx, active_user, store)

    assert isinstance(result, HandlerResult)
    assert result.status_code == 200
    assert result.body["result"] == "ok"
    rid = result.body["request_id"]
    # Must be a valid uuid4 string
    parsed = uuid.UUID(rid)
    assert parsed.version == 4
    assert result.body["amount_cents"] == 100
    assert store.get_request_id(ctx.idempotency_key) == rid


def test_R1_first_request_with_no_body(store, active_user, ctx_factory):
    ctx = ctx_factory(body=None)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert result.body["result"] == "ok"
    assert result.body["amount_cents"] is None
    uuid.UUID(result.body["request_id"])  # validates uuid


def test_R1_first_request_with_empty_body(store, active_user, ctx_factory):
    ctx = ctx_factory(body=b"")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert result.body["amount_cents"] is None


# --------------------------------------------------------------------------- #
# R2: Duplicate idempotency key
# --------------------------------------------------------------------------- #

def test_R2_duplicate_returns_409_and_does_not_mutate(store, active_user, ctx_factory):
    ctx1 = ctx_factory(body=json.dumps({"amount_cents": 50}).encode("utf-8"))
    first = handle_request(ctx1, active_user, store)
    assert first.status_code == 200
    stored_rid = store.get_request_id(ctx1.idempotency_key)
    assert stored_rid == first.body["request_id"]

    # Second request with the same key
    ctx2 = ctx_factory(body=json.dumps({"amount_cents": 999}).encode("utf-8"))
    second = handle_request(ctx2, active_user, store)
    assert second.status_code == 409
    assert second.body == {"reason": "duplicate", "original_request_id": stored_rid}
    # Store unchanged
    assert store.get_request_id(ctx2.idempotency_key) == stored_rid


# --------------------------------------------------------------------------- #
# R3: Authorization gate
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize(
    "auth_header",
    [
        None,
        "",
        "Basic abc",
        "Bearer ",
        "Bearer onlyone",
        "Bearer header.@@@notb64@@@.sig",
    ],
)
def test_R3_unauthorized_returns_401_no_side_effects(
    store, active_user, ctx_factory, auth_header
):
    pre_audit = list(fw.AUDIT_LOG)
    ctx = ctx_factory(authorization=auth_header)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401
    assert store.has(ctx.idempotency_key) is False
    assert fw.AUDIT_LOG == pre_audit


def test_R3_expired_token_returns_401(store, active_user, ctx_factory):
    pre_audit = list(fw.AUDIT_LOG)
    exp = int(datetime.now(timezone.utc).timestamp()) - 1
    token = make_jwt({"sub": "u1", "scope": "foo:invoke", "exp": exp})
    ctx = ctx_factory(authorization=bearer(token))
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401
    assert store.has(ctx.idempotency_key) is False
    assert fw.AUDIT_LOG == pre_audit


def test_R3_wrong_scope_returns_401(store, active_user, ctx_factory):
    pre_audit = list(fw.AUDIT_LOG)
    ctx = ctx_factory(authorization=bearer(valid_token(scope="other:scope")))
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401
    assert store.has(ctx.idempotency_key) is False
    assert fw.AUDIT_LOG == pre_audit


# --------------------------------------------------------------------------- #
# R4: Inactive user
# --------------------------------------------------------------------------- #

def test_R4_inactive_user_returns_403(store, ctx_factory, now_utc):
    pre_audit = list(fw.AUDIT_LOG)
    user = UserProfile(user_id="u1", last_login_at=now_utc - timedelta(days=6))
    ctx = ctx_factory(body=json.dumps({"amount_cents": 10}).encode("utf-8"))
    result = handle_request(ctx, user, store)
    assert result.status_code == 403
    assert store.has(ctx.idempotency_key) is False
    assert fw.AUDIT_LOG == pre_audit


# --------------------------------------------------------------------------- #
# R5: Payload validation
# --------------------------------------------------------------------------- #

def test_R5_invalid_json_returns_400_without_corrupting_other_keys(
    store, active_user, ctx_factory
):
    # Pre-populate store with K1 -> R1
    store.record("K1", "R1-fixed")
    pre_audit = list(fw.AUDIT_LOG)

    ctx = ctx_factory(idempotency_key="K2", body=b"{not json")
    result = handle_request(ctx, active_user, store)

    assert result.status_code == 400
    assert store.get_request_id("K1") == "R1-fixed"
    assert store.has("K2") is False
    assert fw.AUDIT_LOG == pre_audit


def test_R5_zero_amount_returns_422(store, active_user, ctx_factory):
    pre_audit = list(fw.AUDIT_LOG)
    ctx = ctx_factory(body=json.dumps({"amount_cents": 0}).encode("utf-8"))
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 422
    assert store.has(ctx.idempotency_key) is False
    assert fw.AUDIT_LOG == pre_audit


def test_R5_negative_amount_returns_422(store, active_user, ctx_factory):
    pre_audit = list(fw.AUDIT_LOG)
    ctx = ctx_factory(body=json.dumps({"amount_cents": -5}).encode("utf-8"))
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 422
    assert store.has(ctx.idempotency_key) is False
    assert fw.AUDIT_LOG == pre_audit


def test_R5_amount_cents_omitted_is_ok(store, active_user, ctx_factory):
    ctx = ctx_factory(body=json.dumps({"note": "hello"}).encode("utf-8"))
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert result.body["amount_cents"] is None


# --------------------------------------------------------------------------- #
# R6: Audit on success
# --------------------------------------------------------------------------- #

def test_R6_audit_appended_on_200(store, active_user, ctx_factory):
    ctx = ctx_factory(
        authorization=bearer(valid_token(sub="u1")),
        body=json.dumps({"amount_cents": 100}).encode("utf-8"),
    )
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    rid = result.body["request_id"]
    assert len(fw.AUDIT_LOG) == 1
    line = fw.AUDIT_LOG[0]
    assert "u1" in line
    assert rid in line
    assert "100" in line


def test_R6_audit_not_appended_on_non_200(store, active_user, ctx_factory):
    # Duplicate path -> 409, no audit
    ctx1 = ctx_factory()
    handle_request(ctx1, active_user, store)
    fw.AUDIT_LOG.clear()
    ctx2 = ctx_factory()
    result = handle_request(ctx2, active_user, store)
    assert result.status_code == 409
    assert fw.AUDIT_LOG == []


def test_R6_audit_failure_sets_flag_keeps_200(store, active_user, ctx_factory, monkeypatch):
    class _BoomList(list):
        def append(self, _item):
            raise RuntimeError("audit storage down")

    monkeypatch.setattr(fw, "AUDIT_LOG", _BoomList())
    ctx = ctx_factory(body=json.dumps({"amount_cents": 100}).encode("utf-8"))
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert result.body.get("audit_failed") is True
    assert result.body["result"] == "ok"
    # Despite audit failure, the store was written
    assert store.get_request_id(ctx.idempotency_key) == result.body["request_id"]


# --------------------------------------------------------------------------- #
# Concurrency: same key, two threads -> exactly one 200 and one 409
# --------------------------------------------------------------------------- #

def test_concurrent_same_key_yields_one_200_and_one_409(store, active_user, now_utc):
    auth = bearer(valid_token(sub="u1"))
    body = json.dumps({"amount_cents": 100}).encode("utf-8")
    key = "race-key"

    results: list[HandlerResult] = []
    barrier = threading.Barrier(2)
    lock = threading.Lock()

    def worker():
        ctx = RequestContext(
            authorization=auth,
            idempotency_key=key,
            request_received_at=now_utc,
            body_bytes=body,
        )
        barrier.wait()
        r = handle_request(ctx, active_user, store)
        with lock:
            results.append(r)

    threads = [threading.Thread(target=worker) for _ in range(2)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    statuses = sorted(r.status_code for r in results)
    assert statuses == [200, 409]

    success = next(r for r in results if r.status_code == 200)
    duplicate = next(r for r in results if r.status_code == 409)
    assert store.get_request_id(key) == success.body["request_id"]
    assert duplicate.body == {
        "reason": "duplicate",
        "original_request_id": success.body["request_id"],
    }


# --------------------------------------------------------------------------- #
# Processing order checks (auth before active-user, etc.)
# --------------------------------------------------------------------------- #

def test_order_auth_before_active_user(store, ctx_factory, now_utc):
    """Inactive user + missing auth -> 401 (auth checked first)."""
    pre_audit = list(fw.AUDIT_LOG)
    inactive = UserProfile(user_id="u1", last_login_at=now_utc - timedelta(days=30))
    ctx = ctx_factory(authorization=None)
    result = handle_request(ctx, inactive, store)
    assert result.status_code == 401
    assert fw.AUDIT_LOG == pre_audit


def test_order_active_before_duplicate(store, ctx_factory, now_utc):
    """Inactive user + duplicate key -> 403 (active-user checked before duplicate)."""
    # Seed the store so the key is a duplicate
    key = "dup-key"
    store.record(key, "previous-rid")

    inactive = UserProfile(user_id="u1", last_login_at=now_utc - timedelta(days=30))
    ctx = ctx_factory(idempotency_key=key)
    result = handle_request(ctx, inactive, store)
    assert result.status_code == 403
    # Store still has the original entry, untouched
    assert store.get_request_id(key) == "previous-rid"


def test_order_duplicate_before_body_validation(store, active_user, ctx_factory):
    """Duplicate key + invalid JSON -> 409 (duplicate checked before body)."""
    key = "dup-key-2"
    store.record(key, "rid-existing")
    ctx = ctx_factory(idempotency_key=key, body=b"{not json")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 409
    assert result.body["original_request_id"] == "rid-existing"