
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""Tests for foo_work module."""
from __future__ import annotations

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

# Ensure src/ is on the path so we can import foo_work
_HERE = os.path.dirname(os.path.abspath(__file__))
_SRC = os.path.join(_HERE, "src")
if _SRC not in sys.path:

import foo_work
from foo_work import (
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
# Helpers
# --------------------------------------------------------------------------- #


def _b64url(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


def make_jwt(claims: dict) -> str:
    header = _b64url(b'{"alg":"none","typ":"JWT"}')
    payload = _b64url(json.dumps(claims).encode("utf-8"))
    return f"{header}.{payload}.sig"


def valid_claims(sub: str = "u1", scope: str = "foo:invoke", exp_offset: int = 3600) -> dict:
    return {
        "sub": sub,
        "scope": scope,
        "exp": int(datetime.now(timezone.utc).timestamp()) + exp_offset,
    }


def make_bearer(claims: dict | None = None) -> str:
    return "Bearer " + make_jwt(claims if claims is not None else valid_claims())


@pytest.fixture(autouse=True)
def reset_audit_log():
    """Ensure each test starts with an empty AUDIT_LOG and restores after."""
    original = list(AUDIT_LOG)
    AUDIT_LOG.clear()
    yield
    AUDIT_LOG.clear()
    AUDIT_LOG.extend(original)


@pytest.fixture
def store() -> IdempotencyStore:
    return IdempotencyStore()


@pytest.fixture
def now() -> datetime:
    return datetime.now(timezone.utc)


@pytest.fixture
def active_user(now) -> UserProfile:
    return UserProfile(user_id="u1", last_login_at=now - timedelta(days=1))


def make_ctx(
    *,
    authorization: str | None = None,
    idempotency_key: str | None = "key-1",
    request_received_at: datetime | None = None,
    body_bytes: bytes | None = None,
) -> RequestContext:
    if authorization is None:
        authorization = make_bearer()
    if request_received_at is None:
        request_received_at = datetime.now(timezone.utc)
    return RequestContext(
        authorization=authorization,
        idempotency_key=idempotency_key,
        request_received_at=request_received_at,
        body_bytes=body_bytes,
    )


# --------------------------------------------------------------------------- #
# parse_bearer_jwt
# --------------------------------------------------------------------------- #


def test_parse_bearer_jwt_valid():
    ok, claims, err = parse_bearer_jwt(make_bearer())
    assert ok is True
    assert err is None
    assert claims["sub"] == "u1"
    assert "foo:invoke" in claims["scope"].split()


def test_parse_bearer_jwt_none():
    ok, claims, err = parse_bearer_jwt(None)
    assert ok is False
    assert claims is None
    assert err is not None


def test_parse_bearer_jwt_empty_string():
    ok, claims, err = parse_bearer_jwt("")
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_not_bearer():
    ok, claims, _err = parse_bearer_jwt("Basic abc.def.ghi")
    assert ok is False
    assert claims is None


def test_parse_bearer_jwt_bearer_no_token():
    ok, _claims, _err = parse_bearer_jwt("Bearer ")
    assert ok is False


def test_parse_bearer_jwt_malformed_token():
    # Only one segment
    ok, _claims, _err = parse_bearer_jwt("Bearer notajwt")
    assert ok is False


def test_parse_bearer_jwt_undecodable_payload():
    # Header is fine, payload is invalid base64/json
    header = _b64url(b'{"alg":"none"}')
    ok, _claims, _err = parse_bearer_jwt(f"Bearer {header}.!!!notbase64!!!.sig")
    assert ok is False


def test_parse_bearer_jwt_expired():
    claims = valid_claims(exp_offset=-10)
    ok, _claims, _err = parse_bearer_jwt("Bearer " + make_jwt(claims))
    assert ok is False


def test_parse_bearer_jwt_missing_scope():
    claims = valid_claims()
    del claims["scope"]
    ok, _claims, _err = parse_bearer_jwt("Bearer " + make_jwt(claims))
    assert ok is False


def test_parse_bearer_jwt_wrong_scope():
    claims = valid_claims(scope="other:scope")
    ok, _claims, _err = parse_bearer_jwt("Bearer " + make_jwt(claims))
    assert ok is False


def test_parse_bearer_jwt_scope_as_list():
    claims = valid_claims()
    claims["scope"] = ["foo:invoke", "bar:read"]
    ok, parsed, _err = parse_bearer_jwt("Bearer " + make_jwt(claims))
    assert ok is True
    assert parsed is not None


def test_parse_bearer_jwt_missing_exp():
    claims = {"sub": "u1", "scope": "foo:invoke"}
    ok, _claims, _err = parse_bearer_jwt("Bearer " + make_jwt(claims))
    assert ok is False


# --------------------------------------------------------------------------- #
# is_active_user
# --------------------------------------------------------------------------- #


def test_is_active_user_recent(now):
    user = UserProfile(user_id="u1", last_login_at=now - timedelta(days=1))
    assert is_active_user(user, now) is True


def test_is_active_user_exactly_five_days(now):
    user = UserProfile(user_id="u1", last_login_at=now - timedelta(days=5))
    assert is_active_user(user, now) is True


def test_is_active_user_six_days(now):
    user = UserProfile(user_id="u1", last_login_at=now - timedelta(days=6))
    assert is_active_user(user, now) is False


# --------------------------------------------------------------------------- #
# IdempotencyStore
# --------------------------------------------------------------------------- #


def test_store_initially_empty(store):
    assert store.has("k1") is False
    assert store.get_request_id("k1") is None


def test_store_record_and_get(store):
    store.record("k1", "rid-1")
    assert store.has("k1") is True
    assert store.get_request_id("k1") == "rid-1"


def test_store_independent_keys(store):
    store.record("k1", "rid-1")
    store.record("k2", "rid-2")
    assert store.get_request_id("k1") == "rid-1"
    assert store.get_request_id("k2") == "rid-2"


# --------------------------------------------------------------------------- #
# R1: Successful first request
# --------------------------------------------------------------------------- #


def test_r1_first_request_returns_200_and_records_key(store, active_user):
    ctx = make_ctx(body_bytes=b'{"amount_cents": 100}')
    result = handle_request(ctx, active_user, store)

    assert isinstance(result, HandlerResult)
    assert result.status_code == 200
    assert result.body["result"] == "ok"
    rid = result.body["request_id"]
    # request_id must be a uuid4 string
    parsed_uuid = uuid.UUID(rid)
    assert parsed_uuid.version == 4
    assert result.body["amount_cents"] == 100
    assert store.get_request_id(ctx.idempotency_key) == rid


def test_r1_no_body_returns_200_with_null_amount(store, active_user):
    ctx = make_ctx(body_bytes=None)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert result.body["amount_cents"] is None
    assert result.body["result"] == "ok"


def test_r1_empty_body_returns_200(store, active_user):
    ctx = make_ctx(body_bytes=b"")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert result.body["amount_cents"] is None


def test_r1_body_without_amount_returns_200(store, active_user):
    ctx = make_ctx(body_bytes=b'{"note": "hello"}')
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert result.body["amount_cents"] is None


# --------------------------------------------------------------------------- #
# R2: Duplicate idempotency key
# --------------------------------------------------------------------------- #


def test_r2_duplicate_key_returns_409_unchanged(store, active_user):
    ctx1 = make_ctx(body_bytes=b'{"amount_cents": 50}')
    first = handle_request(ctx1, active_user, store)
    assert first.status_code == 200
    stored_rid = store.get_request_id(ctx1.idempotency_key)

    ctx2 = make_ctx(body_bytes=b'{"amount_cents": 999}')
    second = handle_request(ctx2, active_user, store)
    assert second.status_code == 409
    assert second.body == {"reason": "duplicate", "original_request_id": stored_rid}
    # Store unchanged
    assert store.get_request_id(ctx1.idempotency_key) == stored_rid


def test_r2_duplicate_does_not_add_audit_entry(store, active_user):
    ctx = make_ctx(body_bytes=b'{"amount_cents": 50}')
    handle_request(ctx, active_user, store)
    audit_after_first = list(AUDIT_LOG)

    handle_request(ctx, active_user, store)
    assert AUDIT_LOG == audit_after_first  # no new audit entries


# --------------------------------------------------------------------------- #
# R3: Authorization gate
# --------------------------------------------------------------------------- #


@pytest.mark.parametrize(
    "auth_header",
    [
        None,
        "",
        "Basic xyz",
        "Bearer ",
        "Bearer notajwt",
    ],
)
def test_r3_missing_or_malformed_auth_returns_401(auth_header, store, active_user):
    ctx = make_ctx(authorization=auth_header)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401
    # Store unchanged
    assert store.has(ctx.idempotency_key) is False
    # AUDIT_LOG unchanged
    assert AUDIT_LOG == []


def test_r3_expired_token_returns_401(store, active_user):
    expired = make_jwt(valid_claims(exp_offset=-100))
    ctx = make_ctx(authorization=f"Bearer {expired}")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401
    assert store.has(ctx.idempotency_key) is False
    assert AUDIT_LOG == []


def test_r3_wrong_scope_returns_401(store, active_user):
    bad = make_jwt(valid_claims(scope="other:scope"))
    ctx = make_ctx(authorization=f"Bearer {bad}")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401
    assert store.has(ctx.idempotency_key) is False
    assert AUDIT_LOG == []


def test_r3_undecodable_payload_returns_401(store, active_user):
    ctx = make_ctx(authorization="Bearer aaa.!!!bad!!!.ccc")
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401
    assert store.has(ctx.idempotency_key) is False
    assert AUDIT_LOG == []


# --------------------------------------------------------------------------- #
# R4: Inactive user
# --------------------------------------------------------------------------- #


def test_r4_inactive_user_returns_403(store, now):
    inactive = UserProfile(user_id="u1", last_login_at=now - timedelta(days=6))
    ctx = make_ctx(
        request_received_at=now,
        body_bytes=b'{"amount_cents": 100}',
    )
    result = handle_request(ctx, inactive, store)
    assert result.status_code == 403
    assert store.has(ctx.idempotency_key) is False
    assert AUDIT_LOG == []


def test_r4_boundary_five_days_is_active(store, now):
    user = UserProfile(user_id="u1", last_login_at=now - timedelta(days=5))
    ctx = make_ctx(request_received_at=now, body_bytes=b'{"amount_cents": 1}')
    result = handle_request(ctx, user, store)
    assert result.status_code == 200


# --------------------------------------------------------------------------- #
# R5: Payload validation
# --------------------------------------------------------------------------- #


def test_r5_invalid_json_returns_400_no_mutation(store, active_user):
    # Pre-populate another key
    store.record("K1", "R1")
    ctx = make_ctx(idempotency_key="K2", body_bytes=b'{not json')
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 400
    # Other key untouched
    assert store.get_request_id("K1") == "R1"
    # K2 not written
    assert store.has("K2") is False


def test_r5_amount_cents_zero_returns_422(store, active_user):
    ctx = make_ctx(body_bytes=b'{"amount_cents": 0}')
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 422
    assert store.has(ctx.idempotency_key) is False


def test_r5_amount_cents_negative_returns_422(store, active_user):
    ctx = make_ctx(body_bytes=b'{"amount_cents": -5}')
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 422
    assert store.has(ctx.idempotency_key) is False


def test_r5_amount_cents_positive_returns_200(store, active_user):
    ctx = make_ctx(body_bytes=b'{"amount_cents": 1}')
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    assert result.body["amount_cents"] == 1


def test_r5_bad_payload_does_not_add_audit(store, active_user):
    ctx = make_ctx(body_bytes=b'not json at all')
    handle_request(ctx, active_user, store)
    assert AUDIT_LOG == []


# --------------------------------------------------------------------------- #
# R6: Audit
# --------------------------------------------------------------------------- #


def test_r6_audit_appended_on_200(store, active_user):
    ctx = make_ctx(body_bytes=b'{"amount_cents": 100}')
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 200
    rid = result.body["request_id"]
    assert len(AUDIT_LOG) == 1
    line = AUDIT_LOG[0]
    assert "u1" in line
    assert rid in line
    assert "100" in line


def test_r6_audit_failure_sets_flag_but_keeps_200(store, active_user):
    ctx = make_ctx(body_bytes=b'{"amount_cents": 100}')

    original_append = list.append

    def bad_append(self, item):
        if self is foo_work.AUDIT_LOG:
            raise RuntimeError("disk full")
        return original_append(self, item)

    with patch.object(foo_work.AUDIT_LOG, "append", side_effect=RuntimeError("disk full")):
        result = handle_request(ctx, active_user, store)

    assert result.status_code == 200
    assert result.body.get("audit_failed") is True
    # The key still got recorded
    assert store.get_request_id(ctx.idempotency_key) == result.body["request_id"]


def test_r6_no_audit_on_non_200(store, active_user):
    # Inactive user (403)
    inactive = UserProfile(
        user_id="u1",
        last_login_at=datetime.now(timezone.utc) - timedelta(days=10),
    )
    ctx = make_ctx(body_bytes=b'{"amount_cents": 100}')
    handle_request(ctx, inactive, store)
    assert AUDIT_LOG == []


# --------------------------------------------------------------------------- #
# Idempotency key presence
# --------------------------------------------------------------------------- #


def test_missing_idempotency_key_is_rejected(store, active_user):
    ctx = make_ctx(idempotency_key=None)
    result = handle_request(ctx, active_user, store)
    assert result.status_code != 200
    assert store.has("") is False


def test_empty_idempotency_key_is_rejected(store, active_user):
    ctx = make_ctx(idempotency_key="")
    result = handle_request(ctx, active_user, store)
    assert result.status_code != 200


# --------------------------------------------------------------------------- #
# R2 concurrency
# --------------------------------------------------------------------------- #


def test_concurrent_same_key_yields_one_200_and_one_409(store, active_user):
    barrier = threading.Barrier(2)
    results: list[HandlerResult] = []
    results_lock = threading.Lock()

    def worker():
        ctx = make_ctx(body_bytes=b'{"amount_cents": 50}')
        barrier.wait()
        res = handle_request(ctx, active_user, store)
        with results_lock:
            results.append(res)

    threads = [threading.Thread(target=worker) for _ in range(2)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    statuses = sorted(r.status_code for r in results)
    assert statuses == [200, 409]

    ok_result = next(r for r in results if r.status_code == 200)
    dup_result = next(r for r in results if r.status_code == 409)

    assert store.get_request_id("key-1") == ok_result.body["request_id"]
    assert dup_result.body["original_request_id"] == ok_result.body["request_id"]


def test_concurrent_many_threads_same_key_exactly_one_success(active_user):
    store = IdempotencyStore()
    n = 8
    barrier = threading.Barrier(n)
    results: list[HandlerResult] = []
    results_lock = threading.Lock()

    def worker():
        ctx = make_ctx(idempotency_key="shared", body_bytes=b'{"amount_cents": 10}')
        barrier.wait()
        res = handle_request(ctx, active_user, store)
        with results_lock:
            results.append(res)

    threads = [threading.Thread(target=worker) for _ in range(n)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    successes = [r for r in results if r.status_code == 200]
    duplicates = [r for r in results if r.status_code == 409]
    assert len(successes) == 1
    assert len(duplicates) == n - 1
    for d in duplicates:
        assert d.body["original_request_id"] == successes[0].body["request_id"]


# --------------------------------------------------------------------------- #
# Processing order sanity
# --------------------------------------------------------------------------- #


def test_auth_checked_before_idempotency_key(store, active_user):
    # Missing key AND bad auth -> 401 takes precedence
    ctx = make_ctx(authorization=None, idempotency_key=None)
    result = handle_request(ctx, active_user, store)
    assert result.status_code == 401


def test_active_user_checked_before_body_validation(store, now):
    # Inactive user + bad JSON -> 403, not 400
    inactive = UserProfile(user_id="u1", last_login_at=now - timedelta(days=30))
    ctx = make_ctx(request_received_at=now, body_bytes=b"{bad json")
    result = handle_request(ctx, inactive, store)
    assert result.status_code == 403


def test_duplicate_checked_before_body_validation(store, active_user):
    # First valid request to populate the store
    ctx1 = make_ctx(body_bytes=b'{"amount_cents": 5}')
    handle_request(ctx1, active_user, store)
    # Now a duplicate with bad JSON body -> 409 (duplicate check before body)
    ctx2 = make_ctx(body_bytes=b"{bad json")
    result = handle_request(ctx2, active_user, store)
    assert result.status_code == 409