"""Step 4 acceptance tests — structured result / BREAKING CHANGE (12 tests).

All previous tests updated to use ParseResult.user_id.
Cumulative: step 0-3 (10, updated) + step 4 (2) = 12 tests.
"""

from __future__ import annotations

import copy
import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "src")))

from user_id_parser import ParseResult, parse_user_id, parse_user_ids


# --- Step 0 tests (4) — updated for ParseResult ---


def test_accepts_supported_input_shapes():
    r1 = parse_user_id("user:AbC_123")
    assert r1 is not None and r1.user_id == "abc_123"

    r2 = parse_user_id({"user_id": " Bob-01 "})
    assert r2 is not None and r2.user_id == "bob-01"

    r3 = parse_user_id({"user": {"id": "Carol_9"}})
    assert r3 is not None and r3.user_id == "carol_9"


def test_rejects_reserved_and_invalid_ids():
    assert parse_user_id("user:admin") is None
    assert parse_user_id("user:root") is None
    assert parse_user_id("user:system") is None
    assert parse_user_id("user:ab") is None
    assert parse_user_id("user:this_identifier_is_way_too_long") is None
    assert parse_user_id("user:bad space") is None
    assert parse_user_id("user:bad$char") is None


def test_rejects_bad_payloads_without_throwing():
    assert parse_user_id(None) is None
    assert parse_user_id(123) is None
    assert parse_user_id({"user_id": 123}) is None
    assert parse_user_id({"user": {"id": 123}}) is None
    assert parse_user_id({"user": {}}) is None
    assert parse_user_id({"id": "abc123"}) is None
    assert parse_user_id("admin:abc123") is None


def test_does_not_mutate_dict_inputs():
    payload = {"user_id": "  Alice_1  "}
    original = copy.deepcopy(payload)
    r = parse_user_id(payload)
    assert r is not None and r.user_id == "alice_1"
    assert payload == original


# --- Step 1 tests (2) — updated for ParseResult ---


def test_batch_processing_preserves_order():
    items = [
        "user:Alice_1",
        "user:admin",
        {"user_id": "Bob-99"},
        None,
    ]
    result = parse_user_ids(items)
    assert len(result) == 4
    assert result[0] is not None and result[0].user_id == "alice_1"
    assert result[1] is None
    assert result[2] is not None and result[2].user_id == "bob-99"
    assert result[3] is None


def test_batch_processing_handles_empty_and_all_invalid():
    assert parse_user_ids([]) == []
    result = parse_user_ids([None, 123, "bad"])
    assert result == [None, None, None]


# --- Step 2 tests (2) — updated for ParseResult ---


def test_email_input_extracts_username():
    r1 = parse_user_id("email:alice_1@example.com")
    assert r1 is not None and r1.user_id == "alice_1"

    r2 = parse_user_id("email:  Bob-99@corp.io  ")
    assert r2 is not None and r2.user_id == "bob-99"


def test_email_input_validation_rules():
    assert parse_user_id("email:ab@x.com") is None
    assert parse_user_id("email:admin@x.com") is None
    assert parse_user_id("email:bad space@x.com") is None
    assert parse_user_id("email:@x.com") is None
    assert parse_user_id("email:noatsign") is None


# --- Step 3 tests (2) — updated for ParseResult ---


def test_configurable_reserved_ids():
    assert parse_user_id("user:admin") is None
    assert parse_user_id("user:root") is None

    r1 = parse_user_id("user:admin", reserved_ids={"blocked"})
    assert r1 is not None and r1.user_id == "admin"

    assert parse_user_id("user:blocked", reserved_ids={"blocked"}) is None

    r2 = parse_user_id("user:admin", reserved_ids=set())
    assert r2 is not None and r2.user_id == "admin"


def test_batch_with_custom_reserved_ids():
    items = ["user:admin", "user:hello", "user:banned"]
    result = parse_user_ids(items, reserved_ids={"banned"})
    assert len(result) == 3
    assert result[0] is not None and result[0].user_id == "admin"
    assert result[1] is not None and result[1].user_id == "hello"
    assert result[2] is None


# --- Step 4 tests (2) — NEW: source field ---


def test_parse_result_source_string_and_dict():
    """ParseResult.source tracks input type."""
    r1 = parse_user_id("user:alice_1")
    assert r1 is not None
    assert r1.source == "string"

    r2 = parse_user_id({"user_id": "bob_99"})
    assert r2 is not None
    assert r2.source == "dict_flat"

    r3 = parse_user_id({"user": {"id": "carol_1"}})
    assert r3 is not None
    assert r3.source == "dict_nested"


def test_parse_result_source_email():
    """ParseResult.source is 'email' for email inputs."""
    r = parse_user_id("email:alice_1@example.com")
    assert r is not None
    assert r.source == "email"
    assert r.user_id == "alice_1"
