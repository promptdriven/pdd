"""Step 2 acceptance tests — email-based input (8 tests).

Cumulative: step 0 (4) + step 1 (2) + step 2 (2) = 8 tests.
"""

from __future__ import annotations

import copy
import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "src")))

from user_id_parser import parse_user_id, parse_user_ids


# --- Step 0 tests (4) ---


def test_accepts_supported_input_shapes():
    assert parse_user_id("user:AbC_123") == "abc_123"
    assert parse_user_id({"user_id": " Bob-01 "}) == "bob-01"
    assert parse_user_id({"user": {"id": "Carol_9"}}) == "carol_9"


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
    assert parse_user_id(payload) == "alice_1"
    assert payload == original


# --- Step 1 tests (2) ---


def test_batch_processing_preserves_order():
    items = [
        "user:Alice_1",
        "user:admin",
        {"user_id": "Bob-99"},
        None,
    ]
    result = parse_user_ids(items)
    assert result == ["alice_1", None, "bob-99", None]


def test_batch_processing_handles_empty_and_all_invalid():
    assert parse_user_ids([]) == []
    assert parse_user_ids([None, 123, "bad"]) == [None, None, None]


# --- Step 2 tests (2) ---


def test_email_input_extracts_username():
    """email:user@example.com extracts username before @, applies same rules."""
    assert parse_user_id("email:alice_1@example.com") == "alice_1"
    assert parse_user_id("email:  Bob-99@corp.io  ") == "bob-99"


def test_email_input_validation_rules():
    """Email-extracted usernames must pass the same validation rules."""
    assert parse_user_id("email:ab@x.com") is None        # too short
    assert parse_user_id("email:admin@x.com") is None      # reserved
    assert parse_user_id("email:bad space@x.com") is None  # invalid chars
    assert parse_user_id("email:@x.com") is None           # empty username
    assert parse_user_id("email:noatsign") is None          # no @ sign
