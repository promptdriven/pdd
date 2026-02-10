"""Step 0 acceptance tests — medium baseline (4 tests).

Cumulative test count: 4
"""

from __future__ import annotations

import copy
import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "src")))

from user_id_parser import parse_user_id


def test_accepts_supported_input_shapes():
    """String 'user:<id>', flat dict, and nested dict all produce valid IDs."""
    assert parse_user_id("user:AbC_123") == "abc_123"
    assert parse_user_id({"user_id": " Bob-01 "}) == "bob-01"
    assert parse_user_id({"user": {"id": "Carol_9"}}) == "carol_9"


def test_rejects_reserved_and_invalid_ids():
    assert parse_user_id("user:admin") is None
    assert parse_user_id("user:root") is None
    assert parse_user_id("user:system") is None
    assert parse_user_id("user:ab") is None  # too short
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
