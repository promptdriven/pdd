"""Acceptance tests for replay-stability A/B experiment."""

import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "src")))

from user_id_parser import parse_user_id


def test_string_input_supported():
    assert parse_user_id("user:abc123") == "abc123"
    assert parse_user_id("  user:abc123  ") == "abc123"


def test_dict_input_supported():
    assert parse_user_id({"user_id": "abc123"}) == "abc123"
    assert parse_user_id({"user_id": "  abc123  "}) == "abc123"


def test_invalid_values_return_none():
    assert parse_user_id(None) is None
    assert parse_user_id({"user_id": ""}) is None
    assert parse_user_id({"user_id": "   "}) is None
    assert parse_user_id({"id": "abc123"}) is None
    assert parse_user_id({"user_id": 123}) is None
    assert parse_user_id("admin:abc123") is None
    assert parse_user_id("user:") is None
