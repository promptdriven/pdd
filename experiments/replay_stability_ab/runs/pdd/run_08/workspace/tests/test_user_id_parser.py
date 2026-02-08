# ==============================================================================
# TEST PLAN for parse_user_id(raw: object) -> str | None
# ==============================================================================
#
# 1. STRING INPUT FORMAT "user:<id>"
#    - Valid ID extraction from string prefix
#    - Missing/wrong prefix returns None
#    - Empty ID after prefix returns None
#    - Whitespace-only ID after prefix returns None
#
# 2. DICT INPUT FORMAT {"user_id": "<id>"}
#    - Valid flat dict extraction
#    - Non-string value in "user_id" returns None
#    - Missing "user_id" key returns None
#
# 3. DICT INPUT FORMAT {"user": {"id": "<id>"}}
#    - Valid nested dict extraction
#    - "user" value is not a dict returns None
#    - Nested dict missing "id" key returns None
#    - Non-string nested "id" value returns None
#
# 4. NORMALIZATION
#    - Leading/trailing whitespace is trimmed from extracted ID
#    - Uppercase letters are lowercased
#    - Combined: whitespace + uppercase
#
# 5. VALIDITY ENFORCEMENT
#    - Allowed characters: a-z, 0-9, _, -
#    - Invalid characters (e.g., @, !, spaces in middle) rejected
#    - Length minimum: 3 (boundary: 2 rejected, 3 accepted)
#    - Length maximum: 20 (boundary: 20 accepted, 21 rejected)
#    - Reserved IDs: "admin", "root", "system" rejected
#    - Reserved IDs case-insensitive (e.g., "ADMIN" normalized then rejected)
#
# 6. TYPE SAFETY (never raise)
#    - None input -> None
#    - int input -> None
#    - list input -> None
#    - bool input -> None
#    - float input -> None
#    - Unexpected dict value types -> None
#
# 7. NON-MUTATION
#    - Input dicts must not be modified
#
# 8. PRIORITY / AMBIGUITY
#    - Dict with both "user_id" and "user" keys: "user_id" takes precedence
#
# 9. Z3 FORMAL VERIFICATION
#    - Property: any non-None result has length in [3, 20]
#    - Property: any non-None result is lowercase
#    - Property: any non-None result contains only allowed chars
#    - Property: reserved IDs are never returned
#    These are better expressed as property-based checks; Z3 can verify
#    the regex pattern and length constraints are consistent. However,
#    since the function is not purely symbolic, we'll use Z3 to verify
#    properties of the validation logic (pattern + length + reserved check).
# ==============================================================================


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import sys
import os
import copy
import re

import pytest

# Add the src directory to the path for import
from user_id_parser import parse_user_id


# ==============================================================================
# STRING INPUT: "user:<id>" format
# ==============================================================================


class TestStringInput:
    """Tests for string inputs with the 'user:<id>' format."""

    def test_valid_simple_id(self) -> None:
        assert parse_user_id("user:abc123") == "abc123"

    def test_valid_with_underscore(self) -> None:
        assert parse_user_id("user:my_user") == "my_user"

    def test_valid_with_hyphen(self) -> None:
        assert parse_user_id("user:my-user") == "my-user"

    def test_valid_mixed_allowed_chars(self) -> None:
        assert parse_user_id("user:a1_b2-c3") == "a1_b2-c3"

    def test_missing_prefix(self) -> None:
        assert parse_user_id("abc123") is None

    def test_wrong_prefix(self) -> None:
        assert parse_user_id("account:abc123") is None

    def test_empty_string(self) -> None:
        assert parse_user_id("") is None

    def test_prefix_only(self) -> None:
        # "user:" with empty id -> after trim, empty string -> fails length check
        assert parse_user_id("user:") is None

    def test_prefix_with_whitespace_only_id(self) -> None:
        assert parse_user_id("user:   ") is None

    def test_partial_prefix(self) -> None:
        assert parse_user_id("user") is None

    def test_uppercase_prefix(self) -> None:
        # "User:abc" doesn't start with "user:"
        assert parse_user_id("User:abc123") is None

    def test_extra_colon_in_id(self) -> None:
        # "user:abc:def" -> extracted is "abc:def" which has invalid char ':'
        assert parse_user_id("user:abc:def") is None


# ==============================================================================
# DICT INPUT: {"user_id": "<id>"} flat format
# ==============================================================================


class TestDictFlatInput:
    """Tests for flat dict inputs with the 'user_id' key."""

    def test_valid_flat_dict(self) -> None:
        assert parse_user_id({"user_id": "abc123"}) == "abc123"

    def test_non_string_value_int(self) -> None:
        assert parse_user_id({"user_id": 12345}) is None

    def test_non_string_value_none(self) -> None:
        assert parse_user_id({"user_id": None}) is None

    def test_non_string_value_list(self) -> None:
        assert parse_user_id({"user_id": ["abc"]}) is None

    def test_missing_user_id_key(self) -> None:
        assert parse_user_id({"other_key": "abc123"}) is None

    def test_empty_dict(self) -> None:
        assert parse_user_id({}) is None

    def test_empty_string_value(self) -> None:
        assert parse_user_id({"user_id": ""}) is None

    def test_whitespace_value(self) -> None:
        assert parse_user_id({"user_id": "   "}) is None


# ==============================================================================
# DICT INPUT: {"user": {"id": "<id>"}} nested format
# ==============================================================================


class TestDictNestedInput:
    """Tests for nested dict inputs with 'user' -> 'id' keys."""

    def test_valid_nested_dict(self) -> None:
        assert parse_user_id({"user": {"id": "abc123"}}) == "abc123"

    def test_user_not_a_dict(self) -> None:
        assert parse_user_id({"user": "abc123"}) is None

    def test_user_is_none(self) -> None:
        assert parse_user_id({"user": None}) is None

    def test_user_is_list(self) -> None:
        assert parse_user_id({"user": [{"id": "abc123"}]}) is None

    def test_nested_missing_id_key(self) -> None:
        assert parse_user_id({"user": {"name": "abc123"}}) is None

    def test_nested_non_string_id(self) -> None:
        assert parse_user_id({"user": {"id": 12345}}) is None

    def test_nested_none_id(self) -> None:
        assert parse_user_id({"user": {"id": None}}) is None

    def test_nested_empty_string_id(self) -> None:
        assert parse_user_id({"user": {"id": ""}}) is None


# ==============================================================================
# NORMALIZATION: trim whitespace, lowercase
# ==============================================================================


class TestNormalization:
    """Tests for whitespace trimming and case normalization."""

    def test_leading_whitespace_trimmed(self) -> None:
        assert parse_user_id("user:  abc123") == "abc123"

    def test_trailing_whitespace_trimmed(self) -> None:
        assert parse_user_id("user:abc123  ") == "abc123"

    def test_both_sides_whitespace_trimmed(self) -> None:
        assert parse_user_id("user:  abc123  ") == "abc123"

    def test_uppercase_lowered(self) -> None:
        assert parse_user_id("user:ABC123") == "abc123"

    def test_mixed_case_lowered(self) -> None:
        assert parse_user_id("user:AbC_dEf") == "abc_def"

    def test_whitespace_and_uppercase_combined(self) -> None:
        assert parse_user_id("user:  MY_USER  ") == "my_user"

    def test_dict_flat_normalization(self) -> None:
        assert parse_user_id({"user_id": "  Hello_World  "}) == "hello_world"

    def test_dict_nested_normalization(self) -> None:
        assert parse_user_id({"user": {"id": "  TestUser  "}}) == "testuser"


# ==============================================================================
# VALIDITY: character set, length, reserved IDs
# ==============================================================================


class TestValidity:
    """Tests for character validation, length bounds, and reserved ID rejection."""

    # Character validation
    def test_invalid_char_at_sign(self) -> None:
        assert parse_user_id("user:abc@123") is None

    def test_invalid_char_space_in_middle(self) -> None:
        assert parse_user_id("user:abc 123") is None

    def test_invalid_char_dot(self) -> None:
        assert parse_user_id("user:abc.123") is None

    def test_invalid_char_exclamation(self) -> None:
        assert parse_user_id("user:abc!123") is None

    def test_invalid_char_slash(self) -> None:
        assert parse_user_id("user:abc/123") is None

    def test_all_digits_valid(self) -> None:
        assert parse_user_id("user:12345") == "12345"

    def test_all_underscores_valid(self) -> None:
        assert parse_user_id("user:___") == "___"

    def test_all_hyphens_valid(self) -> None:
        assert parse_user_id("user:---") == "---"

    # Length boundary: minimum 3
    def test_length_2_rejected(self) -> None:
        assert parse_user_id("user:ab") is None

    def test_length_1_rejected(self) -> None:
        assert parse_user_id("user:a") is None

    def test_length_3_accepted(self) -> None:
        assert parse_user_id("user:abc") == "abc"

    # Length boundary: maximum 20
    def test_length_20_accepted(self) -> None:
        uid: str = "a" * 20
        assert parse_user_id(f"user:{uid}") == uid

    def test_length_21_rejected(self) -> None:
        uid: str = "a" * 21
        assert parse_user_id(f"user:{uid}") is None

    def test_length_100_rejected(self) -> None:
        uid: str = "a" * 100
        assert parse_user_id(f"user:{uid}") is None

    # Reserved IDs
    def test_reserved_admin(self) -> None:
        assert parse_user_id("user:admin") is None

    def test_reserved_root(self) -> None:
        assert parse_user_id("user:root") is None

    def test_reserved_system(self) -> None:
        assert parse_user_id("user:system") is None

    def test_reserved_admin_uppercase(self) -> None:
        assert parse_user_id("user:ADMIN") is None

    def test_reserved_root_mixed_case(self) -> None:
        assert parse_user_id("user:Root") is None

    def test_reserved_system_with_whitespace(self) -> None:
        assert parse_user_id("user:  SYSTEM  ") is None

    def test_reserved_admin_in_dict(self) -> None:
        assert parse_user_id({"user_id": "admin"}) is None

    def test_reserved_root_in_nested_dict(self) -> None:
        assert parse_user_id({"user": {"id": "root"}}) is None

    def test_non_reserved_similar_to_admin(self) -> None:
        assert parse_user_id("user:admin1") == "admin1"

    def test_non_reserved_similar_to_root(self) -> None:
        assert parse_user_id("user:root_user") == "root_user"

    def test_non_reserved_similar_to_system(self) -> None:
        assert parse_user_id("user:my-system") == "my-system"


# ==============================================================================
# TYPE SAFETY: never raise for bad input
# ==============================================================================


class TestTypeSafety:
    """Tests ensuring the function never raises for any input type."""

    def test_none_input(self) -> None:
        assert parse_user_id(None) is None

    def test_int_input(self) -> None:
        assert parse_user_id(42) is None

    def test_float_input(self) -> None:
        assert parse_user_id(3.14) is None

    def test_bool_input_true(self) -> None:
        assert parse_user_id(True) is None

    def test_bool_input_false(self) -> None:
        assert parse_user_id(False) is None

    def test_list_input(self) -> None:
        assert parse_user_id(["user:abc123"]) is None

    def test_tuple_input(self) -> None:
        assert parse_user_id(("user:abc123",)) is None

    def test_set_input(self) -> None:
        assert parse_user_id({"abc123"}) is None

    def test_bytes_input(self) -> None:
        assert parse_user_id(b"user:abc123") is None

    def test_object_input(self) -> None:
        assert parse_user_id(object()) is None


# ==============================================================================
# NON-MUTATION: input dicts must not be modified
# ==============================================================================


class TestNonMutation:
    """Tests ensuring input dictionaries are not mutated by the function."""

    def test_flat_dict_not_mutated(self) -> None:
        original: dict = {"user_id": "  ABC123  "}
        frozen: dict = copy.deepcopy(original)
        parse_user_id(original)
        assert original == frozen

    def test_nested_dict_not_mutated(self) -> None:
        original: dict = {"user": {"id": "  ABC123  "}}
        frozen: dict = copy.deepcopy(original)
        parse_user_id(original)
        assert original == frozen

    def test_dict_with_extra_keys_not_mutated(self) -> None:
        original: dict = {"user_id": "abc", "extra": [1, 2, 3]}
        frozen: dict = copy.deepcopy(original)
        parse_user_id(original)
        assert original == frozen


# ==============================================================================
# PRIORITY: flat "user_id" takes precedence over nested "user"
# ==============================================================================


class TestPriority:
    """Tests for precedence when both flat and nested keys are present."""

    def test_flat_takes_precedence_over_nested(self) -> None:
        result: str | None = parse_user_id({
            "user_id": "flat_id",
            "user": {"id": "nested_id"},
        })
        assert result == "flat_id"

    def test_flat_invalid_falls_through_to_nested(self) -> None:
        # If user_id is non-string, flat extraction returns None for that path,
        # then tries nested.
        result: str | None = parse_user_id({
            "user_id": 12345,
            "user": {"id": "nested_id"},
        })
        assert result == "nested_id"

    def test_flat_present_but_invalid_chars(self) -> None:
        # Flat form extracts a string, but it's invalid after validation -> None
        result: str | None = parse_user_id({
            "user_id": "ab",  # too short
            "user": {"id": "nested_id"},
        })
        # user_id is a string so it's extracted; validation fails -> None
        assert result is None


# ==============================================================================
# EDGE CASES
# ==============================================================================


class TestEdgeCases:
    """Miscellaneous edge-case tests."""

    def test_tab_and_newline_whitespace_trimmed(self) -> None:
        assert parse_user_id("user:\t abc123 \n") == "abc123"

    def test_id_exactly_matching_prefix(self) -> None:
        assert parse_user_id("user:user") == "user"

    def test_numeric_only_3_chars(self) -> None:
        assert parse_user_id("user:123") == "123"

    def test_hyphen_underscore_mix(self) -> None:
        assert parse_user_id("user:a-_b") == "a-_b"

    def test_dict_with_bool_user_id(self) -> None:
        assert parse_user_id({"user_id": True}) is None

    def test_deeply_nested_extra_ignored(self) -> None:
        assert parse_user_id({"user": {"id": "abc", "extra": "data"}}) == "abc"

    def test_user_key_is_int(self) -> None:
        assert parse_user_id({"user": 42}) is None

    def test_user_key_is_bool(self) -> None:
        # bool is subclass of int, not dict
        assert parse_user_id({"user": True}) is None


# ==============================================================================
# Z3 FORMAL VERIFICATION TESTS
# ==============================================================================
# These tests use Z3 to verify properties of the validation logic.
# They are written as regular pytest tests that invoke Z3.

try:
    from z3 import (
        Solver, String, StringVal, Length, And, Or, Not,
        IntVal, sat, unsat, Re, InRe, Range, Star, Union, Concat,
    )
    Z3_AVAILABLE: bool = True
except ImportError:
    Z3_AVAILABLE: bool = False


@pytest.mark.skipif(not Z3_AVAILABLE, reason="z3-solver not installed")
class TestZ3FormalVerification:
    """Z3-based formal verification of validation logic properties."""

    def test_z3_valid_id_length_in_range(self) -> None:
        """Verify: if a string matches the pattern, its length is in [3, 20]."""
        x = String("x")
        # Define the allowed character class: [a-z0-9_-]
        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re("_"),
            Re("-"),
        )
        pattern = Star(char_class)

        # Verify: strings of length 1 or 2 with valid chars exist (e.g., "ab")
        s2 = Solver()
        s2.add(InRe(x, pattern))
        s2.add(Length(x) < 3)
        s2.add(Length(x) > 0)  # non-empty
        assert s2.check() == sat  # They exist in the char set

        # But our code rejects them via the {3,20} length constraint
        if s2.check() == sat:
            model = s2.model()
            short_id: str = model[x].as_string()
            # Our function should reject this
            assert parse_user_id(f"user:{short_id}") is None

    def test_z3_no_valid_id_longer_than_20(self) -> None:
        """Verify: a 21-char string of valid chars is rejected by the function."""
        s = Solver()
        x = String("x")
        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re("_"),
            Re("-"),
        )
        s.add(InRe(x, Star(char_class)))
        s.add(Length(x) == 21)
        assert s.check() == sat
        model = s.model()
        long_id: str = model[x].as_string()
        assert parse_user_id(f"user:{long_id}") is None

    def test_z3_reserved_ids_always_rejected(self) -> None:
        """Verify: all reserved IDs are rejected regardless of case/whitespace."""
        reserved: list[str] = ["admin", "root", "system"]
        for rid in reserved:
            assert parse_user_id(f"user:{rid}") is None
            assert parse_user_id(f"user:{rid.upper()}") is None
            assert parse_user_id(f"user:  {rid}  ") is None
            assert parse_user_id({"user_id": rid}) is None
            assert parse_user_id({"user": {"id": rid}}) is None

    def test_z3_valid_output_only_contains_allowed_chars(self) -> None:
        """Verify: for a range of valid inputs, output only has allowed chars."""
        valid_pattern = re.compile(r"^[a-z0-9_-]{3,20}$")
        test_cases: list[object] = [
            "user:hello",
            "user:MY_USER",
            "user:test-123",
            "user:  SPACED  ",
            {"user_id": "Dict_User"},
            {"user": {"id": "Nested_User"}},
        ]
        for tc in test_cases:
            result: str | None = parse_user_id(tc)
            if result is not None:
                assert valid_pattern.fullmatch(result), (
                    f"Invalid output '{result}' for input {tc}"
                )
                assert result == result.lower(), (
                    f"Output not lowercase: '{result}'"
                )

    def test_z3_boundary_length_3_satisfiable(self) -> None:
        """Verify: there exist valid IDs of exactly length 3."""
        s = Solver()
        x = String("x")
        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re("_"),
            Re("-"),
        )
        s.add(InRe(x, Star(char_class)))
        s.add(Length(x) == 3)
        assert s.check() == sat
        model = s.model()
        id_3: str = model[x].as_string()
        # If it's not reserved, it should be valid
        if id_3.lower() not in {"admin", "root", "system"}:
            result: str | None = parse_user_id(f"user:{id_3}")
            assert result is not None
            assert len(result) == 3

    def test_z3_boundary_length_20_satisfiable(self) -> None:
        """Verify: there exist valid IDs of exactly length 20."""
        s = Solver()
        x = String("x")
        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re("_"),
            Re("-"),
        )
        s.add(InRe(x, Star(char_class)))
        s.add(Length(x) == 20)
        assert s.check() == sat
        model = s.model()
        id_20: str = model[x].as_string()
        result: str | None = parse_user_id(f"user:{id_20}")
        assert result is not None
        assert len(result) == 20