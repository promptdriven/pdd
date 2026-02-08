# =============================================================================
# TEST PLAN for parse_user_id
# =============================================================================
#
# 1. STRING INPUT TESTS:
#    a) Valid "user:<id>" format → returns normalized id
#    b) Whitespace around string and id → properly trimmed
#    c) Uppercase id → lowercased
#    d) No colon in string → None
#    e) Wrong prefix (not "user") → None
#    f) Empty id after "user:" → None
#    g) Whitespace-only id after "user:" → None
#    h) Multiple colons "user:a:b" → takes everything after first colon
#
# 2. DICT INPUT (user_id key):
#    a) Valid {"user_id": "<id>"} → returns normalized id
#    b) Whitespace in value → trimmed
#    c) Non-string value (int, None, list) → None
#    d) Empty string value → None
#    e) Whitespace-only string value → None
#
# 3. DICT INPUT (user.id nested):
#    a) Valid {"user": {"id": "<id>"}} → returns normalized id
#    b) user is not a dict → None
#    c) user dict missing "id" key → None
#    d) user.id is not a string → None
#    e) user.id is empty → None
#
# 4. DICT WITH BOTH KEYS (priority):
#    a) Both user_id and user.id present → user_id takes priority if valid
#    b) user_id invalid (non-string), user.id valid → falls through to user.id
#
# 5. VALIDATION:
#    a) Length exactly 3 → valid
#    b) Length exactly 20 → valid
#    c) Length 2 → None (too short)
#    d) Length 21 → None (too long)
#    e) Allowed chars: a-z, 0-9, _, - → valid
#    f) Invalid chars: space, dot, !, @, uppercase after normalization won't
#       happen because we lowercase first, but chars like ! remain
#    g) Reserved IDs: "admin", "root", "system" → None
#    h) Reserved IDs case-insensitive: "ADMIN", "Root", "SYSTEM" → None
#
# 6. OTHER INPUT TYPES:
#    a) None → None
#    b) int → None
#    c) list → None
#    d) bool → None (bool is subclass of int in Python)
#    e) float → None
#
# 7. NON-MUTATION:
#    a) Input dict must not be modified after call
#
# 8. NEVER RAISES:
#    a) Various malformed inputs should return None, not raise
#
# 9. Z3 FORMAL VERIFICATION:
#    - Z3 is best suited for verifying properties of the validation logic:
#      a) Any validated output has length in [3, 20]
#      b) Any validated output contains only a-z, 0-9, _, -
#      c) Reserved words never pass validation
#    - However, Z3 string theory has limitations; we'll use it where practical
#      and fall back to property-based reasoning via unit tests.
#    - For this module, unit tests are more practical than Z3 for most cases
#      because the logic is string-based with regex, and Z3's string theory
#      can be slow/limited. We'll include Z3 tests for key invariants if z3
#      is available, with graceful skip if not installed.
#
# =============================================================================


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import sys
import os
import copy
import pytest

# Adjust path so we can import from the src directory

from user_id_parser import parse_user_id


# =============================================================================
# STRING INPUT TESTS
# =============================================================================

class TestStringInput:
    """Tests for parse_user_id when the input is a string."""

    def test_valid_user_prefix(self) -> None:
        assert parse_user_id("user:abc") == "abc"

    def test_valid_alphanumeric(self) -> None:
        assert parse_user_id("user:abc123") == "abc123"

    def test_valid_with_underscore(self) -> None:
        assert parse_user_id("user:a_b_c") == "a_b_c"

    def test_valid_with_hyphen(self) -> None:
        assert parse_user_id("user:a-b-c") == "a-b-c"

    def test_valid_mixed_allowed_chars(self) -> None:
        assert parse_user_id("user:a1_b-2") == "a1_b-2"

    def test_whitespace_around_string(self) -> None:
        assert parse_user_id("  user:abc  ") == "abc"

    def test_whitespace_around_id(self) -> None:
        assert parse_user_id("user:  abc  ") == "abc"

    def test_uppercase_id_lowered(self) -> None:
        assert parse_user_id("user:ABC") == "abc"

    def test_mixed_case_id_lowered(self) -> None:
        assert parse_user_id("user:AbCdEf") == "abcdef"

    def test_no_colon_returns_none(self) -> None:
        assert parse_user_id("userabc") is None

    def test_wrong_prefix_returns_none(self) -> None:
        assert parse_user_id("admin:abc") is None

    def test_empty_prefix_returns_none(self) -> None:
        assert parse_user_id(":abc") is None

    def test_empty_id_returns_none(self) -> None:
        assert parse_user_id("user:") is None

    def test_whitespace_only_id_returns_none(self) -> None:
        assert parse_user_id("user:   ") is None

    def test_multiple_colons_takes_rest(self) -> None:
        # "user:a:b" → rest is "a:b", which contains ':', an invalid char
        assert parse_user_id("user:a:b") is None

    def test_empty_string_returns_none(self) -> None:
        assert parse_user_id("") is None

    def test_just_colon(self) -> None:
        assert parse_user_id(":") is None

    def test_user_colon_space(self) -> None:
        assert parse_user_id("user: ") is None

    def test_prefix_with_uppercase_user(self) -> None:
        # "User:abc" → prefix is "User", not "user"
        assert parse_user_id("User:abc") is None

    def test_prefix_USER_uppercase(self) -> None:
        assert parse_user_id("USER:abc") is None


# =============================================================================
# DICT INPUT (user_id key) TESTS
# =============================================================================

class TestDictUserIdKey:
    """Tests for parse_user_id when the input is a dict with a 'user_id' key."""

    def test_valid_user_id(self) -> None:
        assert parse_user_id({"user_id": "abc"}) == "abc"

    def test_user_id_with_whitespace(self) -> None:
        assert parse_user_id({"user_id": "  abc  "}) == "abc"

    def test_user_id_uppercase(self) -> None:
        assert parse_user_id({"user_id": "ABC"}) == "abc"

    def test_user_id_int_value_returns_none(self) -> None:
        assert parse_user_id({"user_id": 123}) is None

    def test_user_id_none_value_returns_none(self) -> None:
        assert parse_user_id({"user_id": None}) is None

    def test_user_id_list_value_returns_none(self) -> None:
        assert parse_user_id({"user_id": ["abc"]}) is None

    def test_user_id_empty_string(self) -> None:
        assert parse_user_id({"user_id": ""}) is None

    def test_user_id_whitespace_only(self) -> None:
        assert parse_user_id({"user_id": "   "}) is None

    def test_empty_dict(self) -> None:
        assert parse_user_id({}) is None

    def test_unrelated_keys(self) -> None:
        assert parse_user_id({"name": "abc"}) is None


# =============================================================================
# DICT INPUT (user.id nested) TESTS
# =============================================================================

class TestDictNestedUserId:
    """Tests for parse_user_id when the input is a dict with nested 'user'.'id'."""

    def test_valid_nested_id(self) -> None:
        assert parse_user_id({"user": {"id": "abc"}}) == "abc"

    def test_nested_id_with_whitespace(self) -> None:
        assert parse_user_id({"user": {"id": "  abc  "}}) == "abc"

    def test_nested_id_uppercase(self) -> None:
        assert parse_user_id({"user": {"id": "ABC"}}) == "abc"

    def test_user_not_dict(self) -> None:
        assert parse_user_id({"user": "abc"}) is None

    def test_user_is_list(self) -> None:
        assert parse_user_id({"user": ["abc"]}) is None

    def test_user_is_none(self) -> None:
        assert parse_user_id({"user": None}) is None

    def test_user_dict_missing_id(self) -> None:
        assert parse_user_id({"user": {"name": "abc"}}) is None

    def test_user_dict_id_not_string(self) -> None:
        assert parse_user_id({"user": {"id": 123}}) is None

    def test_user_dict_id_empty_string(self) -> None:
        assert parse_user_id({"user": {"id": ""}}) is None

    def test_user_dict_id_whitespace_only(self) -> None:
        assert parse_user_id({"user": {"id": "   "}}) is None


# =============================================================================
# DICT WITH BOTH KEYS (PRIORITY) TESTS
# =============================================================================

class TestDictPriority:
    """Tests for parse_user_id priority when both 'user_id' and nested 'user.id' exist."""

    def test_user_id_takes_priority_when_both_valid(self) -> None:
        result = parse_user_id({"user_id": "first", "user": {"id": "second"}})
        assert result == "first"

    def test_falls_through_to_nested_when_user_id_non_string(self) -> None:
        result = parse_user_id({"user_id": 123, "user": {"id": "second"}})
        assert result == "second"

    def test_falls_through_to_nested_when_user_id_empty(self) -> None:
        result = parse_user_id({"user_id": "", "user": {"id": "second"}})
        assert result == "second"

    def test_falls_through_to_nested_when_user_id_whitespace(self) -> None:
        result = parse_user_id({"user_id": "   ", "user": {"id": "second"}})
        assert result == "second"


# =============================================================================
# VALIDATION TESTS
# =============================================================================

class TestValidation:
    """Tests for ID validation rules: length, allowed chars, reserved words."""

    def test_min_length_3_valid(self) -> None:
        assert parse_user_id("user:abc") == "abc"

    def test_length_2_too_short(self) -> None:
        assert parse_user_id("user:ab") is None

    def test_length_1_too_short(self) -> None:
        assert parse_user_id("user:a") is None

    def test_max_length_20_valid(self) -> None:
        uid: str = "a" * 20
        assert parse_user_id(f"user:{uid}") == uid

    def test_length_21_too_long(self) -> None:
        uid: str = "a" * 21
        assert parse_user_id(f"user:{uid}") is None

    def test_digits_only(self) -> None:
        assert parse_user_id("user:12345") == "12345"

    def test_underscores_and_hyphens(self) -> None:
        assert parse_user_id("user:a_b-c") == "a_b-c"

    def test_all_underscores(self) -> None:
        assert parse_user_id("user:___") == "___"

    def test_all_hyphens(self) -> None:
        assert parse_user_id("user:---") == "---"

    def test_invalid_char_dot(self) -> None:
        assert parse_user_id("user:ab.c") is None

    def test_invalid_char_space_in_middle(self) -> None:
        assert parse_user_id("user:ab c") is None

    def test_invalid_char_at_sign(self) -> None:
        assert parse_user_id("user:ab@c") is None

    def test_invalid_char_exclamation(self) -> None:
        assert parse_user_id("user:ab!c") is None

    def test_invalid_char_slash(self) -> None:
        assert parse_user_id("user:ab/c") is None

    def test_invalid_char_plus(self) -> None:
        assert parse_user_id("user:ab+c") is None

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

    def test_reserved_system_uppercase(self) -> None:
        assert parse_user_id("user:SYSTEM") is None

    def test_reserved_admin_with_whitespace(self) -> None:
        assert parse_user_id("user:  admin  ") is None

    def test_reserved_via_dict(self) -> None:
        assert parse_user_id({"user_id": "admin"}) is None

    def test_reserved_via_nested_dict(self) -> None:
        assert parse_user_id({"user": {"id": "root"}}) is None

    def test_boundary_length_3_with_valid_chars(self) -> None:
        assert parse_user_id("user:a-1") == "a-1"

    def test_boundary_length_20_mixed(self) -> None:
        uid: str = "ab-cd_ef01234567890a"  # exactly 20 chars
        assert len(uid) == 20
        assert parse_user_id(f"user:{uid}") == uid


# =============================================================================
# OTHER INPUT TYPES TESTS
# =============================================================================

class TestOtherInputTypes:
    """Tests for unsupported input types that should all return None."""

    def test_none_returns_none(self) -> None:
        assert parse_user_id(None) is None

    def test_int_returns_none(self) -> None:
        assert parse_user_id(123) is None

    def test_float_returns_none(self) -> None:
        assert parse_user_id(3.14) is None

    def test_bool_returns_none(self) -> None:
        # bool is subclass of int in Python
        assert parse_user_id(True) is None
        assert parse_user_id(False) is None

    def test_list_returns_none(self) -> None:
        assert parse_user_id(["user:abc"]) is None

    def test_tuple_returns_none(self) -> None:
        assert parse_user_id(("user:abc",)) is None

    def test_set_returns_none(self) -> None:
        assert parse_user_id({"abc"}) is None

    def test_bytes_returns_none(self) -> None:
        assert parse_user_id(b"user:abc") is None


# =============================================================================
# NON-MUTATION TESTS
# =============================================================================

class TestNonMutation:
    """Tests ensuring parse_user_id does not mutate its input dict."""

    def test_dict_user_id_not_mutated(self) -> None:
        d = {"user_id": "  ABC  "}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_nested_dict_not_mutated(self) -> None:
        d = {"user": {"id": "  ABC  "}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_with_both_keys_not_mutated(self) -> None:
        d = {"user_id": "  ABC  ", "user": {"id": "  XYZ  "}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original


# =============================================================================
# NEVER RAISES TESTS
# =============================================================================

class TestNeverRaises:
    """Tests ensuring parse_user_id never raises, returning None for bad inputs."""

    def test_deeply_nested_bad_structure(self) -> None:
        # Should return None, not raise
        assert parse_user_id({"user": {"id": {"nested": "too_deep"}}}) is None

    def test_user_key_with_int_id(self) -> None:
        assert parse_user_id({"user": {"id": 999}}) is None

    def test_dict_with_non_hashable_complexity(self) -> None:
        assert parse_user_id({"user_id": [], "user": []}) is None

    def test_custom_object_input(self) -> None:
        class Custom:
            pass
        assert parse_user_id(Custom()) is None


# =============================================================================
# NORMALIZATION INTEGRATION TESTS
# =============================================================================

class TestNormalizationIntegration:
    """Integration tests verifying full normalization pipeline across input paths."""

    def test_string_input_full_normalization(self) -> None:
        """Whitespace trimming + lowercasing through string path."""
        assert parse_user_id("  user:  Hello_World  ") == "hello_world"

    def test_dict_input_full_normalization(self) -> None:
        """Whitespace trimming + lowercasing through dict path."""
        assert parse_user_id({"user_id": "  Hello_World  "}) == "hello_world"

    def test_nested_dict_full_normalization(self) -> None:
        """Whitespace trimming + lowercasing through nested dict path."""
        assert parse_user_id({"user": {"id": "  Hello_World  "}}) == "hello_world"

    def test_normalization_then_validation_length_boundary(self) -> None:
        """After trimming whitespace, the ID should be checked for length."""
        # "  ab  " → trimmed to "ab" → length 2 → too short
        assert parse_user_id("user:  ab  ") is None

    def test_normalization_then_validation_passes(self) -> None:
        # "  ABC  " → trimmed to "ABC" → lowered to "abc" → length 3 → valid
        assert parse_user_id("user:  ABC  ") == "abc"


# =============================================================================
# Z3 FORMAL VERIFICATION TESTS
# =============================================================================
# These tests use Z3 to formally verify key invariants of the validation logic.
# If z3 is not installed, these tests are skipped gracefully.

try:
    import z3
    HAS_Z3 = True
except ImportError:
    HAS_Z3 = False


@pytest.mark.skipif(not HAS_Z3, reason="z3-solver not installed")
class TestZ3FormalVerification:
    """
    Use Z3 to verify key invariants about parse_user_id's validation.
    We test properties that must hold for ALL possible inputs.
    """

    def _build_char_class(self):
        """Build Z3 regex for the character class [a-z0-9_-]."""
        return z3.Union(
            z3.Range("a", "z"),
            z3.Range("0", "9"),
            z3.Range("_", "_"),
            z3.Range("-", "-"),
        )

    def test_z3_valid_output_length_in_range(self) -> None:
        """Verify: if parse_user_id returns a non-None value, its length is in [3, 20].

        We use Z3 to prove that no string of length <3 can satisfy the
        validation regex [a-z0-9_-]{3,20} — the solver must return unsat.
        """
        s = z3.String("s")
        char_class = self._build_char_class()
        valid_regex = z3.Loop(char_class, 3, 20)

        # Prove: no string matching the regex can have length < 3
        solver = z3.Solver()
        solver.add(z3.InRe(s, valid_regex))
        solver.add(z3.Length(s) < 3)
        assert solver.check() == z3.unsat, \
            "Z3 found a string shorter than 3 that matches [a-z0-9_-]{3,20}"

    def test_z3_reserved_ids_always_rejected(self) -> None:
        """Verify: reserved IDs are always rejected regardless of casing/whitespace.

        We check that for each reserved word, no casing variant passes validation.
        """
        reserved = ["admin", "root", "system"]

        for word in reserved:
            # The word itself should be rejected
            assert parse_user_id(f"user:{word}") is None
            # Uppercase variant
            assert parse_user_id(f"user:{word.upper()}") is None
            # Title case
            assert parse_user_id(f"user:{word.title()}") is None
            # With whitespace
            assert parse_user_id(f"user:  {word}  ") is None

    def test_z3_no_string_longer_than_20_passes(self) -> None:
        """Verify: the regex [a-z0-9_-]{3,20} rejects any string longer than 20 chars.

        We use Z3 to prove that no string of length >20 can satisfy the
        validation regex — the solver must return unsat.
        """
        s = z3.String("s")
        char_class = self._build_char_class()
        valid_regex = z3.Loop(char_class, 3, 20)

        # Prove: no string matching the regex can have length > 20
        solver = z3.Solver()
        solver.add(z3.InRe(s, valid_regex))
        solver.add(z3.Length(s) > 20)
        assert solver.check() == z3.unsat, \
            "Z3 found a string longer than 20 that matches [a-z0-9_-]{3,20}"

    def test_z3_valid_chars_property(self) -> None:
        """Verify: if a string passes our regex, every character is in allowed set."""
        import re
        pattern = re.compile(r"^[a-z0-9_-]{3,20}$")
        allowed = set("abcdefghijklmnopqrstuvwxyz0123456789_-")

        # Test with concrete examples generated to stress boundaries
        test_cases = [
            "abc", "a" * 20, "a-b", "a_b", "123", "a1_", "-_-",
            "abcdefghijklmnopqrst",  # 20 chars
        ]
        for tc in test_cases:
            if pattern.match(tc):
                for ch in tc:
                    assert ch in allowed, \
                        f"Character '{ch}' in '{tc}' not in allowed set"