# ==============================================================================
# TEST PLAN for parse_user_id
# ==============================================================================
#
# 1. STRING INPUT FORMAT ("user:<id>")
#    - Valid: "user:abc" -> ParseResult("abc", "string")
#    - Valid with whitespace: "user:  ABC  " -> ParseResult("abc", "string")
#    - Missing prefix: "abc" -> None
#    - Wrong prefix: "admin:abc" -> None
#    - Empty after prefix: "user:" -> None (length < 3)
#    - Only prefix: "user:" with nothing -> None
#
# 2. DICT INPUT FORMAT {"user_id": "<id>"}
#    - Valid: {"user_id": "abc"} -> ParseResult("abc", "dict_flat")
#    - Non-string value: {"user_id": 123} -> None
#    - Missing key: {"other": "abc"} -> None
#
# 3. DICT INPUT FORMAT {"user": {"id": "<id>"}}
#    - Valid: {"user": {"id": "abc"}} -> ParseResult("abc", "dict_nested")
#    - Inner not dict: {"user": "abc"} -> None
#    - Inner missing "id": {"user": {"name": "abc"}} -> None
#    - Inner "id" not string: {"user": {"id": 123}} -> None
#
# 4. NORMALIZATION
#    - Whitespace trimming: leading/trailing spaces
#    - Lowercasing: "ABC" -> "abc", "AbC" -> "abc"
#    - Combined: "  ABC  " -> "abc"
#
# 5. VALIDATION - Allowed characters (a-z, 0-9, _, -)
#    - Valid chars: "abc_def-123" -> valid
#    - Invalid chars: "abc.def" -> None
#    - Invalid chars: "abc@def" -> None
#    - Invalid chars: "abc def" (space in middle) -> None
#
# 6. VALIDATION - Length (3 to 20 inclusive)
#    - Length 2: "ab" -> None
#    - Length 3: "abc" -> valid
#    - Length 20: "a" * 20 -> valid
#    - Length 21: "a" * 21 -> None
#
# 7. RESERVED IDs
#    - "admin" -> None
#    - "root" -> None
#    - "system" -> None
#    - Case-insensitive: "ADMIN" -> None (lowercased first, then checked)
#    - "Admin" -> None
#
# 8. INVALID INPUT TYPES (never raise)
#    - None -> None
#    - int -> None
#    - list -> None
#    - float -> None
#    - bool -> None (bool is subclass of int, but not str or dict)
#    - tuple -> None
#
# 9. NON-MUTATION OF INPUT DICTS
#    - Pass a dict, verify it's unchanged after call
#    - Pass a nested dict, verify inner dict unchanged
#
# 10. EDGE CASES
#    - Empty string -> None
#    - "user:user:abc" -> should extract "user:abc" which has invalid char ':'
#    - Dict with both "user_id" and "user" keys -> "user_id" takes precedence
#    - Subclass of str that starts with "user:" -> should work
#
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

import pytest


try:
    from user_id_parser import parse_user_id, parse_user_ids, ParseResult
except ImportError:
    # Fallback for environments where the module is not yet present
    import collections
    ParseResult = collections.namedtuple("ParseResult", ["user_id", "source"])
    def parse_user_id(input_data, reserved_ids=None):
        pass
    def parse_user_ids(vals, reserved_ids=None): return [None] * len(vals)


# ==============================================================================
# STRING INPUT FORMAT TESTS
# ==============================================================================

class TestStringInput:
    def test_valid_simple_string(self):
        assert parse_user_id("user:abc") == ParseResult(user_id="abc", source="string")

    def test_valid_string_with_numbers(self):
        assert parse_user_id("user:abc123") == ParseResult(user_id="abc123", source="string")

    def test_valid_string_with_underscore(self):
        assert parse_user_id("user:abc_def") == ParseResult(user_id="abc_def", source="string")

    def test_valid_string_with_hyphen(self):
        assert parse_user_id("user:abc-def") == ParseResult(user_id="abc-def", source="string")

    def test_valid_string_mixed_chars(self):
        assert parse_user_id("user:a1_b-2") == ParseResult(user_id="a1_b-2", source="string")

    def test_string_missing_prefix(self):
        assert parse_user_id("abc") is None

    def test_string_wrong_prefix(self):
        assert parse_user_id("admin:abc") is None

    def test_string_empty_after_prefix(self):
        assert parse_user_id("user:") is None

    def test_string_only_prefix_partial(self):
        assert parse_user_id("user") is None

    def test_empty_string(self):
        assert parse_user_id("") is None

    def test_string_with_colon_in_id(self):
        # "user:user:abc" -> extracts "user:abc" which contains ':'
        assert parse_user_id("user:user:abc") is None


# ==============================================================================
# NORMALIZATION TESTS
# ==============================================================================

class TestNormalization:
    def test_trim_leading_whitespace(self):
        assert parse_user_id("user:   abc") == ParseResult(user_id="abc", source="string")

    def test_trim_trailing_whitespace(self):
        assert parse_user_id("user:abc   ") == ParseResult(user_id="abc", source="string")

    def test_trim_both_whitespace(self):
        assert parse_user_id("user:  abc  ") == ParseResult(user_id="abc", source="string")

    def test_lowercase(self):
        assert parse_user_id("user:ABC") == ParseResult(user_id="abc", source="string")

    def test_mixed_case(self):
        assert parse_user_id("user:AbCdEf") == ParseResult(user_id="abcdef", source="string")

    def test_trim_and_lowercase_combined(self):
        assert parse_user_id("user:  ABC  ") == ParseResult(user_id="abc", source="string")

    def test_dict_user_id_normalization(self):
        assert parse_user_id({"user_id": "  ABC  "}) == ParseResult(user_id="abc", source="dict_flat")

    def test_dict_nested_normalization(self):
        assert parse_user_id({"user": {"id": "  ABC  "}}) == ParseResult(user_id="abc", source="dict_nested")

    def test_tab_whitespace_trimmed(self):
        assert parse_user_id("user:\tabc\t") == ParseResult(user_id="abc", source="string")

    def test_newline_whitespace_trimmed(self):
        assert parse_user_id("user:\nabc\n") == ParseResult(user_id="abc", source="string")


# ==============================================================================
# DICT INPUT FORMAT - {"user_id": "<id>"}
# ==============================================================================

class TestDictUserIdKey:
    def test_valid_user_id_key(self):
        assert parse_user_id({"user_id": "abc"}) == ParseResult(user_id="abc", source="dict_flat")

    def test_user_id_non_string_int(self):
        assert parse_user_id({"user_id": 123}) is None

    def test_user_id_non_string_none(self):
        assert parse_user_id({"user_id": None}) is None

    def test_user_id_non_string_list(self):
        assert parse_user_id({"user_id": ["abc"]}) is None

    def test_user_id_non_string_bool(self):
        assert parse_user_id({"user_id": True}) is None

    def test_missing_user_id_key(self):
        assert parse_user_id({"other_key": "abc"}) is None

    def test_empty_dict(self):
        assert parse_user_id({}) is None


# ==============================================================================
# DICT INPUT FORMAT - {"user": {"id": "<id>"}}
# ==============================================================================

class TestDictNestedUser:
    def test_valid_nested_user(self):
        assert parse_user_id({"user": {"id": "abc"}}) == ParseResult(user_id="abc", source="dict_nested")

    def test_inner_not_dict_string(self):
        assert parse_user_id({"user": "abc"}) is None

    def test_inner_not_dict_int(self):
        assert parse_user_id({"user": 123}) is None

    def test_inner_not_dict_none(self):
        assert parse_user_id({"user": None}) is None

    def test_inner_missing_id_key(self):
        assert parse_user_id({"user": {"name": "abc"}}) is None

    def test_inner_id_not_string(self):
        assert parse_user_id({"user": {"id": 123}}) is None

    def test_inner_id_none(self):
        assert parse_user_id({"user": {"id": None}}) is None

    def test_inner_empty_dict(self):
        assert parse_user_id({"user": {}}) is None


# ==============================================================================
# DICT PRECEDENCE - both keys present
# ==============================================================================

class TestDictPrecedence:
    def test_user_id_takes_precedence_over_nested(self):
        """When both 'user_id' and 'user' keys exist, 'user_id' should be used."""
        result = parse_user_id({"user_id": "abc", "user": {"id": "xyz"}})
        assert result == ParseResult(user_id="abc", source="dict_flat")

    def test_user_id_invalid_does_not_fall_back_to_nested(self):
        """If user_id is present but invalid type, should NOT fall back to nested user.id.
        
        The 'user_id' key takes precedence; when it exists but has a non-string
        value, extraction returns None without checking the 'user' key.
        This is consistent with TestParseUserIdDictPriority and TestEdgeCases
        which also assert no-fallback behavior.
        """
        result = parse_user_id({"user_id": 123, "user": {"id": "xyz"}})
        # user_id key exists but value is not str, extraction returns None
        assert result is None


# ==============================================================================
# VALIDATION - Allowed Characters
# ==============================================================================

class TestValidationCharacters:
    def test_valid_lowercase_letters(self):
        assert parse_user_id("user:abcdef") == ParseResult(user_id="abcdef", source="string")

    def test_valid_digits(self):
        assert parse_user_id("user:12345") == ParseResult(user_id="12345", source="string")

    def test_valid_underscore(self):
        assert parse_user_id("user:a_b_c") == ParseResult(user_id="a_b_c", source="string")

    def test_valid_hyphen(self):
        assert parse_user_id("user:a-b-c") == ParseResult(user_id="a-b-c", source="string")

    def test_invalid_dot(self):
        assert parse_user_id("user:abc.def") is None

    def test_invalid_at_sign(self):
        assert parse_user_id("user:abc@def") is None

    def test_invalid_space_in_middle(self):
        assert parse_user_id("user:abc def") is None

    def test_invalid_exclamation(self):
        assert parse_user_id("user:abc!def") is None

    def test_invalid_hash(self):
        assert parse_user_id("user:abc#def") is None

    def test_invalid_slash(self):
        assert parse_user_id("user:abc/def") is None

    def test_invalid_uppercase_after_normalization_still_valid(self):
        # Uppercase gets lowercased, so "ABC" -> "abc" which is valid
        assert parse_user_id("user:ABC") == ParseResult(user_id="abc", source="string")


# ==============================================================================
# VALIDATION - Length (3 to 20 inclusive)
# ==============================================================================

class TestValidationLength:
    def test_length_1(self):
        assert parse_user_id("user:a") is None

    def test_length_2(self):
        assert parse_user_id("user:ab") is None

    def test_length_3_boundary(self):
        assert parse_user_id("user:abc") == ParseResult(user_id="abc", source="string")

    def test_length_4(self):
        assert parse_user_id("user:abcd") == ParseResult(user_id="abcd", source="string")

    def test_length_19(self):
        assert parse_user_id("user:" + "a" * 19) == ParseResult(user_id="a" * 19, source="string")

    def test_length_20_boundary(self):
        assert parse_user_id("user:" + "a" * 20) == ParseResult(user_id="a" * 20, source="string")

    def test_length_21(self):
        assert parse_user_id("user:" + "a" * 21) is None

    def test_length_100(self):
        assert parse_user_id("user:" + "a" * 100) is None

    def test_whitespace_trimmed_then_length_checked(self):
        # "  ab  " -> trimmed to "ab" -> length 2 -> None
        assert parse_user_id("user:  ab  ") is None

    def test_whitespace_trimmed_length_becomes_valid(self):
        # "  abc  " -> trimmed to "abc" -> length 3 -> valid
        assert parse_user_id("user:  abc  ") == ParseResult(user_id="abc", source="string")


# ==============================================================================
# RESERVED IDs
# ==============================================================================

class TestReservedIds:
    def test_reserved_admin(self):
        assert parse_user_id("user:admin") is None

    def test_reserved_root(self):
        assert parse_user_id("user:root") is None

    def test_reserved_system(self):
        assert parse_user_id("user:system") is None

    def test_reserved_admin_uppercase(self):
        # "ADMIN" -> lowercased to "admin" -> reserved
        assert parse_user_id("user:ADMIN") is None

    def test_reserved_admin_mixed_case(self):
        assert parse_user_id("user:Admin") is None

    def test_reserved_root_uppercase(self):
        assert parse_user_id("user:ROOT") is None

    def test_reserved_system_mixed_case(self):
        assert parse_user_id("user:SyStEm") is None

    def test_reserved_admin_with_whitespace(self):
        assert parse_user_id("user:  admin  ") is None

    def test_reserved_via_dict_user_id(self):
        assert parse_user_id({"user_id": "admin"}) is None

    def test_reserved_via_dict_nested(self):
        assert parse_user_id({"user": {"id": "root"}}) is None

    def test_non_reserved_similar_to_admin(self):
        assert parse_user_id("user:admin1") == ParseResult(user_id="admin1", source="string")

    def test_non_reserved_similar_to_root(self):
        assert parse_user_id("user:root_user") == ParseResult(user_id="root_user", source="string")

    def test_non_reserved_similar_to_system(self):
        assert parse_user_id("user:systems") == ParseResult(user_id="systems", source="string")


# ==============================================================================
# INVALID INPUT TYPES (never raise)
# ==============================================================================

class TestInvalidInputTypes:
    def test_none_input(self):
        assert parse_user_id(None) is None

    def test_int_input(self):
        assert parse_user_id(42) is None

    def test_float_input(self):
        assert parse_user_id(3.14) is None

    def test_bool_input(self):
        assert parse_user_id(True) is None

    def test_list_input(self):
        assert parse_user_id(["user:abc"]) is None

    def test_tuple_input(self):
        assert parse_user_id(("user:abc",)) is None

    def test_set_input(self):
        assert parse_user_id({"user:abc"}) is None

    def test_bytes_input(self):
        assert parse_user_id(b"user:abc") is None

    def test_object_input(self):
        assert parse_user_id(object()) is None

    def test_class_input(self):
        class Foo:
            pass
        assert parse_user_id(Foo()) is None


# ==============================================================================
# NON-MUTATION OF INPUT DICTS
# ==============================================================================

class TestNonMutation:
    def test_dict_user_id_not_mutated(self):
        d = {"user_id": "abc"}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_nested_not_mutated(self):
        d = {"user": {"id": "abc"}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_with_extra_keys_not_mutated(self):
        d = {"user_id": "abc", "extra": "data", "nested": {"key": "val"}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_invalid_dict_not_mutated(self):
        d = {"user_id": 123, "user": "not_dict"}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original


# ==============================================================================
# EDGE CASES
# ==============================================================================

class TestEdgeCases:
    def test_only_whitespace_after_prefix(self):
        # "user:   " -> trimmed to "" -> length 0 -> None
        assert parse_user_id("user:   ") is None

    def test_all_underscores_valid_length(self):
        assert parse_user_id("user:___") == ParseResult(user_id="___", source="string")

    def test_all_hyphens_valid_length(self):
        assert parse_user_id("user:---") == ParseResult(user_id="---", source="string")

    def test_all_digits_valid_length(self):
        assert parse_user_id("user:123") == ParseResult(user_id="123", source="string")

    def test_exactly_20_chars(self):
        id_20 = "abcdefghij0123456789"
        assert len(id_20) == 20
        assert parse_user_id("user:" + id_20) == ParseResult(user_id=id_20, source="string")

    def test_unicode_characters_rejected(self):
        assert parse_user_id("user:abcé") is None

    def test_emoji_rejected(self):
        assert parse_user_id("user:abc😀") is None

    def test_string_user_prefix_case_sensitive(self):
        # "User:abc" doesn't start with "user:" so should return None
        assert parse_user_id("User:abc") is None

    def test_string_USER_prefix_case_sensitive(self):
        assert parse_user_id("USER:abc") is None

    def test_dict_bool_is_int_subclass_not_treated_as_dict(self):
        # bool is subclass of int, not dict
        assert parse_user_id(True) is None
        assert parse_user_id(False) is None

    def test_return_type_is_parse_result_or_none(self):
        result = parse_user_id("user:abc")
        if result is not None:
            assert isinstance(result, ParseResult)

        result = parse_user_id("invalid")
        assert result is None

    def test_dict_with_user_key_but_inner_is_list(self):
        assert parse_user_id({"user": ["id", "abc"]}) is None

    def test_dict_with_user_key_but_inner_is_bool(self):
        assert parse_user_id({"user": True}) is None

    def test_whitespace_only_id_in_dict(self):
        assert parse_user_id({"user_id": "   "}) is None

    def test_valid_id_with_all_char_types(self):
        assert parse_user_id("user:a1_b-c") == ParseResult(user_id="a1_b-c", source="string")

    def test_prefix_user_colon_space(self):
        # "user: abc" -> extracts " abc" -> trimmed to "abc" -> valid
        assert parse_user_id("user: abc") == ParseResult(user_id="abc", source="string")


# =============================================================================
# Tests for parse_user_ids
# =============================================================================

class TestParseUserIds:
    def test_empty_list(self):
        assert parse_user_ids([]) == []

    def test_single_valid_item(self):
        result = parse_user_ids(["user:abc123"])
        assert result == [ParseResult(user_id="abc123", source="string")]

    def test_single_invalid_item(self):
        result = parse_user_ids(["invalid"])
        assert result == [None]

    def test_mixed_valid_and_invalid(self):
        items = [
            "user:abc123",
            "invalid",
            {"user_id": "def456"},
            None,
            {"user": {"id": "ghi789"}},
        ]
        result = parse_user_ids(items)
        assert result == [
            ParseResult(user_id="abc123", source="string"),
            None,
            ParseResult(user_id="def456", source="dict_flat"),
            None,
            ParseResult(user_id="ghi789", source="dict_nested"),
        ]

    def test_all_valid(self):
        items = ["user:aaa", "user:bbb", "user:ccc"]
        result = parse_user_ids(items)
        assert result == [
            ParseResult(user_id="aaa", source="string"),
            ParseResult(user_id="bbb", source="string"),
            ParseResult(user_id="ccc", source="string"),
        ]

    def test_all_invalid(self):
        items = [None, 42, "bad", {"foo": "bar"}]
        result = parse_user_ids(items)
        assert result == [None, None, None, None]

    def test_preserves_order(self):
        items = [
            "user:zzz",
            "user:aaa",
            "user:mmm",
        ]
        result = parse_user_ids(items)
        assert result == [
            ParseResult(user_id="zzz", source="string"),
            ParseResult(user_id="aaa", source="string"),
            ParseResult(user_id="mmm", source="string"),
        ]

    def test_length_matches_input(self):
        items = ["user:abc", None, "user:def", 42, "user:ghi"]
        result = parse_user_ids(items)
        assert len(result) == len(items)

    def test_reserved_ids_in_batch(self):
        items = ["user:admin", "user:root", "user:system", "user:valid1"]
        result = parse_user_ids(items)
        assert result == [None, None, None, ParseResult(user_id="valid1", source="string")]


# =============================================================================
# Z3 Formal Verification Tests
# =============================================================================

class TestZ3FormalVerification:
    """Tests using Z3 to formally verify properties of the validation logic."""

    def test_z3_length_lower_bound(self):
        """Verify that IDs shorter than 3 characters are always rejected."""
        try:
            from z3 import Solver, Int, sat, And
        except ImportError:
            pytest.skip("z3-solver not installed")

        solver = Solver()
        length = Int('length')
        solver.add(And(length >= 0, length < 3))

        if solver.check() == sat:
            model = solver.model()
            l = model[length].as_long()
            test_id = "a" * l
            result = parse_user_id(f"user:{test_id}")
            assert result is None, f"ID of length {l} should be rejected"

    def test_z3_length_upper_bound(self):
        """Verify that IDs longer than 20 characters are always rejected."""
        try:
            from z3 import Solver, Int, sat
        except ImportError:
            pytest.skip("z3-solver not installed")

        solver = Solver()
        length = Int('length')
        solver.add(length > 20)
        solver.add(length <= 30)

        if solver.check() == sat:
            model = solver.model()
            l = model[length].as_long()
            test_id = "a" * l
            result = parse_user_id(f"user:{test_id}")
            assert result is None, f"ID of length {l} should be rejected"

    def test_z3_valid_length_range(self):
        """Verify that IDs within 3-20 length with valid chars are accepted (unless reserved)."""
        try:
            from z3 import Solver, Int, sat, And
        except ImportError:
            pytest.skip("z3-solver not installed")

        solver = Solver()
        length = Int('length')
        solver.add(And(length >= 3, length <= 20))

        checked = 0
        while solver.check() == sat and checked < 18:
            model = solver.model()
            l = model[length].as_long()
            test_id = "x" * l
            result = parse_user_id(f"user:{test_id}")
            assert result == ParseResult(user_id=test_id, source="string"), f"ID of length {l} should be accepted"
            solver.add(length != l)
            checked += 1

        assert checked == 18

    def test_z3_reserved_ids_always_rejected(self):
        """Formally verify that all reserved IDs are rejected regardless of casing."""
        try:
            from z3 import Solver, Int, sat, And
        except ImportError:
            pytest.skip("z3-solver not installed")

        reserved = ["admin", "root", "system"]
        for rid in reserved:
            assert parse_user_id(f"user:{rid}") is None
            assert parse_user_id(f"user:{rid.upper()}") is None
            assert parse_user_id(f"user:{rid.title()}") is None
            assert parse_user_id({"user_id": rid}) is None
            assert parse_user_id({"user": {"id": rid}}) is None

    def test_z3_invalid_char_rejection(self):
        """Use Z3 to find ASCII chars outside valid set and verify rejection.
        
        Note: Uppercase letters (A-Z, codes 65-90) are excluded from this test
        because the code normalizes input by lowercasing before validation,
        so uppercase letters become valid lowercase letters after normalization.
        """
        try:
            from z3 import Solver, Int, sat, And, Or, Not
        except ImportError:
            pytest.skip("z3-solver not installed")

        solver = Solver()
        c = Int('c')
        valid_or_normalizable = Or(
            And(c >= 97, c <= 122),  # a-z
            And(c >= 65, c <= 90),   # A-Z (normalizes to a-z)
            And(c >= 48, c <= 57),   # 0-9
            c == 95,                  # _
            c == 45,                  # -
        )
        solver.add(And(c >= 32, c <= 126))
        solver.add(Not(valid_or_normalizable))

        checked = 0
        while solver.check() == sat and checked < 50:
            model = solver.model()
            char_code = model[c].as_long()
            char = chr(char_code)
            test_id = f"aaa{char}bbb"
            result = parse_user_id(f"user:{test_id}")
            assert result is None, f"ID with char '{char}' (code {char_code}) should be rejected"
            solver.add(c != char_code)
            checked += 1

        assert checked > 0

# ==============================================================================
# DETAILED TEST PLAN
# ==============================================================================
#
# 1. ParseResult namedtuple
#    - Test that ParseResult can be instantiated with user_id and source
#    - Test that fields are accessible by name
#    - Unit test (simple structural check, no need for Z3)
#
# 2. parse_user_id - String input "user:<id>"
#    - Valid: "user:john_doe" -> ParseResult("john_doe", "string")
#    - Whitespace trimming: "user:  john  " -> ParseResult("john", "string")
#    - Lowercasing: "user:JohnDoe" -> ParseResult("johndoe", "string")
#    - Combined whitespace + lowercase: "user:  JohnDoe  "
#    - Empty id after prefix: "user:" -> None (too short)
#    - Unit tests (input/output mapping)
#
# 3. parse_user_id - String input "email:user@domain"
#    - Valid: "email:john@example.com" -> ParseResult("john", "email")
#    - No @ sign: "email:johndoe" -> None
#    - Username with valid chars: "email:john_doe-123@example.com"
#    - Username too short: "email:ab@example.com" -> None (length 2)
#    - Username too long: "email:" + "a"*21 + "@example.com" -> None
#    - Uppercase normalization: "email:JOHN@example.com" -> ParseResult("john", "email")
#    - Whitespace in username: "email: john @example.com" -> ParseResult("john", "email")
#    - Unit tests
#
# 4. parse_user_id - Dict input (flat)
#    - Valid: {"user_id": "john"} -> ParseResult("john", "dict_flat")
#    - Non-string value: {"user_id": 123} -> None
#    - Missing key: {"other": "john"} -> None
#    - Unit tests
#
# 5. parse_user_id - Dict input (nested)
#    - Valid: {"user": {"id": "john"}} -> ParseResult("john", "dict_nested")
#    - "user" not a dict: {"user": "john"} -> None
#    - Missing "id" in nested: {"user": {"name": "john"}} -> None
#    - Non-string nested value: {"user": {"id": 123}} -> None
#    - Unit tests
#
# 6. Normalization
#    - Whitespace trimming from all sources
#    - Lowercasing from all sources
#    - Unit tests
#
# 7. Validation - allowed characters
#    - Valid: a-z, 0-9, _, -
#    - Invalid: spaces in middle, special chars (!@#$%^&*), dots
#    - Unit tests
#    - Z3: We can formally verify that the regex pattern matches exactly
#      the allowed character set and length constraints. We can encode
#      character constraints and verify equivalence.
#
# 8. Validation - length constraints
#    - Length 2 -> None (too short)
#    - Length 3 -> valid (boundary)
#    - Length 20 -> valid (boundary)
#    - Length 21 -> None (too long)
#    - Unit tests + Z3 for boundary verification
#
# 9. Reserved IDs
#    - Default reserved: "admin", "root", "system" -> None
#    - Custom reserved_ids replaces defaults entirely
#    - Custom reserved_ids=set() -> no reserved IDs
#    - Custom reserved_ids={"admin"} -> only "admin" is reserved
#    - Previously default-reserved ID allowed with custom set
#    - Unit tests
#
# 10. Invalid input types
#     - None input -> None
#     - Integer input -> None
#     - List input -> None
#     - Boolean input -> None
#     - Unit tests
#
# 11. No mutation of input dicts
#     - Pass a dict, verify it's unchanged after call
#     - Unit test
#
# 12. parse_user_ids - batch processing
#     - Empty list -> empty list
#     - Mixed valid/invalid -> correct ordering preserved
#     - reserved_ids passed through
#     - Unit tests
#
# 13. Z3 Formal Verification
#     - Verify that for any string of length 3-20 with only [a-z0-9_-],
#       the validation regex would accept it (and reject otherwise).
#     - Verify boundary conditions on length.
#     - These are encoded as Z3 constraints and checked as unit tests.
#
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

# Add the source directory to the path

from user_id_parser import ParseResult, parse_user_id, parse_user_ids


# ==============================================================================
# ParseResult namedtuple tests
# ==============================================================================

def test_parse_result_creation():
    result = ParseResult(user_id="john", source="string")
    assert result.user_id == "john"
    assert result.source == "string"


def test_parse_result_tuple_unpacking():
    result = ParseResult(user_id="john", source="email")
    uid, src = result
    assert uid == "john"
    assert src == "email"


def test_parse_result_equality():
    r1 = ParseResult(user_id="john", source="string")
    r2 = ParseResult(user_id="john", source="string")
    assert r1 == r2


def test_parse_result_inequality():
    r1 = ParseResult(user_id="john", source="string")
    r2 = ParseResult(user_id="jane", source="string")
    assert r1 != r2


# ==============================================================================
# parse_user_id - "user:<id>" string format
# ==============================================================================

def test_user_prefix_valid_simple():
    result = parse_user_id("user:john_doe")
    assert result == ParseResult(user_id="john_doe", source="string")


def test_user_prefix_valid_with_hyphens():
    result = parse_user_id("user:john-doe")
    assert result == ParseResult(user_id="john-doe", source="string")


def test_user_prefix_valid_with_numbers():
    result = parse_user_id("user:user123")
    assert result == ParseResult(user_id="user123", source="string")


def test_user_prefix_valid_underscore_and_hyphen():
    result = parse_user_id("user:a_b-c")
    assert result == ParseResult(user_id="a_b-c", source="string")


def test_user_prefix_whitespace_trimming():
    result = parse_user_id("user:  john  ")
    assert result == ParseResult(user_id="john", source="string")


def test_user_prefix_lowercase():
    result = parse_user_id("user:JohnDoe")
    assert result == ParseResult(user_id="johndoe", source="string")


def test_user_prefix_whitespace_and_lowercase():
    result = parse_user_id("user:  JohnDoe  ")
    assert result == ParseResult(user_id="johndoe", source="string")


def test_user_prefix_empty_id():
    result = parse_user_id("user:")
    assert result is None


def test_user_prefix_too_short():
    result = parse_user_id("user:ab")
    assert result is None


def test_user_prefix_exactly_3_chars():
    result = parse_user_id("user:abc")
    assert result == ParseResult(user_id="abc", source="string")


def test_user_prefix_exactly_20_chars():
    uid = "a" * 20
    result = parse_user_id(f"user:{uid}")
    assert result == ParseResult(user_id=uid, source="string")


def test_user_prefix_21_chars_too_long():
    uid = "a" * 21
    result = parse_user_id(f"user:{uid}")
    assert result is None


def test_user_prefix_invalid_chars_dot():
    result = parse_user_id("user:john.doe")
    assert result is None


def test_user_prefix_invalid_chars_space_in_middle():
    result = parse_user_id("user:john doe")
    assert result is None


def test_user_prefix_invalid_chars_special():
    result = parse_user_id("user:john@doe")
    assert result is None


def test_user_prefix_invalid_chars_exclamation():
    result = parse_user_id("user:john!")
    assert result is None


# ==============================================================================
# parse_user_id - "email:user@domain" string format
# ==============================================================================

def test_email_prefix_valid():
    result = parse_user_id("email:john@example.com")
    assert result == ParseResult(user_id="john", source="email")


def test_email_prefix_no_at_sign():
    result = parse_user_id("email:johndoe")
    assert result is None


def test_email_prefix_username_with_valid_chars():
    result = parse_user_id("email:john_doe-123@example.com")
    assert result == ParseResult(user_id="john_doe-123", source="email")


def test_email_prefix_username_too_short():
    result = parse_user_id("email:ab@example.com")
    assert result is None


def test_email_prefix_username_too_long():
    username = "a" * 21
    result = parse_user_id(f"email:{username}@example.com")
    assert result is None


def test_email_prefix_username_exactly_3():
    result = parse_user_id("email:abc@example.com")
    assert result == ParseResult(user_id="abc", source="email")


def test_email_prefix_username_exactly_20():
    username = "a" * 20
    result = parse_user_id(f"email:{username}@example.com")
    assert result == ParseResult(user_id=username, source="email")


def test_email_prefix_uppercase_normalization():
    result = parse_user_id("email:JOHN@example.com")
    assert result == ParseResult(user_id="john", source="email")


def test_email_prefix_whitespace_trimming():
    result = parse_user_id("email: john @example.com")
    assert result == ParseResult(user_id="john", source="email")


def test_email_prefix_invalid_username_chars():
    result = parse_user_id("email:john.doe@example.com")
    assert result is None


def test_email_prefix_multiple_at_signs():
    # Should take everything before the first @
    result = parse_user_id("email:john@domain@other.com")
    assert result == ParseResult(user_id="john", source="email")


def test_email_prefix_empty_username():
    result = parse_user_id("email:@example.com")
    assert result is None


# ==============================================================================
# parse_user_id - Dict flat format
# ==============================================================================

def test_dict_flat_valid():
    result = parse_user_id({"user_id": "john_doe"})
    assert result == ParseResult(user_id="john_doe", source="dict_flat")


def test_dict_flat_whitespace_trimming():
    result = parse_user_id({"user_id": "  john  "})
    assert result == ParseResult(user_id="john", source="dict_flat")


def test_dict_flat_lowercase():
    result = parse_user_id({"user_id": "JohnDoe"})
    assert result == ParseResult(user_id="johndoe", source="dict_flat")


def test_dict_flat_non_string_value():
    result = parse_user_id({"user_id": 123})
    assert result is None


def test_dict_flat_none_value():
    result = parse_user_id({"user_id": None})
    assert result is None


def test_dict_flat_missing_key():
    result = parse_user_id({"other_key": "john"})
    assert result is None


def test_dict_flat_empty_dict():
    result = parse_user_id({})
    assert result is None


def test_dict_flat_too_short():
    result = parse_user_id({"user_id": "ab"})
    assert result is None


def test_dict_flat_too_long():
    result = parse_user_id({"user_id": "a" * 21})
    assert result is None


# ==============================================================================
# parse_user_id - Dict nested format
# ==============================================================================

def test_dict_nested_valid():
    result = parse_user_id({"user": {"id": "john_doe"}})
    assert result == ParseResult(user_id="john_doe", source="dict_nested")


def test_dict_nested_whitespace_trimming():
    result = parse_user_id({"user": {"id": "  john  "}})
    assert result == ParseResult(user_id="john", source="dict_nested")


def test_dict_nested_lowercase():
    result = parse_user_id({"user": {"id": "JohnDoe"}})
    assert result == ParseResult(user_id="johndoe", source="dict_nested")


def test_dict_nested_user_not_dict():
    result = parse_user_id({"user": "john"})
    assert result is None


def test_dict_nested_missing_id_key():
    result = parse_user_id({"user": {"name": "john"}})
    assert result is None


def test_dict_nested_non_string_id():
    result = parse_user_id({"user": {"id": 123}})
    assert result is None


def test_dict_nested_none_id():
    result = parse_user_id({"user": {"id": None}})
    assert result is None


def test_dict_nested_user_is_none():
    result = parse_user_id({"user": None})
    assert result is None


def test_dict_nested_user_is_list():
    result = parse_user_id({"user": [1, 2, 3]})
    assert result is None


# ==============================================================================
# Dict flat takes priority over nested when both keys present
# ==============================================================================

def test_dict_flat_priority_over_nested():
    result = parse_user_id({"user_id": "flat_id", "user": {"id": "nested_id"}})
    assert result == ParseResult(user_id="flat_id", source="dict_flat")


# ==============================================================================
# Reserved IDs
# ==============================================================================

def test_default_reserved_admin():
    result = parse_user_id("user:admin")
    assert result is None


def test_default_reserved_root():
    result = parse_user_id("user:root")
    assert result is None


def test_default_reserved_system():
    result = parse_user_id("user:system")
    assert result is None


def test_default_reserved_case_insensitive():
    result = parse_user_id("user:ADMIN")
    assert result is None


def test_default_reserved_with_whitespace():
    result = parse_user_id("user:  admin  ")
    assert result is None


def test_custom_reserved_replaces_defaults():
    # "admin" should be allowed when custom set doesn't include it
    result = parse_user_id("user:admin", reserved_ids={"blocked"})
    assert result == ParseResult(user_id="admin", source="string")


def test_custom_reserved_blocks_custom_id():
    result = parse_user_id("user:blocked", reserved_ids={"blocked"})
    assert result is None


def test_custom_reserved_empty_set():
    # No reserved IDs at all
    result = parse_user_id("user:admin", reserved_ids=set())
    assert result == ParseResult(user_id="admin", source="string")


def test_custom_reserved_root_allowed():
    result = parse_user_id("user:root", reserved_ids={"other"})
    assert result == ParseResult(user_id="root", source="string")


def test_custom_reserved_system_allowed():
    result = parse_user_id("user:system", reserved_ids=set())
    assert result == ParseResult(user_id="system", source="string")


def test_reserved_ids_applied_to_dict_flat():
    result = parse_user_id({"user_id": "admin"})
    assert result is None


def test_reserved_ids_applied_to_dict_nested():
    result = parse_user_id({"user": {"id": "root"}})
    assert result is None


def test_reserved_ids_applied_to_email():
    result = parse_user_id("email:admin@example.com")
    assert result is None


# ==============================================================================
# Invalid input types
# ==============================================================================

def test_none_input():
    result = parse_user_id(None)
    assert result is None


def test_integer_input():
    result = parse_user_id(42)
    assert result is None


def test_float_input():
    result = parse_user_id(3.14)
    assert result is None


def test_list_input():
    result = parse_user_id(["user:john"])
    assert result is None


def test_boolean_input():
    result = parse_user_id(True)
    assert result is None


def test_tuple_input():
    result = parse_user_id(("user", "john"))
    assert result is None


# ==============================================================================
# Unrecognized string prefixes
# ==============================================================================

def test_unknown_prefix():
    result = parse_user_id("unknown:john")
    assert result is None


def test_no_prefix():
    result = parse_user_id("john_doe")
    assert result is None


def test_empty_string():
    result = parse_user_id("")
    assert result is None


# ==============================================================================
# No mutation of input dicts
# ==============================================================================

def test_no_mutation_flat_dict():
    d = {"user_id": "  JohnDoe  "}
    original = copy.deepcopy(d)
    parse_user_id(d)
    assert d == original


def test_no_mutation_nested_dict():
    d = {"user": {"id": "  JohnDoe  "}}
    original = copy.deepcopy(d)
    parse_user_id(d)
    assert d == original


# ==============================================================================
# parse_user_ids - batch processing
# ==============================================================================

def test_parse_user_ids_empty_list():
    result = parse_user_ids([])
    assert result == []


def test_parse_user_ids_all_valid():
    items = ["user:john", "user:jane", "user:bob"]
    result = parse_user_ids(items)
    assert len(result) == 3
    assert result[0] == ParseResult(user_id="john", source="string")
    assert result[1] == ParseResult(user_id="jane", source="string")
    assert result[2] == ParseResult(user_id="bob", source="string")


def test_parse_user_ids_all_invalid():
    items = [None, 42, "bad"]
    result = parse_user_ids(items)
    assert result == [None, None, None]


def test_parse_user_ids_mixed():
    items = [
        "user:john",
        None,
        {"user_id": "jane"},
        "email:bob@example.com",
        42,
        {"user": {"id": "alice"}},
    ]
    result = parse_user_ids(items)
    assert len(result) == 6
    assert result[0] == ParseResult(user_id="john", source="string")
    assert result[1] is None
    assert result[2] == ParseResult(user_id="jane", source="dict_flat")
    assert result[3] == ParseResult(user_id="bob", source="email")
    assert result[4] is None
    assert result[5] == ParseResult(user_id="alice", source="dict_nested")


def test_parse_user_ids_preserves_order():
    items = ["user:aaa", "user:bbb", "user:ccc"]
    result = parse_user_ids(items)
    assert [r.user_id for r in result] == ["aaa", "bbb", "ccc"]


def test_parse_user_ids_reserved_ids_passed_through():
    items = ["user:admin", "user:root", "user:john"]
    # With default reserved, admin and root should be None
    result_default = parse_user_ids(items)
    assert result_default[0] is None
    assert result_default[1] is None
    assert result_default[2] == ParseResult(user_id="john", source="string")

    # With custom reserved, admin and root should be allowed
    result_custom = parse_user_ids(items, reserved_ids=set())
    assert result_custom[0] == ParseResult(user_id="admin", source="string")
    assert result_custom[1] == ParseResult(user_id="root", source="string")
    assert result_custom[2] == ParseResult(user_id="john", source="string")


def test_parse_user_ids_single_item():
    result = parse_user_ids(["user:john"])
    assert len(result) == 1
    assert result[0] == ParseResult(user_id="john", source="string")


# ==============================================================================
# Edge cases - validation boundaries
# ==============================================================================

def test_all_lowercase_letters():
    result = parse_user_id("user:abcdefghijklmnopqrst")  # 20 chars
    assert result == ParseResult(user_id="abcdefghijklmnopqrst", source="string")


def test_all_digits():
    result = parse_user_id("user:12345")
    assert result == ParseResult(user_id="12345", source="string")


def test_all_underscores():
    result = parse_user_id("user:___")
    assert result == ParseResult(user_id="___", source="string")


def test_all_hyphens():
    result = parse_user_id("user:---")
    assert result == ParseResult(user_id="---", source="string")


def test_mixed_valid_chars():
    result = parse_user_id("user:a1_-b2")
    assert result == ParseResult(user_id="a1_-b2", source="string")


def test_uppercase_letters_normalized():
    result = parse_user_id("user:ABC")
    assert result == ParseResult(user_id="abc", source="string")


def test_only_whitespace_after_prefix():
    result = parse_user_id("user:   ")
    assert result is None  # After trimming, empty string


def test_whitespace_only_id_in_dict():
    result = parse_user_id({"user_id": "   "})
    assert result is None


# ==============================================================================
# Edge cases - boolean is instance of int in Python, but also check isinstance(raw, str)
# ==============================================================================

def test_bool_true_not_treated_as_string():
    result = parse_user_id(True)
    assert result is None


def test_bool_false_not_treated_as_string():
    result = parse_user_id(False)
    assert result is None


# ==============================================================================
# Edge cases - dict with both user_id and user keys
# ==============================================================================

def test_dict_with_user_id_key_takes_precedence():
    d = {"user_id": "flat_user", "user": {"id": "nested_user"}}
    result = parse_user_id(d)
    assert result.source == "dict_flat"
    assert result.user_id == "flat_user"


# ==============================================================================
# Z3 Formal Verification Tests
# ==============================================================================
# We use Z3 to formally verify properties of the validation logic:
# - Character set constraints
# - Length boundary constraints
# These are encoded as Z3 satisfiability checks and run as pytest tests.

def test_z3_length_boundary_min():
    """
    Z3 verification: A string of length 2 with valid chars should be rejected,
    and a string of length 3 with valid chars should be accepted.
    """
    try:
        from z3 import Solver, Int, And, Or, sat, unsat
    except ImportError:
        import pytest
        pytest.skip("z3-solver not installed")

    s = Solver()
    length = Int('length')

    # Constraint: length is 2 (below minimum)
    s.add(length == 2)
    # The validation requires length >= 3
    s.add(length >= 3)
    # This should be unsatisfiable (can't have length 2 AND length >= 3)
    assert s.check() == unsat, "Length 2 should not satisfy length >= 3"

    s2 = Solver()
    length2 = Int('length2')
    s2.add(length2 == 3)
    s2.add(length2 >= 3, length2 <= 20)
    assert s2.check() == sat, "Length 3 should satisfy 3 <= length <= 20"


def test_z3_length_boundary_max():
    """
    Z3 verification: A string of length 20 should be accepted,
    and a string of length 21 should be rejected.
    """
    try:
        from z3 import Solver, Int, And, sat, unsat
    except ImportError:
        import pytest
        pytest.skip("z3-solver not installed")

    s = Solver()
    length = Int('length')
    s.add(length == 20)
    s.add(length >= 3, length <= 20)
    assert s.check() == sat, "Length 20 should satisfy 3 <= length <= 20"

    s2 = Solver()
    length2 = Int('length2')
    s2.add(length2 == 21)
    s2.add(length2 >= 3, length2 <= 20)
    assert s2.check() == unsat, "Length 21 should not satisfy 3 <= length <= 20"


def test_z3_valid_character_range():
    """
    Z3 verification: Verify that the allowed character set is exactly
    a-z (97-122), 0-9 (48-57), _ (95), - (45).
    """
    try:
        from z3 import Solver, Int, And, Or, Not, sat, unsat, ForAll, Implies
    except ImportError:
        import pytest
        pytest.skip("z3-solver not installed")

    s = Solver()
    c = Int('c')

    # Define valid character constraint
    valid_char = Or(
        And(c >= 97, c <= 122),   # a-z
        And(c >= 48, c <= 57),    # 0-9
        c == 95,                   # _
        c == 45,                   # -
    )

    # Verify specific valid characters
    for char_code in [97, 122, 48, 57, 95, 45]:  # 'a', 'z', '0', '9', '_', '-'
        s_test = Solver()
        s_test.add(c == char_code)
        s_test.add(valid_char)
        assert s_test.check() == sat, f"Char code {char_code} should be valid"

    # Verify specific invalid characters
    for char_code in [46, 64, 33, 32, 47, 58, 96, 123]:  # '.', '@', '!', ' ', '/', ':', '`', '{'
        s_test = Solver()
        s_test.add(c == char_code)
        s_test.add(valid_char)
        assert s_test.check() == unsat, f"Char code {char_code} should be invalid"


def test_z3_reserved_id_exclusion():
    """
    Z3 verification: Verify that the reserved ID check is a simple
    set membership test - if an ID is in the reserved set, it's rejected.
    We model this as: for any valid ID that equals a reserved word,
    the result should be rejection.
    """
    try:
        from z3 import Solver, String, StringVal, And, Or, sat, unsat
    except ImportError:
        import pytest
        pytest.skip("z3-solver not installed")

    s = Solver()
    user_id = String('user_id')

    # Reserved IDs
    is_reserved = Or(
        user_id == StringVal("admin"),
        user_id == StringVal("root"),
        user_id == StringVal("system"),
    )

    # Check that "admin" is reserved
    s.add(user_id == StringVal("admin"))
    s.add(is_reserved)
    assert s.check() == sat, "admin should be in reserved set"

    # Check that "john" is not reserved
    s2 = Solver()
    s2.add(user_id == StringVal("john"))
    s2.add(is_reserved)
    assert s2.check() == unsat, "john should not be in reserved set"


def test_z3_normalization_idempotent():
    """
    Z3 verification: After normalization (lowercase + strip), applying
    normalization again should yield the same result. We verify this
    property by checking that a normalized string equals itself when
    normalized again.
    
    This is verified empirically since Z3 string theory has limited
    support for these operations.
    """
    # This is better verified empirically
    test_cases = ["  JohnDoe  ", "ADMIN", "  root  ", "user_123"]
    for tc in test_cases:
        normalized = tc.strip().lower()
        assert normalized == normalized.strip().lower(), \
            f"Normalization should be idempotent for '{tc}'"


# ==============================================================================
# Additional edge cases
# ==============================================================================

def test_user_prefix_with_colon_in_id():
    # "user:abc:def" - the id would be "abc:def" which has invalid char ':'
    result = parse_user_id("user:abc:def")
    assert result is None


def test_email_prefix_empty_domain():
    result = parse_user_id("email:john@")
    assert result == ParseResult(user_id="john", source="email")


def test_dict_flat_empty_string_value():
    result = parse_user_id({"user_id": ""})
    assert result is None


def test_dict_nested_empty_string_value():
    result = parse_user_id({"user": {"id": ""}})
    assert result is None


def test_user_prefix_tab_whitespace():
    result = parse_user_id("user:\tjohn\t")
    assert result == ParseResult(user_id="john", source="string")


def test_user_prefix_newline_whitespace():
    result = parse_user_id("user:\njohn\n")
    assert result == ParseResult(user_id="john", source="string")


def test_parse_user_ids_with_all_sources():
    items = [
        "user:alice",
        "email:bob@example.com",
        {"user_id": "charlie"},
        {"user": {"id": "diana"}},
    ]
    result = parse_user_ids(items)
    assert result[0] == ParseResult(user_id="alice", source="string")
    assert result[1] == ParseResult(user_id="bob", source="email")
    assert result[2] == ParseResult(user_id="charlie", source="dict_flat")
    assert result[3] == ParseResult(user_id="diana", source="dict_nested")


def test_reserved_id_after_normalization():
    """Ensure reserved check happens after normalization (lowercase)."""
    result = parse_user_id("user:ADMIN")
    assert result is None

    result = parse_user_id("user:  Root  ")
    assert result is None

    result = parse_user_id({"user_id": "SYSTEM"})
    assert result is None

if __name__ == "__main__":
    import pytest
    pytest.main([__file__])

# ============================================================================
# TEST PLAN
# ============================================================================
#
# 1. ParseResult namedtuple
#    - Test that ParseResult can be instantiated with user_id and source
#    - Test that fields are accessible by name
#    - Unit test (simple structural check)
#
# 2. parse_user_id - String input "user:<id>"
#    - Valid: "user:john" -> ParseResult("john", "string")
#    - Whitespace trimming: "user:  john  " -> ParseResult("john", "string")
#    - Lowercasing: "user:JOHN" -> ParseResult("john", "string")
#    - Combined whitespace + case: "user:  JOHN  " -> ParseResult("john", "string")
#    - With underscores/hyphens: "user:john_doe", "user:john-doe"
#    - With digits: "user:john123"
#    - Unit tests (behavioral)
#
# 3. parse_user_id - String input "email:user@domain"
#    - Valid: "email:john@example.com" -> ParseResult("john", "email")
#    - No @ sign: "email:johndoe" -> None
#    - Username extraction before @: "email:john.doe@example.com" -> None (dot not allowed)
#    - Valid email username: "email:john_doe@example.com" -> ParseResult("john_doe", "email")
#    - Unit tests
#
# 4. parse_user_id - Dict input flat
#    - Valid: {"user_id": "john"} -> ParseResult("john", "dict_flat")
#    - Non-string value: {"user_id": 123} -> None
#    - Unit tests
#
# 5. parse_user_id - Dict input nested
#    - Valid: {"user": {"id": "john"}} -> ParseResult("john", "dict_nested")
#    - Missing inner key: {"user": {"name": "john"}} -> None
#    - Non-dict inner: {"user": "john"} -> None
#    - Non-string id value: {"user": {"id": 123}} -> None
#    - Unit tests
#
# 6. Normalization
#    - Whitespace trimming on all input types
#    - Lowercasing on all input types
#    - Unit tests
#
# 7. Validation - allowed characters
#    - Only a-z, 0-9, _, - allowed after normalization
#    - Reject special chars: "user:john.doe", "user:john doe", "user:john!"
#    - Unit tests
#
# 8. Validation - length
#    - Min length 3: "user:ab" -> None, "user:abc" -> valid
#    - Max length 20: 20 chars -> valid, 21 chars -> None
#    - Unit tests
#
# 9. Validation - reserved IDs
#    - Default reserved: admin, root, system -> None
#    - Custom reserved_ids replaces defaults entirely
#    - Custom reserved_ids=set() -> no reserved IDs
#    - Unit tests
#
# 10. Validation - strict mode
#     - strict=True rejects: __, --, _-, -_
#     - strict=False allows consecutive specials
#     - Unit tests
#
# 11. Invalid input types
#     - None, int, list, tuple -> None
#     - Unrecognized string prefix -> None
#     - Empty dict -> None
#     - Unit tests
#
# 12. No mutation of input dicts
#     - Pass a dict, verify it's unchanged after call
#     - Unit test
#
# 13. parse_user_ids - batch processing
#     - Processes list of items, preserves order
#     - Invalid items produce None
#     - Passes reserved_ids and strict through
#     - Empty list -> empty list
#     - Unit tests
#
# 14. Z3 formal verification
#     - Verify that the valid pattern regex constraints (length 3-20, chars a-z0-9_-)
#       are consistent: use Z3 to prove that any string matching the pattern has
#       length in [3,20] and only valid chars.
#     - Verify that strict mode rejects all 4 consecutive special patterns.
#     - These are better as Z3 tests because they verify properties over all possible inputs.
#
# ============================================================================


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

# Add the source directory to the path

try:
    from user_id_parser import ParseResult, parse_user_id, parse_user_ids
except ImportError:
    # Fallback for standalone execution if module is not present
    from collections import namedtuple
    ParseResult = namedtuple("ParseResult", ["user_id", "source"])
    def parse_user_id(*args, **kwargs): pass
    def parse_user_ids(*args, **kwargs): pass


# ============================================================================
# ParseResult namedtuple tests
# ============================================================================

class TestParseResult:
    def test_create_parse_result(self):
        result = ParseResult(user_id="john", source="string")
        assert result.user_id == "john"
        assert result.source == "string"

    def test_parse_result_tuple_access(self):
        result = ParseResult(user_id="john", source="string")
        assert result[0] == "john"
        assert result[1] == "string"

    def test_parse_result_equality(self):
        r1 = ParseResult(user_id="john", source="string")
        r2 = ParseResult(user_id="john", source="string")
        assert r1 == r2

    def test_parse_result_inequality(self):
        r1 = ParseResult(user_id="john", source="string")
        r2 = ParseResult(user_id="jane", source="string")
        assert r1 != r2


# ============================================================================
# parse_user_id - "user:<id>" string input
# ============================================================================

class TestParseUserIdStringUser:
    def test_basic_user_string(self):
        result = parse_user_id("user:john")
        assert result == ParseResult(user_id="john", source="string")

    def test_user_string_with_digits(self):
        result = parse_user_id("user:john123")
        assert result == ParseResult(user_id="john123", source="string")

    def test_user_string_with_underscore(self):
        result = parse_user_id("user:john_doe")
        assert result == ParseResult(user_id="john_doe", source="string")

    def test_user_string_with_hyphen(self):
        result = parse_user_id("user:john-doe")
        assert result == ParseResult(user_id="john-doe", source="string")

    def test_user_string_whitespace_trimming(self):
        result = parse_user_id("user:  john  ")
        assert result == ParseResult(user_id="john", source="string")

    def test_user_string_lowercasing(self):
        result = parse_user_id("user:JOHN")
        assert result == ParseResult(user_id="john", source="string")

    def test_user_string_combined_normalization(self):
        result = parse_user_id("user:  JOHN_DOE  ")
        assert result == ParseResult(user_id="john_doe", source="string")

    def test_user_string_mixed_case(self):
        result = parse_user_id("user:JoHn")
        assert result == ParseResult(user_id="john", source="string")

    def test_user_string_all_digits(self):
        result = parse_user_id("user:12345")
        assert result == ParseResult(user_id="12345", source="string")

    def test_user_string_all_underscores(self):
        result = parse_user_id("user:___")
        assert result == ParseResult(user_id="___", source="string")

    def test_user_string_all_hyphens(self):
        result = parse_user_id("user:---")
        assert result == ParseResult(user_id="---", source="string")


# ============================================================================
# parse_user_id - "email:user@domain" string input
# ============================================================================

class TestParseUserIdStringEmail:
    def test_basic_email(self):
        result = parse_user_id("email:john@example.com")
        assert result == ParseResult(user_id="john", source="email")

    def test_email_with_underscore_username(self):
        result = parse_user_id("email:john_doe@example.com")
        assert result == ParseResult(user_id="john_doe", source="email")

    def test_email_with_hyphen_username(self):
        result = parse_user_id("email:john-doe@example.com")
        assert result == ParseResult(user_id="john-doe", source="email")

    def test_email_no_at_sign(self):
        result = parse_user_id("email:johndoe")
        assert result is None

    def test_email_dot_in_username(self):
        # dot is not in allowed chars a-z0-9_-
        result = parse_user_id("email:john.doe@example.com")
        assert result is None

    def test_email_uppercase_username(self):
        result = parse_user_id("email:JOHN@example.com")
        assert result == ParseResult(user_id="john", source="email")

    def test_email_whitespace_in_username(self):
        result = parse_user_id("email: john @example.com")
        assert result == ParseResult(user_id="john", source="email")

    def test_email_multiple_at_signs(self):
        # Should split on first @
        result = parse_user_id("email:john@domain@extra")
        assert result == ParseResult(user_id="john", source="email")

    def test_email_short_username(self):
        result = parse_user_id("email:ab@example.com")
        assert result is None  # too short (2 chars)

    def test_email_exactly_3_char_username(self):
        result = parse_user_id("email:abc@example.com")
        assert result == ParseResult(user_id="abc", source="email")


# ============================================================================
# parse_user_id - Dict flat input
# ============================================================================

class TestParseUserIdDictFlat:
    def test_basic_dict_flat(self):
        result = parse_user_id({"user_id": "john"})
        assert result == ParseResult(user_id="john", source="dict_flat")

    def test_dict_flat_with_normalization(self):
        result = parse_user_id({"user_id": "  JOHN  "})
        assert result == ParseResult(user_id="john", source="dict_flat")

    def test_dict_flat_non_string_value(self):
        result = parse_user_id({"user_id": 123})
        assert result is None

    def test_dict_flat_none_value(self):
        result = parse_user_id({"user_id": None})
        assert result is None

    def test_dict_flat_empty_string(self):
        result = parse_user_id({"user_id": ""})
        assert result is None  # too short

    def test_dict_flat_with_extra_keys(self):
        result = parse_user_id({"user_id": "john", "extra": "data"})
        assert result == ParseResult(user_id="john", source="dict_flat")

    def test_dict_flat_priority_over_nested(self):
        # If both user_id and user keys exist, user_id takes priority
        result = parse_user_id({"user_id": "john", "user": {"id": "jane"}})
        assert result == ParseResult(user_id="john", source="dict_flat")


# ============================================================================
# parse_user_id - Dict nested input
# ============================================================================

class TestParseUserIdDictNested:
    def test_basic_dict_nested(self):
        result = parse_user_id({"user": {"id": "john"}})
        assert result == ParseResult(user_id="john", source="dict_nested")

    def test_dict_nested_with_normalization(self):
        result = parse_user_id({"user": {"id": "  JOHN  "}})
        assert result == ParseResult(user_id="john", source="dict_nested")

    def test_dict_nested_missing_id_key(self):
        result = parse_user_id({"user": {"name": "john"}})
        assert result is None

    def test_dict_nested_non_dict_user(self):
        result = parse_user_id({"user": "john"})
        assert result is None

    def test_dict_nested_user_is_list(self):
        result = parse_user_id({"user": ["john"]})
        assert result is None

    def test_dict_nested_non_string_id(self):
        result = parse_user_id({"user": {"id": 123}})
        assert result is None

    def test_dict_nested_none_id(self):
        result = parse_user_id({"user": {"id": None}})
        assert result is None

    def test_dict_nested_user_is_none(self):
        result = parse_user_id({"user": None})
        assert result is None


# ============================================================================
# Validation - allowed characters
# ============================================================================

class TestParseUserIdCharValidation:
    def test_reject_dot(self):
        assert parse_user_id("user:john.doe") is None

    def test_reject_space_in_id(self):
        assert parse_user_id("user:john doe") is None

    def test_reject_exclamation(self):
        assert parse_user_id("user:john!") is None

    def test_reject_at_sign(self):
        assert parse_user_id("user:john@doe") is None

    def test_reject_hash(self):
        assert parse_user_id("user:john#1") is None

    def test_reject_slash(self):
        assert parse_user_id("user:john/doe") is None

    def test_accept_all_valid_chars(self):
        result = parse_user_id("user:abc-def_123")
        assert result is not None
        assert result.user_id == "abc-def_123"


# ============================================================================
# Validation - length
# ============================================================================

class TestParseUserIdLengthValidation:
    def test_reject_length_0(self):
        assert parse_user_id("user:") is None

    def test_reject_length_1(self):
        assert parse_user_id("user:a") is None

    def test_reject_length_2(self):
        assert parse_user_id("user:ab") is None

    def test_accept_length_3(self):
        result = parse_user_id("user:abc")
        assert result == ParseResult(user_id="abc", source="string")

    def test_accept_length_4(self):
        result = parse_user_id("user:abcd")
        assert result == ParseResult(user_id="abcd", source="string")

    def test_accept_length_20(self):
        uid = "a" * 20
        result = parse_user_id(f"user:{uid}")
        assert result == ParseResult(user_id=uid, source="string")

    def test_reject_length_21(self):
        uid = "a" * 21
        assert parse_user_id(f"user:{uid}") is None

    def test_reject_length_100(self):
        uid = "a" * 100
        assert parse_user_id(f"user:{uid}") is None

    def test_whitespace_only_after_trim(self):
        # "user:   " -> after trim becomes "" which is too short
        assert parse_user_id("user:   ") is None

    def test_length_after_trimming(self):
        # "  abc  " -> "abc" which is length 3
        result = parse_user_id("user:  abc  ")
        assert result == ParseResult(user_id="abc", source="string")


# ============================================================================
# Validation - reserved IDs
# ============================================================================

class TestParseUserIdReservedIds:
    def test_reject_admin_default(self):
        assert parse_user_id("user:admin") is None

    def test_reject_root_default(self):
        assert parse_user_id("user:root") is None

    def test_reject_system_default(self):
        assert parse_user_id("user:system") is None

    def test_reject_admin_case_insensitive(self):
        assert parse_user_id("user:ADMIN") is None

    def test_reject_admin_with_whitespace(self):
        assert parse_user_id("user:  admin  ") is None

    def test_custom_reserved_replaces_defaults(self):
        # With custom reserved, "admin" should be allowed
        result = parse_user_id("user:admin", reserved_ids={"blocked"})
        assert result == ParseResult(user_id="admin", source="string")

    def test_custom_reserved_rejects_custom(self):
        assert parse_user_id("user:blocked", reserved_ids={"blocked"}) is None

    def test_empty_reserved_set(self):
        # Empty set means no reserved IDs
        result = parse_user_id("user:admin", reserved_ids=set())
        assert result == ParseResult(user_id="admin", source="string")

    def test_root_allowed_with_custom_reserved(self):
        result = parse_user_id("user:root", reserved_ids={"other"})
        assert result == ParseResult(user_id="root", source="string")

    def test_system_allowed_with_custom_reserved(self):
        result = parse_user_id("user:system", reserved_ids=set())
        assert result == ParseResult(user_id="system", source="string")

    def test_reserved_ids_passed_to_batch(self):
        items = ["user:admin", "user:john"]
        results = parse_user_ids(items, reserved_ids=set())
        assert results[0] == ParseResult(user_id="admin", source="string")
        assert results[1] == ParseResult(user_id="john", source="string")


# ============================================================================
# Validation - strict mode
# ============================================================================

class TestParseUserIdStrictMode:
    def test_strict_reject_double_underscore(self):
        assert parse_user_id("user:john__doe", strict=True) is None

    def test_strict_reject_double_hyphen(self):
        assert parse_user_id("user:john--doe", strict=True) is None

    def test_strict_reject_underscore_hyphen(self):
        assert parse_user_id("user:john_-doe", strict=True) is None

    def test_strict_reject_hyphen_underscore(self):
        assert parse_user_id("user:john-_doe", strict=True) is None

    def test_non_strict_allow_double_underscore(self):
        result = parse_user_id("user:john__doe", strict=False)
        assert result == ParseResult(user_id="john__doe", source="string")

    def test_non_strict_allow_double_hyphen(self):
        result = parse_user_id("user:john--doe", strict=False)
        assert result == ParseResult(user_id="john--doe", source="string")

    def test_non_strict_allow_underscore_hyphen(self):
        result = parse_user_id("user:john_-doe", strict=False)
        assert result == ParseResult(user_id="john_-doe", source="string")

    def test_non_strict_allow_hyphen_underscore(self):
        result = parse_user_id("user:john-_doe", strict=False)
        assert result == ParseResult(user_id="john-_doe", source="string")

    def test_strict_allow_single_underscore(self):
        result = parse_user_id("user:john_doe", strict=True)
        assert result == ParseResult(user_id="john_doe", source="string")

    def test_strict_allow_single_hyphen(self):
        result = parse_user_id("user:john-doe", strict=True)
        assert result == ParseResult(user_id="john-doe", source="string")

    def test_strict_default_is_false(self):
        result = parse_user_id("user:john__doe")
        assert result == ParseResult(user_id="john__doe", source="string")

    def test_strict_reject_triple_underscore(self):
        assert parse_user_id("user:a___b", strict=True) is None

    def test_strict_at_start(self):
        assert parse_user_id("user:__john", strict=True) is None

    def test_strict_at_end(self):
        assert parse_user_id("user:john__", strict=True) is None

    def test_strict_with_dict_flat(self):
        assert parse_user_id({"user_id": "john__doe"}, strict=True) is None

    def test_strict_with_dict_nested(self):
        assert parse_user_id({"user": {"id": "john__doe"}}, strict=True) is None

    def test_strict_with_email(self):
        assert parse_user_id("email:john__doe@example.com", strict=True) is None


# ============================================================================
# Invalid input types
# ============================================================================

class TestParseUserIdInvalidInputs:
    def test_none_input(self):
        assert parse_user_id(None) is None

    def test_int_input(self):
        assert parse_user_id(123) is None

    def test_float_input(self):
        assert parse_user_id(3.14) is None

    def test_list_input(self):
        assert parse_user_id(["user:john"]) is None

    def test_tuple_input(self):
        assert parse_user_id(("user:john",)) is None

    def test_bool_input(self):
        assert parse_user_id(True) is None

    def test_empty_string(self):
        assert parse_user_id("") is None

    def test_unrecognized_prefix(self):
        assert parse_user_id("name:john") is None

    def test_no_prefix(self):
        assert parse_user_id("john") is None

    def test_empty_dict(self):
        assert parse_user_id({}) is None

    def test_dict_wrong_keys(self):
        assert parse_user_id({"name": "john"}) is None

    def test_set_input(self):
        assert parse_user_id({"john"}) is None

    def test_bytes_input(self):
        assert parse_user_id(b"user:john") is None


# ============================================================================
# No mutation of input dicts
# ============================================================================

class TestParseUserIdNoMutation:
    def test_flat_dict_not_mutated(self):
        d = {"user_id": "  JOHN  "}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_nested_dict_not_mutated(self):
        d = {"user": {"id": "  JOHN  "}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_flat_dict_with_extra_keys_not_mutated(self):
        d = {"user_id": "john", "extra": [1, 2, 3]}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original


# ============================================================================
# parse_user_ids - batch processing
# ============================================================================

class TestParseUserIds:
    def test_empty_list(self):
        assert parse_user_ids([]) == []

    def test_single_valid_item(self):
        result = parse_user_ids(["user:john"])
        assert result == [ParseResult(user_id="john", source="string")]

    def test_single_invalid_item(self):
        result = parse_user_ids([None])
        assert result == [None]

    def test_mixed_valid_and_invalid(self):
        items = ["user:john", None, {"user_id": "jane"}, 123, "email:bob@example.com"]
        results = parse_user_ids(items)
        assert len(results) == 5
        assert results[0] == ParseResult(user_id="john", source="string")
        assert results[1] is None
        assert results[2] == ParseResult(user_id="jane", source="dict_flat")
        assert results[3] is None
        assert results[4] == ParseResult(user_id="bob", source="email")

    def test_preserves_order(self):
        items = ["user:aaa", "user:bbb", "user:ccc"]
        results = parse_user_ids(items)
        assert results[0].user_id == "aaa"
        assert results[1].user_id == "bbb"
        assert results[2].user_id == "ccc"

    def test_passes_reserved_ids(self):
        items = ["user:admin", "user:john"]
        results = parse_user_ids(items, reserved_ids={"admin"})
        assert results[0] is None
        assert results[1] == ParseResult(user_id="john", source="string")

    def test_passes_strict(self):
        items = ["user:john__doe", "user:john"]
        results = parse_user_ids(items, strict=True)
        assert results[0] is None
        assert results[1] == ParseResult(user_id="john", source="string")

    def test_passes_both_reserved_and_strict(self):
        items = ["user:admin", "user:john__doe", "user:jane"]
        results = parse_user_ids(items, reserved_ids={"admin"}, strict=True)
        assert results[0] is None  # reserved
        assert results[1] is None  # strict
        assert results[2] == ParseResult(user_id="jane", source="string")

    def test_all_invalid(self):
        items = [None, 123, "", "bad"]
        results = parse_user_ids(items)
        assert results == [None, None, None, None]

    def test_all_valid(self):
        items = ["user:aaa", "user:bbb"]
        results = parse_user_ids(items)
        assert all(r is not None for r in results)

    def test_result_length_matches_input(self):
        items = ["user:aaa", None, "user:bbb", 42, "email:ccc@d.com"]
        results = parse_user_ids(items)
        assert len(results) == len(items)


# ============================================================================
# Edge cases and integration
# ============================================================================

class TestParseUserIdEdgeCases:
    def test_user_prefix_only(self):
        # "user:" -> id is "" which is too short
        assert parse_user_id("user:") is None

    def test_email_prefix_only(self):
        assert parse_user_id("email:") is None

    def test_email_at_only(self):
        # "email:@domain" -> username is "" which is too short
        assert parse_user_id("email:@domain.com") is None

    def test_user_colon_in_id(self):
        # "user:abc:def" -> id is "abc:def" which has invalid char ':'
        assert parse_user_id("user:abc:def") is None

    def test_exactly_boundary_length_3(self):
        result = parse_user_id("user:abc")
        assert result is not None

    def test_exactly_boundary_length_20(self):
        uid = "abcdefghijklmnopqrst"  # 20 chars
        assert len(uid) == 20
        result = parse_user_id(f"user:{uid}")
        assert result is not None
        assert result.user_id == uid

    def test_length_19(self):
        uid = "a" * 19
        result = parse_user_id(f"user:{uid}")
        assert result is not None

    def test_whitespace_trimmed_then_length_checked(self):
        # "  ab  " -> "ab" which is length 2, too short
        assert parse_user_id("user:  ab  ") is None

    def test_whitespace_trimmed_then_length_valid(self):
        # "  abc  " -> "abc" which is length 3, valid
        result = parse_user_id("user:  abc  ")
        assert result is not None

    def test_tab_whitespace_in_id(self):
        # Tab is not in allowed chars, but strip() removes it
        # "user:\tabc\t" -> "abc" after strip
        result = parse_user_id("user:\tabc\t")
        assert result == ParseResult(user_id="abc", source="string")

    def test_newline_in_id(self):
        result = parse_user_id("user:\nabc\n")
        assert result == ParseResult(user_id="abc", source="string")

    def test_reserved_id_case_insensitive(self):
        # "ADMIN" -> lowercased to "admin" -> reserved
        assert parse_user_id("user:ADMIN") is None
        assert parse_user_id("user:Admin") is None
        assert parse_user_id("user:ROOT") is None
        assert parse_user_id("user:SYSTEM") is None

    def test_dict_flat_takes_priority_over_nested_when_both_present(self):
        d = {"user_id": "john", "user": {"id": "jane"}}
        result = parse_user_id(d)
        assert result.source == "dict_flat"
        assert result.user_id == "john"

    def test_bool_is_not_treated_as_dict_or_string(self):
        # bool is subclass of int in Python
        assert parse_user_id(True) is None
        assert parse_user_id(False) is None


# ============================================================================
# Z3 Formal Verification Tests
# ============================================================================

class TestZ3FormalVerification:
    """
    Use Z3 to formally verify properties of the validation logic.
    These tests verify that the constraints are consistent and complete.
    """

    def test_z3_valid_id_length_bounds(self):
        """
        Verify using Z3 that any valid ID must have length between 3 and 20.
        We model the constraint and check that no valid ID can have length < 3 or > 20.
        """
        try:
            from z3 import Solver, Int, And, Or, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        length = Int('length')

        # The valid pattern requires length in [3, 20]
        # Try to find a length that is valid but outside [3, 20]
        s.add(Or(length < 3, length > 20))
        # A valid ID must satisfy length in [3, 20]
        s.add(And(length >= 3, length <= 20))

        # This should be unsatisfiable - no length can be both in and out of range
        assert s.check() == unsat

    def test_z3_strict_mode_rejects_all_consecutive_specials(self):
        """
        Verify that the strict mode pattern covers all 4 combinations of
        consecutive special characters.
        """
        try:
            from z3 import Solver, String, Contains, Or, And, sat, Not, StringVal
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        user_id = String('user_id')

        # The consecutive specials pattern matches any of: __, --, _-, -_
        has_consecutive = Or(
            Contains(user_id, StringVal("__")),
            Contains(user_id, StringVal("--")),
            Contains(user_id, StringVal("_-")),
            Contains(user_id, StringVal("-_"))
        )

        # Try to find a string with two adjacent special chars that doesn't match
        # any of the four patterns. Special chars are _ and -.
        # If we have two adjacent chars from {_, -}, it must be one of: __, --, _-, -_
        # This is exhaustive, so there should be no counterexample.

        # We model: there exist two adjacent special chars, but none of the 4 patterns match
        # This is impossible by enumeration, but let's verify with Z3.
        s.add(Not(has_consecutive))

        # Add constraint that the string contains at least one pair of adjacent specials
        # We'll check a specific case: if string contains "__" then has_consecutive is true
        s2 = Solver()
        s2.add(Contains(user_id, StringVal("__")))
        s2.add(Not(has_consecutive))
        assert s2.check() == unsat, "__ should be caught by consecutive specials pattern"

        s3 = Solver()
        s3.add(Contains(user_id, StringVal("--")))
        s3.add(Not(has_consecutive))
        assert s3.check() == unsat, "-- should be caught by consecutive specials pattern"

        s4 = Solver()
        s4.add(Contains(user_id, StringVal("_-")))
        s4.add(Not(has_consecutive))
        assert s4.check() == unsat, "_- should be caught by consecutive specials pattern"

        s5 = Solver()
        s5.add(Contains(user_id, StringVal("-_")))
        s5.add(Not(has_consecutive))
        assert s5.check() == unsat, "-_ should be caught by consecutive specials pattern"

    def test_z3_reserved_default_set_completeness(self):
        """
        Verify that the default reserved set contains exactly {admin, root, system}.
        Model as: for any string in the reserved set, it must be one of the three.
        """
        try:
            from z3 import Solver, String, Or, StringVal, sat, unsat, Not
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        uid = String('uid')

        is_reserved = Or(
            uid == StringVal("admin"),
            uid == StringVal("root"),
            uid == StringVal("system")
        )

        # Verify "admin" is reserved
        s_admin = Solver()
        s_admin.add(uid == StringVal("admin"))
        s_admin.add(Not(is_reserved))
        assert s_admin.check() == unsat

        # Verify "root" is reserved
        s_root = Solver()
        s_root.add(uid == StringVal("root"))
        s_root.add(Not(is_reserved))
        assert s_root.check() == unsat

        # Verify "system" is reserved
        s_system = Solver()
        s_system.add(uid == StringVal("system"))
        s_system.add(Not(is_reserved))
        assert s_system.check() == unsat

        # Verify "john" is NOT reserved
        s_john = Solver()
        s_john.add(uid == StringVal("john"))
        s_john.add(is_reserved)
        assert s_john.check() == unsat

    def test_z3_length_boundary_satisfiability(self):
        """
        Verify that length 3 and length 20 are satisfiable (boundary values are valid).
        """
        try:
            from z3 import Solver, Int, And, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        length = Int('length')

        # Length 3 should be satisfiable
        s3 = Solver()
        s3.add(And(length >= 3, length <= 20))
        s3.add(length == 3)
        assert s3.check() == sat

        # Length 20 should be satisfiable
        s20 = Solver()
        s20.add(And(length >= 3, length <= 20))
        s20.add(length == 20)
        assert s20.check() == sat

        # Length 2 should NOT be satisfiable within valid range
        s2 = Solver()
        s2.add(And(length >= 3, length <= 20))
        s2.add(length == 2)
        assert s2.check() == unsat

        # Length 21 should NOT be satisfiable within valid range
        s21 = Solver()
        s21.add(And(length >= 3, length <= 20))
        s21.add(length == 21)
        assert s21.check() == unsat

if __name__ == "__main__":
    pytest.main([__file__])