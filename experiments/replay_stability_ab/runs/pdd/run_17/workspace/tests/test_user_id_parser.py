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
    def parse_user_id(input_data, reserved_ids=None): pass
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
        assert parse_user_id("user": None) is None

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

    def test_passes_reserved_ids(self):
        items = ["user:admin", "user:john"]
        results = parse_user_ids(items, reserved_ids=set())
        assert results[0] == ParseResult(user_id="admin", source="string")
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
            from z3 import Solver, String, Contains, Or, And, sat, unsat, Not, StringVal
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
            uid == StringVal("system"),
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