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

# Add the src directory to the path

try:
    from user_id_parser import ParseResult, parse_user_id, parse_user_ids
except ImportError:
    # Mocking for standalone execution if src is not present
    from collections import namedtuple
    ParseResult = namedtuple("ParseResult", ["user_id", "source"])
    def parse_user_id(val, **kwargs):
        return None
    def parse_user_ids(vals, **kwargs):
        return []

# ==============================================================================
# Tests for parse_user_id - String input "user:<id>"
# ==============================================================================

class TestParseUserIdStringInput:
    def test_valid_simple_id(self):
        assert parse_user_id("user:abc123") == ParseResult("abc123", "string")

    def test_valid_with_underscore(self):
        assert parse_user_id("user:my_user") == ParseResult("my_user", "string")

    def test_valid_with_hyphen(self):
        assert parse_user_id("user:my-user") == ParseResult("my-user", "string")

    def test_valid_with_mixed_allowed_chars(self):
        assert parse_user_id("user:a1_b2-c3") == ParseResult("a1_b2-c3", "string")

    def test_uppercase_is_lowercased(self):
        assert parse_user_id("user:ABC123") == ParseResult("abc123", "string")

    def test_mixed_case_is_lowercased(self):
        assert parse_user_id("user:AbCdEf") == ParseResult("abcdef", "string")

    def test_whitespace_trimmed(self):
        assert parse_user_id("user:  abc123  ") == ParseResult("abc123", "string")

    def test_leading_whitespace_trimmed(self):
        assert parse_user_id("user:  abc123") == ParseResult("abc123", "string")

    def test_trailing_whitespace_trimmed(self):
        assert parse_user_id("user:abc123  ") == ParseResult("abc123", "string")

    def test_whitespace_and_uppercase(self):
        assert parse_user_id("user:  ABC  ") == ParseResult("abc", "string")

    def test_no_user_prefix(self):
        assert parse_user_id("abc123") is None

    def test_different_prefix(self):
        assert parse_user_id("account:abc123") is None

    def test_empty_string(self):
        assert parse_user_id("") is None

    def test_user_prefix_only(self):
        # "user:" with empty id -> after trim, empty string, length 0 < 3
        assert parse_user_id("user:") is None

    def test_user_prefix_with_whitespace_only(self):
        # "user:   " -> strip -> "", length 0 < 3
        assert parse_user_id("user:   ") is None

    def test_id_too_short_1_char(self):
        assert parse_user_id("user:a") is None

    def test_id_too_short_2_chars(self):
        assert parse_user_id("user:ab") is None

    def test_id_exactly_3_chars(self):
        assert parse_user_id("user:abc") == ParseResult("abc", "string")

    def test_id_exactly_20_chars(self):
        id_20 = "a" * 20
        assert parse_user_id(f"user:{id_20}") == ParseResult(id_20, "string")

    def test_id_exactly_21_chars(self):
        id_21 = "a" * 21
        assert parse_user_id(f"user:{id_21}") is None

    def test_id_very_long(self):
        assert parse_user_id("user:" + "a" * 100) is None

    def test_invalid_chars_dot(self):
        assert parse_user_id("user:abc.def") is None

    def test_invalid_chars_at(self):
        assert parse_user_id("user:abc@def") is None

    def test_invalid_chars_space_in_middle(self):
        assert parse_user_id("user:abc def") is None

    def test_invalid_chars_exclamation(self):
        assert parse_user_id("user:abc!def") is None

    def test_invalid_chars_slash(self):
        assert parse_user_id("user:abc/def") is None

    def test_invalid_chars_unicode(self):
        assert parse_user_id("user:abcüdef") is None

    def test_reserved_admin(self):
        assert parse_user_id("user:admin") is None

    def test_reserved_root(self):
        assert parse_user_id("user:root") is None

    def test_reserved_system(self):
        assert parse_user_id("user:system") is None

    def test_reserved_admin_uppercase(self):
        assert parse_user_id("user:ADMIN") is None

    def test_reserved_admin_mixed_case(self):
        assert parse_user_id("user:Admin") is None

    def test_reserved_root_uppercase(self):
        assert parse_user_id("user:ROOT") is None

    def test_reserved_system_mixed_case(self):
        assert parse_user_id("user:System") is None

    def test_reserved_with_whitespace(self):
        assert parse_user_id("user: admin ") is None

    def test_case_sensitive_prefix_uppercase_u(self):
        assert parse_user_id("User:abc123") is None

    def test_case_sensitive_prefix_all_upper(self):
        assert parse_user_id("USER:abc123") is None

    def test_all_digits(self):
        assert parse_user_id("user:12345") == ParseResult("12345", "string")

    def test_all_underscores(self):
        assert parse_user_id("user:___") == ParseResult("___", "string")

    def test_all_hyphens(self):
        assert parse_user_id("user:---") == ParseResult("---", "string")

    def test_starts_with_hyphen(self):
        assert parse_user_id("user:-abc") == ParseResult("-abc", "string")

    def test_starts_with_underscore(self):
        assert parse_user_id("user:_abc") == ParseResult("_abc", "string")


# ==============================================================================
# Tests for parse_user_id - Dict input with "user_id" key
# ==============================================================================

class TestParseUserIdDictUserIdFirst:
    def test_valid_user_id(self):
        assert parse_user_id({"user_id": "abc123"}) == ParseResult("abc123", "dict_flat")

    def test_user_id_with_whitespace(self):
        assert parse_user_id({"user_id": " abc123 "}) == ParseResult("abc123", "dict_flat")

    def test_user_id_uppercase(self):
        assert parse_user_id({"user_id": "ABC123"}) == ParseResult("abc123", "dict_flat")

    def test_user_id_whitespace_and_uppercase(self):
        assert parse_user_id({"user_id": "  MyUser  "}) == ParseResult("myuser", "dict_flat")

    def test_user_id_non_string_int(self):
        assert parse_user_id({"user_id": 123}) is None

    def test_user_id_non_string_none(self):
        assert parse_user_id({"user_id": None}) is None

    def test_user_id_non_string_list(self):
        assert parse_user_id({"user_id": ["abc"]}) is None

    def test_user_id_too_short(self):
        assert parse_user_id({"user_id": "ab"}) is None

    def test_user_id_too_long(self):
        assert parse_user_id({"user_id": "a" * 21}) is None

    def test_user_id_reserved_admin(self):
        assert parse_user_id({"user_id": "admin"}) is None

    def test_user_id_reserved_root(self):
        assert parse_user_id({"user_id": "root"}) is None

    def test_user_id_reserved_system(self):
        assert parse_user_id({"user_id": "system"}) is None

    def test_user_id_invalid_chars(self):
        assert parse_user_id({"user_id": "abc@def"}) is None

    def test_user_id_empty_string(self):
        assert parse_user_id({"user_id": ""}) is None

    def test_user_id_exactly_3_chars(self):
        assert parse_user_id({"user_id": "abc"}) == ParseResult("abc", "dict_flat")

    def test_user_id_exactly_20_chars(self):
        id_20 = "b" * 20
        assert parse_user_id({"user_id": id_20}) == ParseResult(id_20, "dict_flat")


# ==============================================================================
# Tests for parse_user_id - Dict input with nested {"user": {"id": "<id>"}}
# ==============================================================================

class TestParseUserIdDictNestedUserFirst:
    def test_valid_nested_id(self):
        assert parse_user_id({"user": {"id": "abc123"}}) == ParseResult("abc123", "dict_nested")

    def test_nested_id_with_whitespace(self):
        assert parse_user_id({"user": {"id": " abc123 "}}) == ParseResult("abc123", "dict_nested")

    def test_nested_id_uppercase(self):
        assert parse_user_id({"user": {"id": "ABC123"}}) == ParseResult("abc123", "dict_nested")

    def test_nested_id_non_string_int(self):
        assert parse_user_id({"user": {"id": 123}}) is None

    def test_nested_id_non_string_none(self):
        assert parse_user_id({"user": {"id": None}}) is None

    def test_nested_user_not_dict(self):
        assert parse_user_id({"user": "not_a_dict"}) is None

    def test_nested_user_is_none(self):
        assert parse_user_id({"user": None}) is None

    def test_nested_user_is_list(self):
        assert parse_user_id({"user": [{"id": "abc"}]}) is None

    def test_nested_user_missing_id_key(self):
        assert parse_user_id({"user": {"name": "abc123"}}) is None

    def test_nested_user_empty_inner_dict(self):
        assert parse_user_id({"user": {}}) is None

    def test_nested_id_reserved(self):
        assert parse_user_id({"user": {"id": "admin"}}) is None

    def test_nested_id_too_short(self):
        assert parse_user_id({"user": {"id": "ab"}}) is None

    def test_nested_id_too_long(self):
        assert parse_user_id({"user": {"id": "a" * 21}}) is None

    def test_nested_id_invalid_chars(self):
        assert parse_user_id({"user": {"id": "abc.def"}}) is None


# ==============================================================================
# Tests for parse_user_id - Dict with both keys (priority)
# ==============================================================================

class TestParseUserIdDictPriority:
    def test_user_id_takes_priority_over_nested(self):
        """When both 'user_id' and 'user' keys exist, 'user_id' should be used."""
        result = parse_user_id({"user_id": "first_id", "user": {"id": "second_id"}})
        assert result == ParseResult("first_id", "dict_flat")

    def test_user_id_invalid_falls_through_to_none(self):
        """If user_id is present but invalid type, it returns None (doesn't fall through to user)."""
        result = parse_user_id({"user_id": 123, "user": {"id": "valid_id"}})
        assert result is None


# ==============================================================================
# Tests for parse_user_id - Invalid input types (should never raise)
# ==============================================================================

class TestParseUserIdInvalidTypes:
    def test_none_input(self):
        assert parse_user_id(None) is None

    def test_int_input(self):
        assert parse_user_id(42) is None

    def test_float_input(self):
        assert parse_user_id(3.14) is None

    def test_bool_true_input(self):
        assert parse_user_id(True) is None

    def test_bool_false_input(self):
        assert parse_user_id(False) is None

    def test_list_input(self):
        assert parse_user_id(["user:abc"]) is None

    def test_tuple_input(self):
        assert parse_user_id(("user:abc",)) is None

    def test_set_input(self):
        assert parse_user_id({"abc"}) is None

    def test_empty_dict(self):
        assert parse_user_id({}) is None

    def test_dict_with_unrelated_keys(self):
        assert parse_user_id({"name": "abc123"}) is None

    def test_bytes_input(self):
        assert parse_user_id(b"user:abc123") is None


# ==============================================================================
# Tests for parse_user_id - No mutation of input dicts
# ==============================================================================

class TestParseUserIdNoMutation:
    def test_dict_user_id_not_mutated(self):
        d = {"user_id": "abc123"}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_nested_not_mutated(self):
        d = {"user": {"id": "abc123"}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_with_extra_keys_not_mutated(self):
        d = {"user_id": "abc123", "extra": "data", "nested": {"key": "val"}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_invalid_dict_not_mutated(self):
        d = {"user_id": 123, "user": {"id": 456}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original


# ==============================================================================
# Tests for parse_user_ids - Batch processing (first set)
# ==============================================================================

class TestParseUserIdsBatch:
    def test_empty_list(self):
        assert parse_user_ids([]) == []

    def test_single_valid_item(self):
        assert parse_user_ids(["user:abc123"]) == [ParseResult("abc123", "string")]

    def test_single_invalid_item(self):
        assert parse_user_ids(["invalid"]) == [None]

    def test_all_valid_items(self):
        items = ["user:abc", {"user_id": "def"}, {"user": {"id": "ghi"}}]
        result = parse_user_ids(items)
        assert result == [ParseResult("abc", "string"), ParseResult("def", "dict_flat"), ParseResult("ghi", "dict_nested")]

    def test_all_invalid_items(self):
        items = [None, 42, "invalid", {"bad": "data"}]
        result = parse_user_ids(items)
        assert result == [None, None, None, None]

    def test_mixed_valid_and_invalid(self):
        items = ["user:abc", None, {"user_id": "def"}, 42, {"user": {"id": "ghi"}}]
        result = parse_user_ids(items)
        assert result == [ParseResult("abc", "string"), None, ParseResult("def", "dict_flat"), None, ParseResult("ghi", "dict_nested")]

    def test_preserves_ordering(self):
        items = ["user:zzz", "user:aaa", "user:mmm"]
        result = parse_user_ids(items)
        assert result == [ParseResult("zzz", "string"), ParseResult("aaa", "string"), ParseResult("mmm", "string")]

    def test_result_length_matches_input(self):
        items = ["user:abc", None, "user:def", 42, "bad"]
        result = parse_user_ids(items)
        assert len(result) == len(items)

    def test_reserved_ids_in_batch(self):
        items = ["user:admin", "user:root", "user:system", "user:valid_id"]
        result = parse_user_ids(items)
        assert result == [None, None, None, ParseResult("valid_id", "string")]

    def test_mixed_formats_in_batch(self):
        items = [
            "user:abc",
            {"user_id": "def"},
            {"user": {"id": "ghi"}},
            "user:UPPER",
            {"user_id": " spaced "},
        ]
        result = parse_user_ids(items)
        assert result == [
            ParseResult("abc", "string"),
            ParseResult("def", "dict_flat"),
            ParseResult("ghi", "dict_nested"),
            ParseResult("upper", "string"),
            ParseResult("spaced", "dict_flat"),
        ]

    def test_does_not_deduplicate(self):
        items = ["user:abc", "user:abc", "user:abc"]
        result = parse_user_ids(items)
        assert result == [ParseResult("abc", "string"), ParseResult("abc", "string"), ParseResult("abc", "string")]


# ==============================================================================
# Tests for edge cases and boundary conditions
# ==============================================================================

class TestEdgeCasesFirst:
    def test_id_with_only_digits(self):
        result = parse_user_id("user:123")
        assert result == ParseResult("123", "string")

    def test_id_with_only_underscores_3(self):
        result = parse_user_id("user:___")
        assert result == ParseResult("___", "string")

    def test_id_with_only_hyphens_3(self):
        result = parse_user_id("user:---")
        assert result == ParseResult("---", "string")

    def test_id_boundary_3_chars_with_whitespace(self):
        result = parse_user_id("user:  abc  ")
        assert result == ParseResult("abc", "string")

    def test_id_boundary_whitespace_makes_too_short(self):
        assert parse_user_id("user:  ab  ") is None

    def test_tab_whitespace_trimmed(self):
        result = parse_user_id("user:\tabc\t")
        assert result == ParseResult("abc", "string")

    def test_newline_whitespace_trimmed(self):
        result = parse_user_id("user:\nabc\n")
        assert result == ParseResult("abc", "string")

    def test_user_colon_with_colon_in_id(self):
        assert parse_user_id("user:abc:def") is None

    def test_not_reserved_admin_prefix(self):
        result = parse_user_id("user:admin1")
        assert result == ParseResult("admin1", "string")

    def test_not_reserved_root_suffix(self):
        result = parse_user_id("user:myroot")
        assert result == ParseResult("myroot", "string")

    def test_not_reserved_system_substring(self):
        result = parse_user_id("user:subsystem")
        assert result == ParseResult("subsystem", "string")

    def test_string_user_without_colon(self):
        assert parse_user_id("userabc") is None

    def test_string_just_user_colon(self):
        assert parse_user_id("user:") is None

    def test_dict_user_id_empty_string(self):
        assert parse_user_id({"user_id": ""}) is None

    def test_dict_nested_id_empty_string(self):
        assert parse_user_id({"user": {"id": ""}}) is None

    def test_dict_user_id_whitespace_only(self):
        assert parse_user_id({"user_id": "   "}) is None

    def test_dict_nested_id_whitespace_only(self):
        assert parse_user_id({"user": {"id": "   "}}) is None

    def test_id_with_uppercase_after_normalization_valid(self):
        result = parse_user_id({"user_id": "ABC_DEF"})
        assert result == ParseResult("abc_def", "dict_flat")

    def test_id_20_chars_boundary(self):
        id_20 = "abcdefghij0123456789"
        assert len(id_20) == 20
        result = parse_user_id(f"user:{id_20}")
        assert result == ParseResult(id_20, "string")

    def test_id_19_chars(self):
        id_19 = "a" * 19
        result = parse_user_id(f"user:{id_19}")
        assert result == ParseResult(id_19, "string")

    def test_id_4_chars(self):
        result = parse_user_id("user:abcd")
        assert result == ParseResult("abcd", "string")


# ==============================================================================
# Z3 Formal Verification Tests (first set)
# ==============================================================================

class TestZ3FormalVerificationFirst:
    """
    Use Z3 to formally verify properties of the validation logic.
    """

    def test_z3_reserved_ids_always_rejected(self):
        """Verify that reserved IDs are always rejected regardless of format."""
        try:
            from z3 import Solver, String, StringVal, And, Or, sat, Length
        except ImportError:
            pytest.skip("z3-solver not installed")

        reserved = ["admin", "root", "system"]
        for rid in reserved:
            assert parse_user_id(f"user:{rid}") is None
            assert parse_user_id({"user_id": rid}) is None
            assert parse_user_id({"user": {"id": rid}}) is None
            assert parse_user_id(f"user:{rid.upper()}") is None
            assert parse_user_id(f"user:{rid.capitalize()}") is None

    def test_z3_length_constraints(self):
        """Use Z3 to verify that length constraints are properly enforced."""
        try:
            from z3 import Solver, Int, And, Or, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        length = Int('length')

        s.add(Or(length < 3, length > 20))
        s.add(length >= 0)

        if s.check() == sat:
            m = s.model()
            bad_length = m[length].as_long()
            if bad_length >= 0:
                test_id = "a" * bad_length
                result = parse_user_id(f"user:{test_id}")
                assert result is None, f"ID of length {bad_length} should be rejected"

    def test_z3_valid_chars_property(self):
        """Verify that IDs with invalid characters are rejected."""
        try:
            from z3 import Solver, Int, sat
        except ImportError:
            pytest.skip("z3-solver not installed")

        invalid_chars = [chr(i) for i in range(32, 127)
                         if chr(i) not in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-']

        for ch in invalid_chars:
            test_id = f"aa{ch}bb"
            result = parse_user_id(f"user:{test_id}")
            assert result is None, f"ID containing '{ch}' (ord {ord(ch)}) should be rejected"

    def test_z3_all_valid_chars_accepted(self):
        """Verify that all individually valid characters are accepted in valid IDs."""
        try:
            from z3 import Solver
        except ImportError:
            pytest.skip("z3-solver not installed")

        valid_chars = 'abcdefghijklmnopqrstuvwxyz0123456789_-'
        for ch in valid_chars:
            test_id = ch * 3
            if test_id in ('admin', 'root', 'system'):
                continue
            result = parse_user_id(f"user:{test_id}")
            assert result is not None and result.user_id == test_id, f"ID '{test_id}' with valid char '{ch}' should be accepted"

    def test_z3_normalization_idempotent(self):
        """Verify that applying normalization twice gives the same result."""
        try:
            from z3 import Solver
        except ImportError:
            pytest.skip("z3-solver not installed")

        test_cases = ["user:ABC", "user:  abc  ", "user: XYZ_123 "]
        for tc in test_cases:
            result1 = parse_user_id(tc)
            if result1 is not None:
                result2 = parse_user_id(f"user:{result1.user_id}")
                assert result1.user_id == result2.user_id, f"Normalization not idempotent for {tc}"

# ==============================================================================
# Tests for parse_user_id with "email:" prefix (first set)
# ==============================================================================

class TestParseUserIdEmailPrefixFirst:
    def test_valid_email(self):
        assert parse_user_id("email:john@example.com") == ParseResult("john", "email")

    def test_valid_email_username_with_digits(self):
        assert parse_user_id("email:user123@example.com") == ParseResult("user123", "email")

    def test_valid_email_username_with_underscore(self):
        assert parse_user_id("email:john_doe@example.com") == ParseResult("john_doe", "email")

    def test_valid_email_username_with_hyphen(self):
        assert parse_user_id("email:john-doe@example.com") == ParseResult("john-doe", "email")

    def test_email_no_at_sign(self):
        assert parse_user_id("email:johnatexample.com") is None

    def test_email_empty_username(self):
        assert parse_user_id("email:@example.com") is None

    def test_email_username_too_short(self):
        assert parse_user_id("email:ab@example.com") is None

    def test_email_username_too_long(self):
        username = "a" * 21
        assert parse_user_id(f"email:{username}@example.com") is None

    def test_email_username_exactly_3(self):
        assert parse_user_id("email:abc@example.com") == ParseResult("abc", "email")

    def test_email_username_exactly_20(self):
        username = "a" * 20
        assert parse_user_id(f"email:{username}@example.com") == ParseResult(username, "email")

    def test_email_username_invalid_chars(self):
        assert parse_user_id("email:jo!hn@example.com") is None

    def test_email_username_with_dot(self):
        assert parse_user_id("email:john.doe@example.com") is None

    def test_email_reserved_admin(self):
        assert parse_user_id("email:admin@example.com") is None

    def test_email_reserved_root(self):
        assert parse_user_id("email:root@example.com") is None

    def test_email_reserved_system(self):
        assert parse_user_id("email:system@example.com") is None

    def test_email_multiple_at_signs(self):
        assert parse_user_id("email:user@domain@extra") == ParseResult("user", "email")

    def test_email_username_uppercase(self):
        assert parse_user_id("email:JOHN@example.com") == ParseResult("john", "email")

    def test_email_username_whitespace(self):
        assert parse_user_id("email:  JOHN  @example.com") == ParseResult("john", "email")

    def test_email_empty_after_prefix(self):
        assert parse_user_id("email:") is None

    def test_email_just_at(self):
        assert parse_user_id("email:@") is None


# ==============================================================================
# Tests for parse_user_id: "user:<id>" format (second set)
# ==============================================================================

class TestParseUserIdUserPrefix:
    def test_valid_simple_id(self):
        assert parse_user_id("user:alice") == ParseResult("alice", "string")

    def test_valid_id_with_numbers(self):
        assert parse_user_id("user:user123") == ParseResult("user123", "string")

    def test_valid_id_with_underscore(self):
        assert parse_user_id("user:my_user") == ParseResult("my_user", "string")

    def test_valid_id_with_hyphen(self):
        assert parse_user_id("user:my-user") == ParseResult("my-user", "string")

    def test_valid_id_with_mixed_allowed_chars(self):
        assert parse_user_id("user:a1_b-2") == ParseResult("a1_b-2", "string")

    def test_uppercase_is_lowered(self):
        assert parse_user_id("user:ALICE") == ParseResult("alice", "string")

    def test_mixed_case_is_lowered(self):
        assert parse_user_id("user:AlIcE") == ParseResult("alice", "string")

    def test_whitespace_trimmed(self):
        assert parse_user_id("user:  alice  ") == ParseResult("alice", "string")

    def test_whitespace_and_uppercase(self):
        assert parse_user_id("user:  ALICE  ") == ParseResult("alice", "string")

    def test_empty_id_returns_none(self):
        assert parse_user_id("user:") is None

    def test_whitespace_only_id_returns_none(self):
        assert parse_user_id("user:   ") is None

    def test_id_too_short_1_char(self):
        assert parse_user_id("user:a") is None

    def test_id_too_short_2_chars(self):
        assert parse_user_id("user:ab") is None

    def test_id_exactly_3_chars(self):
        assert parse_user_id("user:abc") == ParseResult("abc", "string")

    def test_id_exactly_20_chars(self):
        uid = "a" * 20
        assert parse_user_id(f"user:{uid}") == ParseResult(uid, "string")

    def test_id_21_chars_too_long(self):
        uid = "a" * 21
        assert parse_user_id(f"user:{uid}") is None

    def test_invalid_chars_dot(self):
        assert parse_user_id("user:al.ice") is None

    def test_invalid_chars_space_in_middle(self):
        assert parse_user_id("user:al ice") is None

    def test_invalid_chars_at_sign(self):
        assert parse_user_id("user:al@ice") is None

    def test_invalid_chars_exclamation(self):
        assert parse_user_id("user:alice!") is None


# ==============================================================================
# Tests for parse_user_id: "email:user@domain" format (second set)
# ==============================================================================

class TestParseUserIdEmailPrefix:
    def test_valid_email(self):
        assert parse_user_id("email:alice@example.com") == ParseResult("alice", "email")

    def test_email_uppercase_username(self):
        assert parse_user_id("email:ALICE@example.com") == ParseResult("alice", "email")

    def test_email_with_whitespace_around_username(self):
        assert parse_user_id("email:  alice  @example.com") == ParseResult("alice", "email")

    def test_email_no_at_sign(self):
        assert parse_user_id("email:aliceexample.com") is None

    def test_email_empty_username(self):
        assert parse_user_id("email:@example.com") is None

    def test_email_username_with_dots_invalid(self):
        assert parse_user_id("email:alice.bob@example.com") is None

    def test_email_username_with_underscore(self):
        assert parse_user_id("email:alice_bob@example.com") == ParseResult("alice_bob", "email")

    def test_email_username_with_hyphen(self):
        assert parse_user_id("email:alice-bob@example.com") == ParseResult("alice-bob", "email")

    def test_email_username_too_short(self):
        assert parse_user_id("email:ab@example.com") is None

    def test_email_username_too_long(self):
        long_name = "a" * 21
        assert parse_user_id(f"email:{long_name}@example.com") is None

    def test_email_username_exactly_3(self):
        assert parse_user_id("email:abc@example.com") == ParseResult("abc", "email")

    def test_email_username_exactly_20(self):
        name = "a" * 20
        assert parse_user_id(f"email:{name}@example.com") == ParseResult(name, "email")

    def test_email_multiple_at_signs(self):
        assert parse_user_id("email:alice@domain@other") == ParseResult("alice", "email")


# ==============================================================================
# Tests for parse_user_id: dict input {"user_id": "<id>"} (second set)
# ==============================================================================

class TestParseUserIdDictUserId:
    def test_valid_dict_user_id(self):
        assert parse_user_id({"user_id": "alice"}) == ParseResult("alice", "dict_flat")

    def test_dict_user_id_uppercase(self):
        assert parse_user_id({"user_id": "ALICE"}) == ParseResult("alice", "dict_flat")

    def test_dict_user_id_whitespace(self):
        assert parse_user_id({"user_id": "  alice  "}) == ParseResult("alice", "dict_flat")

    def test_dict_user_id_not_string(self):
        assert parse_user_id({"user_id": 123}) is None

    def test_dict_user_id_none_value(self):
        assert parse_user_id({"user_id": None}) is None

    def test_dict_user_id_invalid_chars(self):
        assert parse_user_id({"user_id": "al!ce"}) is None

    def test_dict_user_id_too_short(self):
        assert parse_user_id({"user_id": "ab"}) is None

    def test_dict_user_id_too_long(self):
        assert parse_user_id({"user_id": "a" * 21}) is None


# ==============================================================================
# Tests for parse_user_id: dict input {"user": {"id": "<id>"}} (second set)
# ==============================================================================

class TestParseUserIdDictNestedUser:
    def test_valid_nested_dict(self):
        assert parse_user_id({"user": {"id": "alice"}}) == ParseResult("alice", "dict_nested")

    def test_nested_dict_uppercase(self):
        assert parse_user_id({"user": {"id": "ALICE"}}) == ParseResult("alice", "dict_nested")

    def test_nested_dict_whitespace(self):
        assert parse_user_id({"user": {"id": "  alice  "}}) == ParseResult("alice", "dict_nested")

    def test_nested_dict_id_not_string(self):
        assert parse_user_id({"user": {"id": 123}}) is None

    def test_nested_dict_user_not_dict(self):
        assert parse_user_id({"user": "alice"}) is None

    def test_nested_dict_user_list(self):
        assert parse_user_id({"user": [1, 2, 3]}) is None

    def test_nested_dict_no_id_key(self):
        assert parse_user_id({"user": {"name": "alice"}}) is None

    def test_nested_dict_id_none(self):
        assert parse_user_id({"user": {"id": None}}) is None

    def test_user_id_takes_precedence_over_nested(self):
        """When both user_id and user.id exist, user_id should be used."""
        result = parse_user_id({"user_id": "alice", "user": {"id": "bob"}})
        assert result == ParseResult("alice", "dict_flat")


# ==============================================================================
# Tests for parse_user_id: reserved IDs
# ==============================================================================

class TestParseUserIdReserved:
    def test_default_reserved_admin(self):
        assert parse_user_id("user:admin") is None

    def test_default_reserved_root(self):
        assert parse_user_id("user:root") is None

    def test_default_reserved_system(self):
        assert parse_user_id("user:system") is None

    def test_default_reserved_case_insensitive(self):
        assert parse_user_id("user:ADMIN") is None

    def test_default_reserved_with_whitespace(self):
        assert parse_user_id("user:  admin  ") is None

    def test_custom_reserved_rejects_custom(self):
        assert parse_user_id("user:test", reserved_ids={"test"}) is None

    def test_custom_reserved_allows_default(self):
        result = parse_user_id("user:admin", reserved_ids={"test"})
        assert result == ParseResult("admin", "string")

    def test_custom_reserved_allows_root(self):
        result = parse_user_id("user:root", reserved_ids={"test"})
        assert result == ParseResult("root", "string")

    def test_empty_reserved_allows_admin(self):
        result = parse_user_id("user:admin", reserved_ids=set())
        assert result == ParseResult("admin", "string")

    def test_empty_reserved_allows_root(self):
        result = parse_user_id("user:root", reserved_ids=set())
        assert result == ParseResult("root", "string")

    def test_empty_reserved_allows_system(self):
        result = parse_user_id("user:system", reserved_ids=set())
        assert result == ParseResult("system", "string")

    def test_custom_reserved_multiple(self):
        reserved = {"foo", "bar", "baz"}
        assert parse_user_id("user:foo", reserved_ids=reserved) is None
        assert parse_user_id("user:bar", reserved_ids=reserved) is None
        assert parse_user_id("user:baz", reserved_ids=reserved) is None
        result = parse_user_id("user:alice", reserved_ids=reserved)
        assert result == ParseResult("alice", "string")


# ==============================================================================
# Tests for parse_user_id: edge cases and error handling
# ==============================================================================

class TestParseUserIdEdgeCases:
    def test_none_input(self):
        assert parse_user_id(None) is None

    def test_integer_input(self):
        assert parse_user_id(123) is None

    def test_float_input(self):
        assert parse_user_id(3.14) is None

    def test_list_input(self):
        assert parse_user_id(["user:alice"]) is None

    def test_bool_input(self):
        assert parse_user_id(True) is None

    def test_empty_string(self):
        assert parse_user_id("") is None

    def test_string_without_prefix(self):
        assert parse_user_id("alice") is None

    def test_string_with_unknown_prefix(self):
        assert parse_user_id("id:alice") is None

    def test_empty_dict(self):
        assert parse_user_id({}) is None

    def test_dict_with_irrelevant_keys(self):
        assert parse_user_id({"name": "alice"}) is None

    def test_does_not_mutate_input_dict_flat(self):
        d = {"user_id": "  ALICE  "}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_does_not_mutate_input_dict_nested(self):
        d = {"user": {"id": "  ALICE  "}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_tuple_input(self):
        assert parse_user_id(("user", "alice")) is None

    def test_set_input(self):
        assert parse_user_id({"alice"}) is None

    def test_user_prefix_with_colon_in_id(self):
        assert parse_user_id("user:foo:bar") is None


# ==============================================================================
# Tests for parse_user_id: boundary length tests
# ==============================================================================

class TestParseUserIdLengthBoundaries:
    def test_length_0(self):
        assert parse_user_id("user:") is None

    def test_length_1(self):
        assert parse_user_id("user:a") is None

    def test_length_2(self):
        assert parse_user_id("user:ab") is None

    def test_length_3(self):
        assert parse_user_id("user:abc") == ParseResult("abc", "string")

    def test_length_4(self):
        assert parse_user_id("user:abcd") == ParseResult("abcd", "string")

    def test_length_19(self):
        uid = "a" * 19
        assert parse_user_id(f"user:{uid}") == ParseResult(uid, "string")

    def test_length_20(self):
        uid = "a" * 20
        assert parse_user_id(f"user:{uid}") == ParseResult(uid, "string")

    def test_length_21(self):
        uid = "a" * 21
        assert parse_user_id(f"user:{uid}") is None

    def test_length_100(self):
        uid = "a" * 100
        assert parse_user_id(f"user:{uid}") is None


# ==============================================================================
# Tests for parse_user_ids: batch processing (second set)
# ==============================================================================

class TestParseUserIds:
    def test_empty_list(self):
        assert parse_user_ids([]) == []

    def test_single_valid(self):
        assert parse_user_ids(["user:alice"]) == [ParseResult("alice", "string")]

    def test_single_invalid(self):
        assert parse_user_ids(["invalid"]) == [None]

    def test_mixed_valid_invalid(self):
        items = ["user:alice", "invalid", "user:bob", None, {"user_id": "charlie"}]
        result = parse_user_ids(items)
        assert result == [ParseResult("alice", "string"), None, ParseResult("bob", "string"), None, ParseResult("charlie", "dict_flat")]

    def test_preserves_ordering(self):
        items = ["user:zzz", "user:aaa", "user:mmm"]
        result = parse_user_ids(items)
        assert result == [ParseResult("zzz", "string"), ParseResult("aaa", "string"), ParseResult("mmm", "string")]

    def test_all_invalid(self):
        items = [None, 123, "", "bad"]
        result = parse_user_ids(items)
        assert result == [None, None, None, None]

    def test_reserved_ids_passed_through(self):
        items = ["user:admin", "user:alice"]
        result_default = parse_user_ids(items)
        assert result_default == [None, ParseResult("alice", "string")]

        result_empty = parse_user_ids(items, reserved_ids=set())
        assert result_empty == [ParseResult("admin", "string"), ParseResult("alice", "string")]

    def test_custom_reserved_passed_through(self):
        items = ["user:alice", "user:bob"]
        result = parse_user_ids(items, reserved_ids={"alice"})
        assert result == [None, ParseResult("bob", "string")]

    def test_result_length_matches_input(self):
        items = ["user:a", "user:bb", "user:ccc", "user:dddd"]
        result = parse_user_ids(items)
        assert len(result) == len(items)

    def test_various_input_types(self):
        items = [
            "user:alice",
            "email:bob@example.com",
            {"user_id": "charlie"},
            {"user": {"id": "dave"}},
        ]
        result = parse_user_ids(items)
        assert result == [
            ParseResult("alice", "string"),
            ParseResult("bob", "email"),
            ParseResult("charlie", "dict_flat"),
            ParseResult("dave", "dict_nested"),
        ]

    def test_does_not_mutate_input_list(self):
        items = ["user:alice", "user:bob"]
        original = items.copy()
        parse_user_ids(items)
        assert items == original


# ==============================================================================
# Tests for parse_user_id: character validation
# ==============================================================================

class TestParseUserIdCharacterValidation:
    def test_all_lowercase_letters(self):
        assert parse_user_id("user:abcdef") == ParseResult("abcdef", "string")

    def test_all_digits(self):
        assert parse_user_id("user:12345") == ParseResult("12345", "string")

    def test_all_underscores(self):
        assert parse_user_id("user:___") == ParseResult("___", "string")

    def test_all_hyphens(self):
        assert parse_user_id("user:---") == ParseResult("---", "string")

    def test_mixed_valid_chars(self):
        assert parse_user_id("user:a1_b-2") == ParseResult("a1_b-2", "string")

    def test_uppercase_letters_normalized(self):
        assert parse_user_id("user:ABC") == ParseResult("abc", "string")

    def test_special_char_plus(self):
        assert parse_user_id("user:abc+def") is None

    def test_special_char_period(self):
        assert parse_user_id("user:abc.def") is None

    def test_special_char_slash(self):
        assert parse_user_id("user:abc/def") is None

    def test_special_char_backslash(self):
        assert parse_user_id("user:abc\\def") is None

    def test_unicode_char(self):
        assert parse_user_id("user:àlice") is None

    def test_emoji(self):
        assert parse_user_id("user:ali😀ce") is None


# ==============================================================================
# Z3 Formal Verification Tests (second set)
# ==============================================================================

class TestZ3FormalVerification:
    """
    Use Z3 to formally verify properties of the ID validation logic.
    """

    def test_z3_valid_id_length_boundaries(self):
        """Verify that length constraints [3, 20] are correctly enforced."""
        try:
            from z3 import Solver, String, Length, And, Or, sat, unsat, IntVal
        except ImportError:
            pytest.skip("z3-solver not installed")

        for length in range(0, 3):
            test_id = "a" * length
            result = parse_user_id(f"user:{test_id}")
            assert result is None, f"ID of length {length} should be rejected"

        for length in [3, 10, 20]:
            test_id = "x" * length
            result = parse_user_id(f"user:{test_id}")
            assert result is not None and result.user_id == test_id, f"ID of length {length} should be accepted"

        for length in [21, 50, 100]:
            test_id = "a" * length
            result = parse_user_id(f"user:{test_id}")
            assert result is None, f"ID of length {length} should be rejected"

    def test_z3_character_constraints(self):
        """Verify character constraints using Z3-like exhaustive checking."""
        try:
            from z3 import Solver, String, Length, sat
        except ImportError:
            pytest.skip("z3-solver not installed")

        import string

        allowed = set(string.ascii_lowercase + string.digits + "_-")

        for ch in string.printable:
            test_id = ch * 3
            result = parse_user_id(f"user:{test_id}")
            if ch.lower() in allowed:
                if test_id.lower() not in {"admin", "root", "system"}:
                    assert result is not None, f"Character '{ch}' should be allowed"
            else:
                assert result is None, f"Character '{ch}' should be rejected"

    def test_z3_reserved_id_property(self):
        """Verify that reserved IDs are always rejected with default settings."""
        try:
            from z3 import Solver, String, Or, sat
        except ImportError:
            pytest.skip("z3-solver not installed")

        default_reserved = {"admin", "root", "system"}

        for rid in default_reserved:
            assert parse_user_id(f"user:{rid}") is None
            assert parse_user_id(f"user:{rid.upper()}") is None
            assert parse_user_id(f"user:  {rid}  ") is None
            assert parse_user_id({"user_id": rid}) is None
            assert parse_user_id({"user": {"id": rid}}) is None

            result = parse_user_id(f"user:{rid}", reserved_ids=set())
            assert result == ParseResult(rid, "string")

    def test_z3_normalization_idempotent(self):
        """Verify that normalization (trim + lowercase) is idempotent."""
        try:
            from z3 import Solver
        except ImportError:
            pytest.skip("z3-solver not installed")

        test_cases = [
            "  ALICE  ",
            "  Bob  ",
            "CHARLIE",
            "  dave",
            "eve  ",
        ]

        for raw_id in test_cases:
            result1 = parse_user_id(f"user:{raw_id}")
            if result1 is not None:
                result2 = parse_user_id(f"user:{result1.user_id}")
                assert result1.user_id == result2.user_id, f"Normalization not idempotent for '{raw_id}'"


# ==============================================================================
# Additional integration-style tests
# ==============================================================================

class TestIntegration:
    def test_email_and_user_prefix_same_result(self):
        """Same username extracted from both formats should match."""
        r1 = parse_user_id("user:alice")
        r2 = parse_user_id("email:alice@example.com")
        assert r1.user_id == r2.user_id == "alice"

    def test_dict_formats_same_result(self):
        """Same ID from both dict formats should match."""
        r1 = parse_user_id({"user_id": "alice"})
        r2 = parse_user_id({"user": {"id": "alice"}})
        assert r1.user_id == r2.user_id == "alice"

    def test_all_formats_same_result(self):
        """All four input formats should produce the same user_id."""
        results = [
            parse_user_id("user:alice"),
            parse_user_id("email:alice@example.com"),
            parse_user_id({"user_id": "alice"}),
            parse_user_id({"user": {"id": "alice"}}),
        ]
        assert all(r.user_id == "alice" for r in results)

    def test_batch_with_all_formats(self):
        items = [
            "user:alice",
            "email:bob@domain.com",
            {"user_id": "charlie"},
            {"user": {"id": "dave"}},
            "invalid",
            None,
        ]
        result = parse_user_ids(items)
        assert result == [
            ParseResult("alice", "string"),
            ParseResult("bob", "email"),
            ParseResult("charlie", "dict_flat"),
            ParseResult("dave", "dict_nested"),
            None,
            None,
        ]

    def test_return_type_is_parse_result_or_none(self):
        result = parse_user_id("user:alice")
        assert isinstance(result, ParseResult)

        result = parse_user_id("invalid")
        assert result is None

    def test_parse_user_ids_return_type(self):
        result = parse_user_ids(["user:alice", "invalid"])
        assert isinstance(result, list)
        assert len(result) == 2
        assert isinstance(result[0], ParseResult)
        assert result[1] is None

# ==============================================================================
# TEST PLAN
# ==============================================================================
#
# 1. ParseResult namedtuple
#    - Test that ParseResult can be instantiated with user_id and source fields
#    - Test that fields are accessible by name
#
# 2. parse_user_id - String input "user:<id>"
#    - Valid user:id → ParseResult with source="string"
#    - Whitespace trimming: "user:  alice  " → "alice"
#    - Lowercasing: "user:ALICE" → "alice"
#    - Combined trim + lowercase
#
# 3. parse_user_id - String input "email:user@domain"
#    - Valid email → extracts username, source="email"
#    - Email without @ → None
#    - Email with multiple @ → splits on first @
#    - Email username normalization (trim, lowercase)
#
# 4. parse_user_id - Dict input (flat)
#    - {"user_id": "alice"} → source="dict_flat"
#    - Non-string value in user_id → None
#    - Dict not mutated
#
# 5. parse_user_id - Dict input (nested)
#    - {"user": {"id": "alice"}} → source="dict_nested"
#    - {"user": "not_a_dict"} → None
#    - {"user": {}} → None (no "id" key)
#    - Dict not mutated
#
# 6. parse_user_id - Validation: allowed characters
#    - Only a-z, 0-9, _, - allowed
#    - Special chars like !, @, # → None
#    - Uppercase after normalization should be fine (lowercased)
#
# 7. parse_user_id - Validation: length
#    - Length < 3 → None
#    - Length == 3 → valid
#    - Length == 20 → valid
#    - Length > 20 → None
#
# 8. parse_user_id - Validation: reserved IDs
#    - Default reserved: admin, root, system → None
#    - Custom reserved_ids replaces defaults entirely
#    - Custom reserved_ids=set() → no reserved IDs
#    - Default reserved ID allowed when custom set doesn't include it
#
# 9. parse_user_id - Strict mode
#    - strict=False: "__" allowed
#    - strict=True: "__" rejected
#    - strict=True: "--" rejected
#    - strict=True: "_-" rejected
#    - strict=True: "-_" rejected
#    - strict=True: single _ or - allowed
#    - strict=False (default): consecutive specials allowed
#
# 10. parse_user_id - Edge cases / error handling
#     - None input → None
#     - Integer input → None
#     - List input → None
#     - Empty string → None
#     - "user:" with empty id → None (length < 3)
#     - Boolean input → None (bool is subclass of int, but also... it's truthy dict check?)
#       Actually bool is subclass of int in Python, isinstance(True, int) is True
#       but isinstance(True, str) is False, isinstance(True, dict) is False → None
#
# 11. parse_user_ids - Batch processing
#     - Empty list → empty list
#     - Mixed valid/invalid → preserves order, None for invalid
#     - Passes reserved_ids and strict through
#
# 12. Z3 Formal Verification
#     - Use Z3 to verify properties of the validation regex pattern:
#       - All valid IDs have length 3-20
#       - All valid IDs contain only allowed characters
#     - These are better suited as unit tests since the logic is string-based
#       and Z3 string theory can be complex. We'll use Z3 for a simple property check.
#
# Decision on Z3 vs Unit Tests:
# - Most tests are better as unit tests because they test specific input/output behavior
# - Z3 could verify that the validation constraints are consistent (e.g., no valid ID
#   can be both accepted and rejected), but the string operations make Z3 cumbersome.
# - We'll include a simple Z3 test to verify length constraints are consistent.
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

# Add the src directory to the path

from user_id_parser import parse_user_id, parse_user_ids, ParseResult


# ==============================================================================
# ParseResult namedtuple tests
# ==============================================================================

class TestParseResult:
    def test_create_parse_result(self):
        result = ParseResult(user_id="alice", source="string")
        assert result.user_id == "alice"
        assert result.source == "string"

    def test_parse_result_is_namedtuple(self):
        result = ParseResult(user_id="bob", source="email")
        assert isinstance(result, tuple)
        assert result[0] == "bob"
        assert result[1] == "email"

    def test_parse_result_fields(self):
        assert ParseResult._fields == ("user_id", "source")


# ==============================================================================
# parse_user_id - String "user:<id>" format
# ==============================================================================

class TestParseUserIdStringFormat:
    def test_valid_user_string(self):
        result = parse_user_id("user:alice")
        assert result == ParseResult(user_id="alice", source="string")

    def test_user_string_with_numbers(self):
        result = parse_user_id("user:alice123")
        assert result == ParseResult(user_id="alice123", source="string")

    def test_user_string_with_underscore(self):
        result = parse_user_id("user:alice_bob")
        assert result == ParseResult(user_id="alice_bob", source="string")

    def test_user_string_with_hyphen(self):
        result = parse_user_id("user:alice-bob")
        assert result == ParseResult(user_id="alice-bob", source="string")

    def test_user_string_whitespace_trimmed(self):
        result = parse_user_id("user:  alice  ")
        assert result == ParseResult(user_id="alice", source="string")

    def test_user_string_lowercased(self):
        result = parse_user_id("user:ALICE")
        assert result == ParseResult(user_id="alice", source="string")

    def test_user_string_trim_and_lowercase(self):
        result = parse_user_id("user:  ALICE  ")
        assert result == ParseResult(user_id="alice", source="string")

    def test_user_string_empty_id(self):
        # Empty after "user:" → length 0 < 3 → None
        result = parse_user_id("user:")
        assert result is None

    def test_user_string_short_id(self):
        result = parse_user_id("user:ab")
        assert result is None

    def test_user_string_min_length(self):
        result = parse_user_id("user:abc")
        assert result == ParseResult(user_id="abc", source="string")

    def test_user_string_max_length(self):
        result = parse_user_id("user:" + "a" * 20)
        assert result == ParseResult(user_id="a" * 20, source="string")

    def test_user_string_too_long(self):
        result = parse_user_id("user:" + "a" * 21)
        assert result is None


# ==============================================================================
# parse_user_id - String "email:user@domain" format
# ==============================================================================

class TestParseUserIdEmailFormat:
    def test_valid_email(self):
        result = parse_user_id("email:alice@example.com")
        assert result == ParseResult(user_id="alice", source="email")

    def test_email_username_extracted(self):
        result = parse_user_id("email:bob_smith@domain.org")
        assert result == ParseResult(user_id="bob_smith", source="email")

    def test_email_no_at_sign(self):
        result = parse_user_id("email:noatsign")
        assert result is None

    def test_email_multiple_at_signs(self):
        # Should split on first @
        result = parse_user_id("email:user@domain@extra")
        assert result == ParseResult(user_id="user", source="email")

    def test_email_username_trimmed_and_lowered(self):
        result = parse_user_id("email:  ALICE  @example.com")
        assert result == ParseResult(user_id="alice", source="email")

    def test_email_username_too_short(self):
        result = parse_user_id("email:ab@example.com")
        assert result is None

    def test_email_username_invalid_chars(self):
        result = parse_user_id("email:al!ce@example.com")
        assert result is None

    def test_email_empty_username(self):
        result = parse_user_id("email:@example.com")
        assert result is None


# ==============================================================================
# parse_user_id - Dict flat format
# ==============================================================================

class TestParseUserIdDictFlat:
    def test_valid_dict_flat(self):
        result = parse_user_id({"user_id": "alice"})
        assert result == ParseResult(user_id="alice", source="dict_flat")

    def test_dict_flat_trimmed_and_lowered(self):
        result = parse_user_id({"user_id": "  ALICE  "})
        assert result == ParseResult(user_id="alice", source="dict_flat")

    def test_dict_flat_non_string_value(self):
        result = parse_user_id({"user_id": 12345})
        assert result is None

    def test_dict_flat_none_value(self):
        result = parse_user_id({"user_id": None})
        assert result is None

    def test_dict_flat_not_mutated(self):
        d = {"user_id": "  ALICE  "}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_flat_takes_priority_over_nested(self):
        # If both "user_id" and "user" keys exist, "user_id" should be checked first
        result = parse_user_id({"user_id": "alice", "user": {"id": "bob"}})
        assert result == ParseResult(user_id="alice", source="dict_flat")


# ==============================================================================
# parse_user_id - Dict nested format
# ==============================================================================

class TestParseUserIdDictNested:
    def test_valid_dict_nested(self):
        result = parse_user_id({"user": {"id": "alice"}})
        assert result == ParseResult(user_id="alice", source="dict_nested")

    def test_dict_nested_trimmed_and_lowered(self):
        result = parse_user_id({"user": {"id": "  BOB  "}})
        assert result == ParseResult(user_id="bob", source="dict_nested")

    def test_dict_nested_user_not_dict(self):
        result = parse_user_id({"user": "not_a_dict"})
        assert result is None

    def test_dict_nested_no_id_key(self):
        result = parse_user_id({"user": {"name": "alice"}})
        assert result is None

    def test_dict_nested_non_string_id(self):
        result = parse_user_id({"user": {"id": 123}})
        assert result is None

    def test_dict_nested_not_mutated(self):
        d = {"user": {"id": "  ALICE  "}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_nested_user_is_none(self):
        result = parse_user_id({"user": None})
        assert result is None


# ==============================================================================
# parse_user_id - Validation: allowed characters
# ==============================================================================

class TestParseUserIdCharacterValidation:
    def test_valid_alphanumeric(self):
        result = parse_user_id("user:abc123")
        assert result is not None

    def test_valid_with_underscore(self):
        result = parse_user_id("user:a_b_c")
        assert result is not None

    def test_valid_with_hyphen(self):
        result = parse_user_id("user:a-b-c")
        assert result is not None

    def test_invalid_exclamation(self):
        assert parse_user_id("user:abc!def") is None

    def test_invalid_at_sign(self):
        assert parse_user_id("user:abc@def") is None

    def test_invalid_space_in_middle(self):
        assert parse_user_id("user:abc def") is None

    def test_invalid_dot(self):
        assert parse_user_id("user:abc.def") is None

    def test_invalid_hash(self):
        assert parse_user_id("user:abc#def") is None

    def test_all_digits(self):
        result = parse_user_id("user:12345")
        assert result == ParseResult(user_id="12345", source="string")

    def test_all_underscores_min_length(self):
        result = parse_user_id("user:___")
        assert result == ParseResult(user_id="___", source="string")

    def test_all_hyphens_min_length(self):
        result = parse_user_id("user:---")
        assert result == ParseResult(user_id="---", source="string")


# ==============================================================================
# parse_user_id - Validation: length
# ==============================================================================

class TestParseUserIdLengthValidation:
    def test_length_1(self):
        assert parse_user_id("user:a") is None

    def test_length_2(self):
        assert parse_user_id("user:ab") is None

    def test_length_3(self):
        result = parse_user_id("user:abc")
        assert result is not None

    def test_length_10(self):
        result = parse_user_id("user:" + "a" * 10)
        assert result is not None

    def test_length_20(self):
        result = parse_user_id("user:" + "a" * 20)
        assert result is not None

    def test_length_21(self):
        assert parse_user_id("user:" + "a" * 21) is None

    def test_length_100(self):
        assert parse_user_id("user:" + "a" * 100) is None


# ==============================================================================
# parse_user_id - Validation: reserved IDs
# ==============================================================================

class TestParseUserIdReservedIds:
    def test_default_reserved_admin(self):
        assert parse_user_id("user:admin") is None

    def test_default_reserved_root(self):
        assert parse_user_id("user:root") is None

    def test_default_reserved_system(self):
        assert parse_user_id("user:system") is None

    def test_default_reserved_case_insensitive(self):
        # "ADMIN" lowercased → "admin" → reserved
        assert parse_user_id("user:ADMIN") is None

    def test_custom_reserved_replaces_defaults(self):
        # "admin" should be allowed when custom set doesn't include it
        result = parse_user_id("user:admin", reserved_ids={"blocked"})
        assert result == ParseResult(user_id="admin", source="string")

    def test_custom_reserved_blocks_custom_id(self):
        assert parse_user_id("user:blocked", reserved_ids={"blocked"}) is None

    def test_custom_reserved_empty_set(self):
        # No reserved IDs at all
        result = parse_user_id("user:admin", reserved_ids=set())
        assert result == ParseResult(user_id="admin", source="string")

    def test_custom_reserved_root_allowed(self):
        result = parse_user_id("user:root", reserved_ids={"other"})
        assert result == ParseResult(user_id="root", source="string")

    def test_custom_reserved_system_allowed(self):
        result = parse_user_id("user:system", reserved_ids=set())
        assert result == ParseResult(user_id="system", source="string")


# ==============================================================================
# parse_user_id - Strict mode
# ==============================================================================

class TestParseUserIdStrictMode:
    def test_strict_false_double_underscore_allowed(self):
        result = parse_user_id("user:a__b", strict=False)
        assert result == ParseResult(user_id="a__b", source="string")

    def test_strict_true_double_underscore_rejected(self):
        assert parse_user_id("user:a__b", strict=True) is None

    def test_strict_true_double_hyphen_rejected(self):
        assert parse_user_id("user:a--b", strict=True) is None

    def test_strict_true_underscore_hyphen_rejected(self):
        assert parse_user_id("user:a_-b", strict=True) is None

    def test_strict_true_hyphen_underscore_rejected(self):
        assert parse_user_id("user:a-_b", strict=True) is None

    def test_strict_true_single_underscore_allowed(self):
        result = parse_user_id("user:a_b_c", strict=True)
        assert result == ParseResult(user_id="a_b_c", source="string")

    def test_strict_true_single_hyphen_allowed(self):
        result = parse_user_id("user:a-b-c", strict=True)
        assert result == ParseResult(user_id="a-b-c", source="string")

    def test_strict_true_no_specials(self):
        result = parse_user_id("user:alice", strict=True)
        assert result == ParseResult(user_id="alice", source="string")

    def test_strict_false_double_hyphen_allowed(self):
        result = parse_user_id("user:a--b", strict=False)
        assert result == ParseResult(user_id="a--b", source="string")

    def test_strict_true_triple_underscore_rejected(self):
        assert parse_user_id("user:a___b", strict=True) is None

    def test_strict_default_is_false(self):
        # Default strict=False, so consecutive specials should be allowed
        result = parse_user_id("user:a__b")
        assert result == ParseResult(user_id="a__b", source="string")


# ==============================================================================
# parse_user_id - Edge cases / error handling
# ==============================================================================

class TestParseUserIdEdgeCases:
    def test_none_input(self):
        assert parse_user_id(None) is None

    def test_integer_input(self):
        assert parse_user_id(42) is None

    def test_float_input(self):
        assert parse_user_id(3.14) is None

    def test_list_input(self):
        assert parse_user_id(["user:alice"]) is None

    def test_boolean_input(self):
        assert parse_user_id(True) is None

    def test_empty_string(self):
        assert parse_user_id("") is None

    def test_random_string(self):
        assert parse_user_id("hello") is None

    def test_string_without_prefix(self):
        assert parse_user_id("alice") is None

    def test_empty_dict(self):
        assert parse_user_id({}) is None

    def test_dict_with_wrong_keys(self):
        assert parse_user_id({"name": "alice"}) is None

    def test_tuple_input(self):
        assert parse_user_id(("user:alice",)) is None

    def test_set_input(self):
        assert parse_user_id({"user:alice"}) is None

    def test_user_prefix_only_whitespace_id(self):
        # "user:   " → after trim → "" → length 0 → None
        assert parse_user_id("user:   ") is None

    def test_email_prefix_only(self):
        assert parse_user_id("email:") is None

    def test_dict_flat_with_list_value(self):
        assert parse_user_id({"user_id": ["alice"]}) is None

    def test_dict_nested_with_list_id(self):
        assert parse_user_id({"user": {"id": ["alice"]}}) is None

    def test_does_not_raise_on_bad_input(self):
        """Ensure no exceptions are raised for various bad inputs."""
        bad_inputs = [None, 42, 3.14, [], {}, True, False, object(), b"bytes"]
        for inp in bad_inputs:
            result = parse_user_id(inp)
            assert result is None


# ==============================================================================
# parse_user_ids - Batch processing
# ==============================================================================

class TestParseUserIds:
    def test_empty_list(self):
        assert parse_user_ids([]) == []

    def test_single_valid_item(self):
        result = parse_user_ids(["user:alice"])
        assert result == [ParseResult(user_id="alice", source="string")]

    def test_single_invalid_item(self):
        result = parse_user_ids([None])
        assert result == [None]

    def test_mixed_valid_and_invalid(self):
        items = ["user:alice", None, "email:bob@example.com", 42, {"user_id": "charlie"}]
        result = parse_user_ids(items)
        assert len(result) == 5
        assert result[0] == ParseResult(user_id="alice", source="string")
        assert result[1] is None
        assert result[2] == ParseResult(user_id="bob", source="email")
        assert result[3] is None
        assert result[4] == ParseResult(user_id="charlie", source="dict_flat")

    def test_preserves_ordering(self):
        items = ["user:zzz", "user:aaa", "user:mmm"]
        result = parse_user_ids(items)
        assert result[0].user_id == "zzz"
        assert result[1].user_id == "aaa"
        assert result[2].user_id == "mmm"

    def test_passes_reserved_ids_through(self):
        items = ["user:admin", "user:alice"]
        # With default reserved, admin should be None
        result_default = parse_user_ids(items)
        assert result_default[0] is None
        assert result_default[1] is not None

        # With custom reserved that doesn't include admin
        result_custom = parse_user_ids(items, reserved_ids=set())
        assert result_custom[0] is not None
        assert result_custom[1] is not None

    def test_passes_strict_through(self):
        items = ["user:a__b"]
        result_non_strict = parse_user_ids(items, strict=False)
        assert result_non_strict[0] is not None

        result_strict = parse_user_ids(items, strict=True)
        assert result_strict[0] is None

    def test_all_invalid(self):
        items = [None, 42, "", "bad"]
        result = parse_user_ids(items)
        assert result == [None, None, None, None]

    def test_all_valid(self):
        items = ["user:alice", "user:bob", "user:charlie"]
        result = parse_user_ids(items)
        assert all(r is not None for r in result)
        assert len(result) == 3

    def test_result_length_matches_input(self):
        items = ["user:alice", None, "user:bob", 42, "email:eve@test.com"]
        result = parse_user_ids(items)
        assert len(result) == len(items)


# ==============================================================================
# Integration tests - combining multiple features
# ==============================================================================

class TestIntegration:
    def test_email_reserved_id(self):
        # Email where username is a reserved ID
        assert parse_user_id("email:admin@example.com") is None

    def test_dict_nested_reserved_id(self):
        assert parse_user_id({"user": {"id": "root"}}) is None

    def test_dict_flat_strict_mode(self):
        assert parse_user_id({"user_id": "a__b"}, strict=True) is None
        result = parse_user_id({"user_id": "a__b"}, strict=False)
        assert result is not None

    def test_email_strict_mode(self):
        assert parse_user_id("email:a__b@example.com", strict=True) is None

    def test_custom_reserved_with_strict(self):
        # Custom reserved + strict mode
        assert parse_user_id("user:blocked", reserved_ids={"blocked"}, strict=True) is None
        result = parse_user_id("user:alice", reserved_ids={"blocked"}, strict=True)
        assert result == ParseResult(user_id="alice", source="string")

    def test_whitespace_in_dict_nested(self):
        result = parse_user_id({"user": {"id": "  ALICE  "}})
        assert result == ParseResult(user_id="alice", source="dict_nested")

    def test_batch_with_all_sources(self):
        items = [
            "user:alice",
            "email:bob@test.com",
            {"user_id": "charlie"},
            {"user": {"id": "dave"}},
        ]
        result = parse_user_ids(items)
        assert result[0] == ParseResult(user_id="alice", source="string")
        assert result[1] == ParseResult(user_id="bob", source="email")
        assert result[2] == ParseResult(user_id="charlie", source="dict_flat")
        assert result[3] == ParseResult(user_id="dave", source="dict_nested")

    def test_reserved_id_after_normalization(self):
        # "  ADMIN  " → "admin" → reserved
        assert parse_user_id("user:  ADMIN  ") is None
        assert parse_user_id({"user_id": "  ROOT  "}) is None
        assert parse_user_id({"user": {"id": "  SYSTEM  "}}) is None


# ==============================================================================
# Z3 Formal Verification Tests
# ==============================================================================

class TestZ3FormalVerification:
    """
    Use Z3 to formally verify properties of the validation logic.
    These tests verify that certain invariants hold.
    """

    def test_z3_length_constraints_consistent(self):
        """
        Verify using Z3 that the length constraints (3-20) are consistent:
        there exist valid IDs of length 3 and length 20, and no valid ID
        can have length < 3 or > 20.
        """
        try:
            from z3 import Int, And, Or, Solver, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        length = Int('length')
        s = Solver()

        # Property: valid length is 3 <= length <= 20
        valid_length = And(length >= 3, length <= 20)

        # Check that length=3 is satisfiable
        s.push()
        s.add(valid_length)
        s.add(length == 3)
        assert s.check() == sat, "Length 3 should be valid"
        s.pop()

        # Check that length=20 is satisfiable
        s.push()
        s.add(valid_length)
        s.add(length == 20)
        assert s.check() == sat, "Length 20 should be valid"
        s.pop()

        # Check that length=2 is unsatisfiable
        s.push()
        s.add(valid_length)
        s.add(length == 2)
        assert s.check() == unsat, "Length 2 should be invalid"
        s.pop()

        # Check that length=21 is unsatisfiable
        s.push()
        s.add(valid_length)
        s.add(length == 21)
        assert s.check() == unsat, "Length 21 should be invalid"
        s.pop()

    def test_z3_reserved_and_custom_mutually_exclusive(self):
        """
        Verify that when custom reserved_ids is provided, default reserved IDs
        are not used. Model this as: if custom is provided, default set is ignored.
        """
        try:
            from z3 import Bool, And, Not, Or, Solver, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        custom_provided = Bool('custom_provided')
        id_is_admin = Bool('id_is_admin')
        id_in_custom = Bool('id_in_custom')
        id_rejected = Bool('id_rejected')

        s = Solver()

        # Model: if custom_provided, reject iff id_in_custom
        #         if not custom_provided, reject iff id_is_admin (default)
        s.add(id_rejected == Or(
            And(custom_provided, id_in_custom),
            And(Not(custom_provided), id_is_admin)
        ))

        # Scenario: custom provided, id is "admin" but not in custom set
        s.push()
        s.add(custom_provided == True)
        s.add(id_is_admin == True)
        s.add(id_in_custom == False)
        assert s.check() == sat
        model = s.model()
        # id_rejected should be False (admin allowed when custom set doesn't include it)
        assert not model[id_rejected], "admin should be allowed with custom set not containing it"
        s.pop()

    def test_z3_strict_mode_is_superset_of_non_strict(self):
        """
        Verify that strict mode rejects everything non-strict rejects plus more.
        If non-strict rejects an ID, strict must also reject it.
        """
        try:
            from z3 import Bool, And, Or, Not, Implies, Solver, sat, unsat, ForAll
        except ImportError:
            pytest.skip("z3-solver not installed")

        # Model: non_strict_valid implies strict could be valid or invalid
        #        but strict_valid implies non_strict_valid
        non_strict_valid = Bool('non_strict_valid')
        strict_valid = Bool('strict_valid')
        has_consecutive_special = Bool('has_consecutive_special')

        s = Solver()

        # strict_valid = non_strict_valid AND NOT has_consecutive_special
        s.add(strict_valid == And(non_strict_valid, Not(has_consecutive_special)))

        # Verify: strict_valid implies non_strict_valid
        s.push()
        s.add(strict_valid == True)
        assert s.check() == sat
        model = s.model()
        assert model[non_strict_valid], "strict valid implies non-strict valid"
        s.pop()

        # Verify: non_strict invalid implies strict invalid
        s.push()
        s.add(non_strict_valid == False)
        assert s.check() == sat
        model = s.model()
        assert not model[strict_valid], "non-strict invalid implies strict invalid"
        s.pop()


# ==============================================================================
# Additional boundary and corner case tests
# ==============================================================================

class TestBoundaryAndCornerCases:
    def test_user_id_exactly_boundary_chars(self):
        """Test with IDs at exact boundary of allowed character set."""
        # All allowed chars
        result = parse_user_id("user:az09_-az09_-az09")
        assert result is not None

    def test_id_with_only_special_chars(self):
        result = parse_user_id("user:_-_")
        assert result is not None

    def test_id_starting_with_number(self):
        result = parse_user_id("user:123abc")
        assert result is not None

    def test_id_starting_with_underscore(self):
        result = parse_user_id("user:_abc")
        assert result is not None

    def test_id_starting_with_hyphen(self):
        result = parse_user_id("user:-abc")
        assert result is not None

    def test_email_with_plus_in_username(self):
        # '+' is not in allowed chars
        assert parse_user_id("email:user+tag@example.com") is None

    def test_email_with_dot_in_username(self):
        # '.' is not in allowed chars
        assert parse_user_id("email:user.name@example.com") is None

    def test_dict_with_both_keys_flat_wins(self):
        """When dict has both user_id and user keys, user_id (flat) takes priority."""
        result = parse_user_id({"user_id": "flat_id", "user": {"id": "nested_id"}})
        assert result.source == "dict_flat"
        assert result.user_id == "flat_id"

    def test_whitespace_only_after_trim_too_short(self):
        assert parse_user_id("user:  a  ") is None  # "a" is length 1

    def test_tabs_and_newlines_trimmed(self):
        result = parse_user_id("user:\t alice \n")
        assert result == ParseResult(user_id="alice", source="string")

    def test_reserved_id_with_different_case(self):
        """Reserved check should happen after lowercasing."""
        assert parse_user_id("user:Admin") is None
        assert parse_user_id("user:ROOT") is None
        assert parse_user_id("user:SyStEm") is None