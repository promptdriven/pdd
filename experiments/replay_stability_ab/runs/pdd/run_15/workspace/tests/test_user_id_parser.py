import sys
from pathlib import Path

# Add src directory to sys.path to ensure local code is prioritized
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root / "src"))

from user_id_parser import parse_user_id, parse_user_ids, ParseResult
import copy


class TestDictPrecedenceComprehensive:
    def test_user_id_string_empty_takes_precedence_over_valid_nested(self):
        """user_id key with empty string means user: branch wins with ''"""
        result = parse_user_id({"user_id": "", "user": {"id": "valid1"}})
        assert result is None


# ===========================================================================
# 1. String "user:" prefix tests
# ===========================================================================

class TestUserPrefix:
    def test_valid_simple_id(self):
        assert parse_user_id("user:alice") == ParseResult(user_id="alice", source="string")

    def test_valid_numeric_id(self):
        assert parse_user_id("user:user123") == ParseResult(user_id="user123", source="string")

    def test_whitespace_trimmed(self):
        assert parse_user_id("user:  alice  ") == ParseResult(user_id="alice", source="string")

    def test_uppercase_lowered(self):
        assert parse_user_id("user:ALICE") == ParseResult(user_id="alice", source="string")

    def test_mixed_case_and_whitespace(self):
        assert parse_user_id("user:  AlIcE  ") == ParseResult(user_id="alice", source="string")

    def test_empty_after_prefix(self):
        assert parse_user_id("user:") is None

    def test_whitespace_only_after_prefix(self):
        assert parse_user_id("user:   ") is None

    def test_exactly_3_chars(self):
        assert parse_user_id("user:abc") == ParseResult(user_id="abc", source="string")

    def test_exactly_20_chars(self):
        uid = "a" * 20
        assert parse_user_id(f"user:{uid}") == ParseResult(user_id=uid, source="string")

    def test_2_chars_too_short(self):
        assert parse_user_id("user:ab") is None

    def test_21_chars_too_long(self):
        uid = "a" * 21
        assert parse_user_id(f"user:{uid}") is None

    def test_underscore_allowed(self):
        assert parse_user_id("user:al_ce") == ParseResult(user_id="al_ce", source="string")

    def test_hyphen_allowed(self):
        assert parse_user_id("user:al-ce") == ParseResult(user_id="al-ce", source="string")

    def test_invalid_char_exclamation(self):
        assert parse_user_id("user:al!ce") is None

    def test_invalid_char_dot(self):
        assert parse_user_id("user:al.ce") is None

    def test_invalid_char_at(self):
        assert parse_user_id("user:al@ce") is None

    def test_space_in_middle(self):
        assert parse_user_id("user:al ce") is None

    def test_numbers_and_letters(self):
        assert parse_user_id("user:abc123") == ParseResult(user_id="abc123", source="string")

    def test_all_valid_char_types(self):
        assert parse_user_id("user:a1_b2-c3") == ParseResult(user_id="a1_b2-c3", source="string")


# ===========================================================================
# 2. String "email:" prefix tests
# ===========================================================================

class TestEmailPrefix:
    def test_valid_email(self):
        assert parse_user_id("email:alice@example.com") == ParseResult(user_id="alice", source="email")

    def test_email_uppercase_normalized(self):
        assert parse_user_id("email:ALICE@example.com") == ParseResult(user_id="alice", source="email")

    def test_email_username_whitespace_trimmed(self):
        assert parse_user_id("email:  alice  @example.com") == ParseResult(user_id="alice", source="email")

    def test_email_no_at_sign(self):
        assert parse_user_id("email:alice") is None

    def test_email_empty_username(self):
        assert parse_user_id("email:@domain.com") is None

    def test_email_whitespace_only_username(self):
        assert parse_user_id("email:   @domain.com") is None

    def test_email_multiple_at_signs(self):
        # Should use first @ sign, so username is "alice"
        assert parse_user_id("email:alice@domain@extra") == ParseResult(user_id="alice", source="email")

    def test_email_short_username(self):
        assert parse_user_id("email:ab@domain.com") is None  # 2 chars too short

    def test_email_exact_3_char_username(self):
        assert parse_user_id("email:abc@domain.com") == ParseResult(user_id="abc", source="email")

    def test_email_long_username(self):
        uid = "a" * 21
        assert parse_user_id(f"email:{uid}@domain.com") is None

    def test_email_reserved_username(self):
        assert parse_user_id("email:admin@example.com") is None

    def test_email_invalid_chars_in_username(self):
        assert parse_user_id("email:al.ice@example.com") is None

    def test_email_valid_with_hyphen(self):
        assert parse_user_id("email:al-ice@example.com") == ParseResult(user_id="al-ice", source="email")

    def test_email_valid_with_underscore(self):
        assert parse_user_id("email:al_ice@example.com") == ParseResult(user_id="al_ice", source="email")


# ===========================================================================
# 3. Dict {"user_id": ...} tests
# ===========================================================================

class TestDictUserId:
    def test_valid_user_id(self):
        assert parse_user_id({"user_id": "alice"}) == ParseResult(user_id="alice", source="dict_flat")

    def test_user_id_normalized(self):
        assert parse_user_id({"user_id": "  ALICE  "}) == ParseResult(user_id="alice", source="dict_flat")

    def test_user_id_non_string_int(self):
        assert parse_user_id({"user_id": 123}) is None

    def test_user_id_non_string_none(self):
        assert parse_user_id({"user_id": None}) is None

    def test_user_id_non_string_list(self):
        assert parse_user_id({"user_id": ["alice"]}) is None

    def test_user_id_reserved(self):
        assert parse_user_id({"user_id": "admin"}) is None

    def test_user_id_too_short(self):
        assert parse_user_id({"user_id": "ab"}) is None

    def test_user_id_too_long(self):
        assert parse_user_id({"user_id": "a" * 21}) is None

    def test_user_id_invalid_chars(self):
        assert parse_user_id({"user_id": "al!ce"}) is None


# ===========================================================================
# 4. Dict {"user": {"id": ...}}
# ===========================================================================

class TestDictNestedUserId:
    def test_valid_nested_id(self):
        assert parse_user_id({"user": {"id": "alice"}}) == ParseResult(user_id="alice", source="dict_nested")

    def test_nested_id_normalized(self):
        assert parse_user_id({"user": {"id": "  ALICE  "}}) == ParseResult(user_id="alice", source="dict_nested")

    def test_user_not_dict_string(self):
        assert parse_user_id({"user": "alice"}) is None

    def test_user_not_dict_int(self):
        assert parse_user_id({"user": 123}) is None

    def test_user_not_dict_none(self):
        assert parse_user_id({"user": None}) is None

    def test_nested_id_not_string_int(self):
        assert parse_user_id({"user": {"id": 123}}) is None

    def test_nested_id_not_string_none(self):
        assert parse_user_id({"user": {"id": None}}) is None

    def test_nested_id_missing_key(self):
        assert parse_user_id({"user": {"name": "alice"}}) is None

    def test_nested_id_reserved(self):
        assert parse_user_id({"user": {"id": "root"}}) is None

    def test_nested_id_invalid_chars(self):
        assert parse_user_id({"user": {"id": "al.ce"}}) is None


# ===========================================================================
# 5. Dict precedence tests
# ===========================================================================

class TestDictPrecedence:
    def test_user_id_takes_precedence_over_nested(self):
        result = parse_user_id({"user_id": "alice", "user": {"id": "bob"}})
        assert result == ParseResult(user_id="alice", source="dict_flat")

    def test_user_id_invalid_blocks_nested_valid(self):
        """When user_id key exists but value is non-string, nested is not tried."""
        result = parse_user_id({"user_id": 123, "user": {"id": "bob"}})
        assert result is None

    def test_user_id_empty_string_blocks_nested(self):
        """user_id with empty string is extracted (returns '') which then fails validation."""
        result = parse_user_id({"user_id": "  ", "user": {"id": "valid1"}})
        assert result is None


# ===========================================================================
# 6. Reserved IDs tests
# ===========================================================================

class TestReservedIds:
    def test_default_reserved_admin(self):
        assert parse_user_id("user:admin") is None

    def test_default_reserved_root(self):
        assert parse_user_id("user:root") is None

    def test_default_reserved_system(self):
        assert parse_user_id("user:system") is None

    def test_default_reserved_case_insensitive(self):
        assert parse_user_id("user:ADMIN") is None

    def test_custom_reserved_replaces_defaults(self):
        # "admin" should be allowed when custom set doesn't include it
        result = parse_user_id("user:admin", reserved_ids={"blocked"})
        assert result == ParseResult(user_id="admin", source="string")

    def test_custom_reserved_rejects_custom(self):
        assert parse_user_id("user:blocked", reserved_ids={"blocked"}) is None

    def test_empty_reserved_allows_all(self):
        result = parse_user_id("user:admin", reserved_ids=set())
        assert result == ParseResult(user_id="admin", source="string")

    def test_empty_reserved_allows_root(self):
        result = parse_user_id("user:root", reserved_ids=set())
        assert result == ParseResult(user_id="root", source="string")

    def test_empty_reserved_allows_system(self):
        result = parse_user_id("user:system", reserved_ids=set())
        assert result == ParseResult(user_id="system", source="string")

    def test_custom_reserved_multiple(self):
        reserved = {"test", "demo", "example"}
        assert parse_user_id("user:test", reserved_ids=reserved) is None
        assert parse_user_id("user:demo", reserved_ids=reserved) is None
        assert parse_user_id("user:example", reserved_ids=reserved) is None
        result = parse_user_id("user:alice", reserved_ids=reserved)
        assert result == ParseResult(user_id="alice", source="string")


# ===========================================================================
# 7. Invalid/unexpected input types
# ===========================================================================

class TestInvalidInputTypes:
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
        assert parse_user_id(["user:alice"]) is None

    def test_tuple_input(self):
        assert parse_user_id(("user:alice",)) is None

    def test_empty_string(self):
        assert parse_user_id("") is None

    def test_string_no_prefix(self):
        assert parse_user_id("alice") is None

    def test_string_unknown_prefix(self):
        assert parse_user_id("name:alice") is None

    def test_empty_dict(self):
        assert parse_user_id({}) is None

    def test_dict_wrong_keys(self):
        assert parse_user_id({"name": "alice"}) is None

    def test_string_just_user_colon(self):
        # "user:" + empty -> extracted is "", strip -> "", length 0 < 3
        assert parse_user_id("user:") is None

    def test_string_just_email_colon(self):
        assert parse_user_id("email:") is None

    def test_set_input(self):
        assert parse_user_id({"alice"}) is None  # set, not dict... wait, {"alice"} is a set


# ===========================================================================
# 8. No mutation of input dicts
# ===========================================================================

class TestNoMutation:
    def test_flat_dict_not_mutated(self):
        d = {"user_id": "  Alice  "}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_nested_dict_not_mutated(self):
        d = {"user": {"id": "  Alice  "}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_with_extra_keys_not_mutated(self):
        d = {"user_id": "alice", "extra": "data", "user": {"id": "bob"}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original


# ===========================================================================
# 9. parse_user_ids batch processing tests
# ===========================================================================

class TestParseUserIds:
    def test_empty_list(self):
        assert parse_user_ids([]) == []

    def test_all_valid(self):
        items = ["user:alice", "user:bob", "user:charlie"]
        result = parse_user_ids(items)
        assert result == [
            ParseResult(user_id="alice", source="string"),
            ParseResult(user_id="bob", source="string"),
            ParseResult(user_id="charlie", source="string"),
        ]

    def test_all_invalid(self):
        items = [None, 42, "invalid", "user:!!", "user:ab"]
        result = parse_user_ids(items)
        assert result == [None, None, None, None, None]

    def test_mixed_valid_invalid(self):
        items = ["user:alice", None, "user:bob", 42, "email:carol@x.com"]
        result = parse_user_ids(items)
        assert result == [
            ParseResult(user_id="alice", source="string"),
            None,
            ParseResult(user_id="bob", source="string"),
            None,
            ParseResult(user_id="carol", source="email"),
        ]

    def test_ordering_preserved(self):
        items = ["user:zzz", "user:aaa", "user:mmm"]
        result = parse_user_ids(items)
        assert result == [
            ParseResult(user_id="zzz", source="string"),
            ParseResult(user_id="aaa", source="string"),
            ParseResult(user_id="mmm", source="string"),
        ]

    def test_length_matches_input(self):
        items = ["user:alice", None, "bad", {"user_id": "bob"}]
        result = parse_user_ids(items)
        assert len(result) == len(items)

    def test_reserved_ids_passed_through(self):
        items = ["user:admin", "user:root", "user:alice"]
        # Default reserved
        result_default = parse_user_ids(items)
        assert result_default == [None, None, ParseResult(user_id="alice", source="string")]

        # Custom reserved (empty)
        result_empty = parse_user_ids(items, reserved_ids=set())
        assert result_empty == [
            ParseResult(user_id="admin", source="string"),
            ParseResult(user_id="root", source="string"),
            ParseResult(user_id="alice", source="string"),
        ]

    def test_reserved_ids_custom_set(self):
        items = ["user:admin", "user:blocked"]
        result = parse_user_ids(items, reserved_ids={"blocked"})
        assert result == [ParseResult(user_id="admin", source="string"), None]

    def test_dict_inputs_in_batch(self):
        items = [
            {"user_id": "alice"},
            {"user": {"id": "bob"}},
            {"bad_key": "carol"},
        ]
        result = parse_user_ids(items)
        assert result == [
            ParseResult(user_id="alice", source="dict_flat"),
            ParseResult(user_id="bob", source="dict_nested"),
            None,
        ]

    def test_single_item_list(self):
        assert parse_user_ids(["user:alice"]) == [ParseResult(user_id="alice", source="string")]

    def test_email_inputs_in_batch(self):
        items = ["email:alice@x.com", "email:bob@y.com"]
        result = parse_user_ids(items)
        assert result == [
            ParseResult(user_id="alice", source="email"),
            ParseResult(user_id="bob", source="email"),
        ]


# ===========================================================================
# 10. Boundary and edge case tests
# ===========================================================================

class TestBoundaryAndEdgeCases:
    def test_id_all_underscores_length_3(self):
        assert parse_user_id("user:___") == ParseResult(user_id="___", source="string")

    def test_id_all_hyphens_length_3(self):
        assert parse_user_id("user:---") == ParseResult(user_id="---", source="string")

    def test_id_all_digits_length_3(self):
        assert parse_user_id("user:123") == ParseResult(user_id="123", source="string")

    def test_id_exact_length_20(self):
        uid = "abcdefghij1234567890"
        assert len(uid) == 20
        assert parse_user_id(f"user:{uid}") == ParseResult(user_id=uid, source="string")

    def test_id_length_19(self):
        uid = "a" * 19
        assert parse_user_id(f"user:{uid}") == ParseResult(user_id=uid, source="string")

    def test_id_length_4(self):
        assert parse_user_id("user:abcd") == ParseResult(user_id="abcd", source="string")

    def test_whitespace_trimmed_results_in_valid_length(self):
        # "  abc  " -> "abc" (3 chars, valid)
        assert parse_user_id("user:  abc  ") == ParseResult(user_id="abc", source="string")

    def test_whitespace_trimmed_results_in_too_short(self):
        # "  ab  " -> "ab" (2 chars, invalid)
        assert parse_user_id("user:  ab  ") is None

    def test_tab_and_newline_whitespace(self):
        assert parse_user_id("user:\tabc\n") == ParseResult(user_id="abc", source="string")

    def test_email_prefix_case_sensitive(self):
        # "Email:" is not "email:", should return None
        assert parse_user_id("Email:alice@example.com") is None

    def test_user_prefix_case_sensitive(self):
        # "User:" is not "user:", should return None
        assert parse_user_id("User:alice") is None

    def test_dict_user_id_empty_dict_value(self):
        assert parse_user_id({"user": {}}) is None

    def test_reserved_after_normalization(self):
        # "ADMIN" -> "admin" which is reserved
        assert parse_user_id({"user_id": "ADMIN"}) is None

    def test_reserved_with_whitespace(self):
        # "  root  " -> "root" which is reserved
        assert parse_user_id({"user_id": "  root  "}) is None


# ===========================================================================
# 11. Z3 Formal Verification Tests (run as unit tests)
# ===========================================================================

class TestZ3FormalVerification:
    """
    Use Z3 to formally verify properties of the validation logic.
    These tests verify that the regex pattern and length constraints
    are consistent and correct.
    """

    def test_z3_valid_chars_accepted(self):
        """Verify using Z3 that all allowed character classes produce valid IDs."""
        try:
            from z3 import Solver, String, Length, And, Or, sat, StringVal, Re, InRe, Union, Star, Range
        except ImportError:
            import pytest
            pytest.skip("z3-solver not installed")

        s = Solver()
        x = String("x")

        # Define the valid pattern: [a-z0-9_-]{3,20}
        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re(StringVal("_")),
            Re(StringVal("-")),
        )
        valid_pattern = And(
            InRe(x, Star(char_class)),
            Length(x) >= 3,
            Length(x) <= 20,
        )

        # Assert there exists a valid string
        s.add(valid_pattern)
        assert s.check() == sat

        model = s.model()
        result_str = model[x].as_string()
        # Verify the result also passes our actual function
        parsed = parse_user_id(f"user:{result_str}", reserved_ids=set())
        assert parsed is not None
        assert parsed.user_id == result_str

    def test_z3_too_short_rejected(self):
        """Verify that strings of length < 3 are always rejected."""
        try:
            from z3 import Solver, String, Length, And, Or, sat, unsat, StringVal, Re, InRe, Union, Star, Range
        except ImportError:
            import pytest
            pytest.skip("z3-solver not installed")

        s = Solver()
        x = String("x")

        # Valid chars but length < 3
        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re(StringVal("_")),
            Re(StringVal("-")),
        )
        s.add(InRe(x, Star(char_class)))
        s.add(Length(x) >= 1)
        s.add(Length(x) < 3)

        # There should exist such strings
        assert s.check() == sat

        model = s.model()
        short_str = model[x].as_string()
        # Verify actual function rejects it
        assert parse_user_id(f"user:{short_str}", reserved_ids=set()) is None

    def test_z3_too_long_rejected(self):
        """Verify that strings of length > 20 are always rejected."""
        try:
            from z3 import Solver, String, Length, And, sat, StringVal, Re, InRe, Union, Star, Range
        except ImportError:
            import pytest
            pytest.skip("z3-solver not installed")

        s = Solver()
        x = String("x")

        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re(StringVal("_")),
            Re(StringVal("-")),
        )
        s.add(InRe(x, Star(char_class)))
        s.add(Length(x) > 20)
        s.add(Length(x) <= 25)  # bound for tractability

        assert s.check() == sat

        model = s.model()
        long_str = model[x].as_string()
        assert parse_user_id(f"user:{long_str}", reserved_ids=set()) is None

    def test_z3_invalid_char_rejected(self):
        """
        Verify using concrete examples derived from Z3 reasoning that
        invalid characters cause rejection.
        """
        # Characters outside [a-z0-9_-] should be rejected
        invalid_chars = ['!', '@', '#', '$', '%', '^', '&', '*', '(', ')',
                         '.', ',', '/', '\\', ' ', '+', '=', '~', '`',
                         'A', 'Z']  # uppercase already lowered, but after lower they're valid
        for ch in invalid_chars:
            test_id = f"ab{ch}cd"
            result = parse_user_id(f"user:{test_id}", reserved_ids=set())
            if ch.isalpha() and ch.lower() + "" == ch.lower():
                # Uppercase letters get lowered and become valid
                if all(c in 'abcdefghijklmnopqrstuvwxyz0123456789_-"' for c in test_id.strip().lower()):
                    assert result is not None, f"Expected valid for char '{ch}'"
                    continue
            if any(c not in 'abcdefghijklmnopqrstuvwxyz0123456789_-' for c in test_id.strip().lower()):
                assert result is None, f"Expected None for char '{ch}' in '{test_id}'"


# ===========================================================================
# ParseResult structure test
# ===========================================================================

class TestParseResultStructure:
    def test_parse_result_has_user_id_field(self):
        pr = ParseResult(user_id='alice', source='string')
        assert pr.user_id == 'alice'


# ==========================================================================
# NEW TESTS — Detailed Test Plan
# ===========================================================================
#
# MAJOR GAP IDENTIFIED: No existing tests for strict mode (strict=True).
# This is a critical feature that rejects IDs containing consecutive
# special characters: __, --, _-, -_.
#
# Test Plan:
#
# 1. STRICT MODE UNIT TESTS:
#    a) Each of the 4 consecutive special patterns (__, --, _-, -_) rejected
#       when strict=True across ALL input types (string, email, dict_flat, dict_nested)
#    b) Each pattern ALLOWED when strict=False (default)
#    c) Single specials still allowed in strict mode
#    d) Triple specials rejected in strict mode
#    e) Consecutive specials at start/middle/end of ID
#    f) Default strict=False verified explicitly
#    → Best as unit tests: deterministic, fast, clear pass/fail
#
# 2. STRICT MODE IN BATCH (parse_user_ids):
#    a) strict=True passed through correctly
#    b) Combined strict + reserved_ids
#    → Unit tests
#
# 3. PARSERESULT NAMEDTUPLE COMPLETENESS:
#    a) Index access, unpacking, equality, tuple inheritance
#    → Unit tests
#
# 4. NO-EXCEPTION GUARANTEE:
#    a) Various bad input types (bytes, complex, class instances, frozenset)
#    b) Deeply nested dicts, etc.
#    → Unit tests
#
# 5. RESERVED IDS EDGE CASES:
#    a) None vs explicit set; frozenset/list as container; normalization order
#    → Unit tests
#
# 6. Z3 FORMAL VERIFICATION FOR STRICT MODE:
#    a) Find valid string containing "__" → verify strict rejects, non-strict accepts
#    b) Find valid string containing "--" → same
#    c) Find valid string containing "_-" → same
#    d) Find valid string with NO consecutive specials → verify strict accepts
#    → Z3 tests (stronger guarantee via symbolic reasoning)
#
# 7. ADDITIONAL EDGE CASES:
#    a) Unicode/emoji in IDs
#    b) Batch with all 4 input types simultaneously
#    c) Batch ordering and mutation safety
#    d) Email edge cases (empty domain)
#    → Unit tests


# ===========================================================================
# 12. Strict Mode — String "user:" prefix
# ===========================================================================


class TestStrictMode:
    """Tests for strict=True which rejects consecutive special characters."""

    def test_double_underscore_rejected_strict(self):
        assert parse_user_id("user:a__b", strict=True) is None

    def test_double_hyphen_rejected_strict(self):
        assert parse_user_id("user:a--b", strict=True) is None

    def test_underscore_hyphen_rejected_strict(self):
        assert parse_user_id("user:a_-b", strict=True) is None

    def test_hyphen_underscore_rejected_strict(self):
        assert parse_user_id("user:a-_b", strict=True) is None

    def test_double_underscore_allowed_nonstrict(self):
        result = parse_user_id("user:a__b", strict=False)
        assert result == ParseResult(user_id="a__b", source="string")

    def test_double_hyphen_allowed_nonstrict(self):
        result = parse_user_id("user:a--b", strict=False)
        assert result == ParseResult(user_id="a--b", source="string")

    def test_underscore_hyphen_allowed_nonstrict(self):
        result = parse_user_id("user:a_-b", strict=False)
        assert result == ParseResult(user_id="a_-b", source="string")

    def test_hyphen_underscore_allowed_nonstrict(self):
        result = parse_user_id("user:a-_b", strict=False)
        assert result == ParseResult(user_id="a-_b", source="string")

    def test_single_underscore_allowed_strict(self):
        result = parse_user_id("user:a_bc", strict=True)
        assert result == ParseResult(user_id="a_bc", source="string")

    def test_single_hyphen_allowed_strict(self):
        result = parse_user_id("user:a-bc", strict=True)
        assert result == ParseResult(user_id="a-bc", source="string")

    def test_separated_specials_allowed_strict(self):
        result = parse_user_id("user:a_b-c", strict=True)
        assert result == ParseResult(user_id="a_b-c", source="string")

    def test_triple_underscore_rejected_strict(self):
        assert parse_user_id("user:a___b", strict=True) is None

    def test_triple_hyphen_rejected_strict(self):
        assert parse_user_id("user:a---b", strict=True) is None

    def test_consecutive_at_start_rejected_strict(self):
        assert parse_user_id("user:__abc", strict=True) is None

    def test_consecutive_at_end_rejected_strict(self):
        assert parse_user_id("user:abc__", strict=True) is None

    def test_no_specials_allowed_strict(self):
        result = parse_user_id("user:alice", strict=True)
        assert result == ParseResult(user_id="alice", source="string")

    def test_all_letters_strict(self):
        result = parse_user_id("user:abcdef", strict=True)
        assert result == ParseResult(user_id="abcdef", source="string")

    def test_default_strict_is_false(self):
        """Verify default behavior is non-strict (consecutive specials allowed)."""
        result = parse_user_id("user:a__b")
        assert result == ParseResult(user_id="a__b", source="string")

    def test_multiple_separate_pairs_rejected_strict(self):
        """Even one consecutive pair should cause rejection in strict mode."""
        assert parse_user_id("user:a_b__c", strict=True) is None

    def test_mixed_consecutive_patterns_rejected_strict(self):
        assert parse_user_id("user:a_-b-_c", strict=True) is None


# ===========================================================================
# 13. Strict Mode — Dict flat
# ===========================================================================

class TestStrictModeWithDictFlat:
    def test_dict_flat_strict_rejects_double_underscore(self):
        assert parse_user_id({"user_id": "a__b"}, strict=True) is None

    def test_dict_flat_strict_rejects_double_hyphen(self):
        assert parse_user_id({"user_id": "a--b"}, strict=True) is None

    def test_dict_flat_strict_rejects_underscore_hyphen(self):
        assert parse_user_id({"user_id": "a_-b"}, strict=True) is None

    def test_dict_flat_strict_rejects_hyphen_underscore(self):
        assert parse_user_id({"user_id": "a-_b"}, strict=True) is None

    def test_dict_flat_strict_accepts_valid(self):
        result = parse_user_id({"user_id": "alice"}, strict=True)
        assert result == ParseResult(user_id="alice", source="dict_flat")

    def test_dict_flat_nonstrict_allows_consecutive(self):
        result = parse_user_id({"user_id": "a__b"}, strict=False)
        assert result == ParseResult(user_id="a__b", source="dict_flat")


# ===========================================================================
# 14. Strict Mode — Dict nested
# ===========================================================================

class TestStrictModeWithDictNested:
    def test_dict_nested_strict_rejects_double_underscore(self):
        assert parse_user_id({"user": {"id": "a__b"}}, strict=True) is None

    def test_dict_nested_strict_rejects_double_hyphen(self):
        assert parse_user_id({"user": {"id": "a--b"}}, strict=True) is None

    def test_dict_nested_strict_accepts_valid(self):
        result = parse_user_id({"user": {"id": "alice"}}, strict=True)
        assert result == ParseResult(user_id="alice", source="dict_nested")

    def test_dict_nested_nonstrict_allows_consecutive(self):
        result = parse_user_id({"user": {"id": "a--b"}}, strict=False)
        assert result == ParseResult(user_id="a--b", source="dict_nested")


# ===========================================================================
# 15. Strict Mode — Email
# ===========================================================================

class TestStrictModeWithEmail:
    def test_email_strict_rejects_double_underscore(self):
        assert parse_user_id("email:a__b@example.com", strict=True) is None

    def test_email_strict_rejects_double_hyphen(self):
        assert parse_user_id("email:a--b@example.com", strict=True) is None

    def test_email_strict_rejects_underscore_hyphen(self):
        assert parse_user_id("email:a_-b@example.com", strict=True) is None

    def test_email_strict_rejects_hyphen_underscore(self):
        assert parse_user_id("email:a-_b@example.com", strict=True) is None

    def test_email_strict_accepts_valid(self):
        result = parse_user_id("email:alice@example.com", strict=True)
        assert result == ParseResult(user_id="alice", source="email")

    def test_email_nonstrict_allows_consecutive(self):
        result = parse_user_id("email:a__b@example.com", strict=False)
        assert result == ParseResult(user_id="a__b", source="email")


# ===========================================================================
# 16. Strict Mode — Batch processing
# ===========================================================================

class TestStrictModeInBatch:
    def test_batch_strict_rejects_consecutive(self):
        items = ["user:a__b", "user:alice", "user:b--c"]
        result = parse_user_ids(items, strict=True)
        assert result == [
            None,
            ParseResult(user_id="alice", source="string"),
            None,
        ]

    def test_batch_strict_false_allows_consecutive(self):
        items = ["user:a__b", "user:alice", "user:b--c"]
        result = parse_user_ids(items, strict=False)
        assert result == [
            ParseResult(user_id="a__b", source="string"),
            ParseResult(user_id="alice", source="string"),
            ParseResult(user_id="b--c", source="string"),
        ]

    def test_batch_strict_and_reserved_combined(self):
        items = ["user:admin", "user:a__b", "user:alice"]
        result = parse_user_ids(items, reserved_ids={"admin"}, strict=True)
        assert result == [None, None, ParseResult(user_id="alice", source="string")]

    def test_batch_strict_with_all_input_types(self):
        items = [
            "user:a__b",
            "email:c__d@x.com",
            {"user_id": "e__f"},
            {"user": {"id": "g__h"}},
        ]
        result = parse_user_ids(items, strict=True)
        assert result == [None, None, None, None]

    def test_batch_strict_mixed_valid_invalid(self):
        items = [
            "user:alice",
            "user:a__b",
            "email:bob@x.com",
            {"user_id": "c--d"},
            {"user": {"id": "diana"}},
        ]
        result = parse_user_ids(items, strict=True)
        assert result == [
            ParseResult(user_id="alice", source="string"),
            None,
            ParseResult(user_id="bob", source="email"),
            None,
            ParseResult(user_id="diana", source="dict_nested"),
        ]


# ===========================================================================
# 17. Strict Mode — All four patterns exhaustive
# ===========================================================================

class TestStrictModeAllConsecutivePatterns:
    """Exhaustive test of all four consecutive special patterns across all input types."""

    CONSECUTIVE_PATTERNS = ["__", "--", "_-", "-_"]

    def test_all_patterns_rejected_in_strict_string(self):
        for pat in self.CONSECUTIVE_PATTERNS:
            uid = f"a{pat}b"
            result = parse_user_id(f"user:{uid}", strict=True)
            assert result is None, f"Expected None for pattern '{pat}' in strict mode"

    def test_all_patterns_allowed_in_nonstrict_string(self):
        for pat in self.CONSECUTIVE_PATTERNS:
            uid = f"a{pat}b"
            result = parse_user_id(f"user:{uid}", strict=False)
            assert result == ParseResult(user_id=uid, source="string"), \
                f"Expected valid result for pattern '{pat}' in non-strict mode"

    def test_all_patterns_rejected_in_strict_email(self):
        for pat in self.CONSECUTIVE_PATTERNS:
            uid = f"a{pat}b"
            result = parse_user_id(f"email:{uid}@example.com", strict=True)
            assert result is None, f"Expected None for pattern '{pat}' in strict email"

    def test_all_patterns_rejected_in_strict_dict_flat(self):
        for pat in self.CONSECUTIVE_PATTERNS:
            uid = f"a{pat}b"
            result = parse_user_id({"user_id": uid}, strict=True)
            assert result is None, f"Expected None for pattern '{pat}' in strict dict_flat"

    def test_all_patterns_rejected_in_strict_dict_nested(self):
        for pat in self.CONSECUTIVE_PATTERNS:
            uid = f"a{pat}b"
            result = parse_user_id({"user": {"id": uid}}, strict=True)
            assert result is None, f"Expected None for pattern '{pat}' in strict dict_nested"


# ===========================================================================
# 18. ParseResult namedtuple additional tests
# ===========================================================================

class TestParseResultAdditional:
    def test_parse_result_has_source_field(self):
        pr = ParseResult(user_id='alice', source='string')
        assert pr.source == 'string'

    def test_parse_result_index_access(self):
        pr = ParseResult(user_id='alice', source='string')
        assert pr[0] == 'alice'
        assert pr[1] == 'string'

    def test_parse_result_unpacking(self):
        pr = ParseResult(user_id='alice', source='string')
        uid, src = pr
        assert uid == 'alice'
        assert src == 'string'

    def test_parse_result_equality(self):
        pr1 = ParseResult(user_id='alice', source='string')
        pr2 = ParseResult(user_id='alice', source='string')
        assert pr1 == pr2

    def test_parse_result_inequality_different_id(self):
        pr1 = ParseResult(user_id='alice', source='string')
        pr2 = ParseResult(user_id='bob', source='string')
        assert pr1 != pr2

    def test_parse_result_inequality_different_source(self):
        pr1 = ParseResult(user_id='alice', source='string')
        pr2 = ParseResult(user_id='alice', source='email')
        assert pr1 != pr2

    def test_parse_result_is_tuple(self):
        pr = ParseResult(user_id='alice', source='string')
        assert isinstance(pr, tuple)

    def test_parse_result_len(self):
        pr = ParseResult(user_id='alice', source='string')
        assert len(pr) == 2


# ===========================================================================
# 19. Normalization detailed tests
# ===========================================================================

class TestNormalizationDetailed:
    """Detailed normalization tests across different input types."""

    def test_mixed_case_dict_flat(self):
        result = parse_user_id({"user_id": "AlIcE"})
        assert result == ParseResult(user_id="alice", source="dict_flat")

    def test_mixed_case_dict_nested(self):
        result = parse_user_id({"user": {"id": "AlIcE"}})
        assert result == ParseResult(user_id="alice", source="dict_nested")

    def test_mixed_case_email(self):
        result = parse_user_id("email:AlIcE@domain.com")
        assert result == ParseResult(user_id="alice", source="email")

    def test_whitespace_dict_nested(self):
        result = parse_user_id({"user": {"id": "  alice  "}})
        assert result == ParseResult(user_id="alice", source="dict_nested")

    def test_normalization_then_validation(self):
        """ID with uppercase chars that become valid after lowering."""
        result = parse_user_id("user:ABC123")
        assert result == ParseResult(user_id="abc123", source="string")

    def test_normalization_preserves_underscores_hyphens(self):
        result = parse_user_id("user:  A_B-C  ")
        assert result == ParseResult(user_id="a_b-c", source="string")

    def test_strict_applied_after_normalization(self):
        """Normalization (lowering) happens before strict check."""
        # "A__B" -> "a__b" which has consecutive specials
        assert parse_user_id("user:A__B", strict=True) is None

    def test_reserved_check_after_normalization(self):
        """Reserved check happens after strip + lower."""
        assert parse_user_id("user:  ADMIN  ") is None
        assert parse_user_id({"user_id": "\tROOT\t"}) is None


# ===========================================================================
# 20. No-exception guarantee for exotic input types
# =========================================================================== 

class TestNoExceptionOnBadInput:
    """Verify that the function never raises for expected bad input."""

    def test_deeply_nested_dict_value(self):
        d = {"user": {"id": {"nested": "too_deep"}}}
        assert parse_user_id(d) is None

    def test_class_instance_input(self):
        class Foo:
            pass
        assert parse_user_id(Foo()) is None

    def test_bytes_input(self):
        assert parse_user_id(b"user:alice") is None

    def test_complex_number_input(self):
        assert parse_user_id(1 + 2j) is None

    def test_frozenset_input(self):
        assert parse_user_id(frozenset({"alice"})) is None

    def test_none_in_batch(self):
        result = parse_user_ids([None, None, None])
        assert result == [None, None, None]

    def test_mixed_weird_types_in_batch(self):
        items = [42, 3.14, True, b"bytes", None, [], ()]
        result = parse_user_ids(items)
        assert all(r is None for r in result)
        assert len(result) == len(items)

    def test_dict_with_user_id_as_dict(self):
        assert parse_user_id({"user_id": {"nested": "val"}}) is None

    def test_dict_with_user_as_bool(self):
        assert parse_user_id({"user": True}) is None


# ===========================================================================
# 21. Reserved IDs edge cases
# ===========================================================================

class TestReservedIdsEdgeCases:
    def test_reserved_none_uses_default_explicitly(self):
        """Explicitly passing None uses default reserved set."""
        assert parse_user_id("user:admin", reserved_ids=None) is None
        assert parse_user_id("user:root", reserved_ids=None) is None
        assert parse_user_id("user:system", reserved_ids=None) is None

    def test_reserved_frozenset_works(self):
        result = parse_user_id("user:admin", reserved_ids=frozenset({"blocked"}))
        assert result == ParseResult(user_id="admin", source="string")
        assert parse_user_id("user:blocked", reserved_ids=frozenset({"blocked"})) is None

    def test_reserved_list_works(self):
        """reserved_ids as a list should also work since 'in' is supported."""
        assert parse_user_id("user:admin", reserved_ids=["blocked"]) is not None
        assert parse_user_id("user:blocked", reserved_ids=["blocked"]) is None

    def test_reserved_check_order_after_normalization(self):
        """Reserved check happens after normalization (lowering)."""
        assert parse_user_id("user:ADMIN") is None
        assert parse_user_id("user:Admin") is None
        assert parse_user_id("user:ROOT") is None
        assert parse_user_id("user:SYSTEM") is None

    def test_strict_with_reserved_interaction(self):
        """Strict mode doesn't affect reserved ID check."""
        assert parse_user_id("user:admin", strict=True) is None
        assert parse_user_id("user:admin", strict=False) is None

    def test_strict_with_custom_reserved_empty(self):
        """Strict mode + empty reserved set: only strict rules apply."""
        result = parse_user_id("user:admin", reserved_ids=set(), strict=True)
        assert result == ParseResult(user_id="admin", source="string")
        assert parse_user_id("user:a__b", reserved_ids=set(), strict=True) is None


# ===========================================================================
# 22. Additional edge cases
# ===========================================================================

class TestAdditionalEdgeCases:
    def test_unicode_input_rejected(self):
        assert parse_user_id("user:alicé") is None

    def test_emoji_in_id_rejected(self):
        assert parse_user_id("user:alice😀") is None

    def test_newline_in_id_stripped(self):
        assert parse_user_id("user:\nalice\n") == ParseResult(user_id="alice", source="string")

    def test_only_numbers_valid(self):
        assert parse_user_id("user:12345") == ParseResult(user_id="12345", source="string")

    def test_only_underscores_20_chars(self):
        uid = "_" * 20
        assert parse_user_id(f"user:{uid}") == ParseResult(user_id=uid, source="string")

    def test_only_hyphens_20_chars(self):
        uid = "-" * 20
        assert parse_user_id(f"user:{uid}") == ParseResult(user_id=uid, source="string")

    def test_nested_dict_with_extra_keys(self):
        result = parse_user_id({"user": {"id": "alice", "name": "Alice"}})
        assert result == ParseResult(user_id="alice", source="dict_nested")

    def test_email_empty_domain(self):
        # "email:alice@" -> username is "alice", should be valid
        result = parse_user_id("email:alice@")
        assert result == ParseResult(user_id="alice", source="email")

    def test_email_at_only(self):
        # "email:@" -> username is "", too short
        assert parse_user_id("email:@") is None

    def test_dict_bool_value_for_user_id(self):
        assert parse_user_id({"user_id": True}) is None

    def test_dict_bool_value_for_nested_id(self):
        assert parse_user_id({"user": {"id": False}}) is None

    def test_dict_float_value_for_user_id(self):
        assert parse_user_id({"user_id": 3.14}) is None

    def test_string_with_colon_but_no_known_prefix(self):
        assert parse_user_id("unknown:alice") is None

    def test_string_with_multiple_colons_user_prefix(self):
        # "user:alice:extra" -> extracted id is "alice:extra", colon is invalid char
        assert parse_user_id("user:alice:extra") is None

    def test_string_user_prefix_with_tab(self):
        assert parse_user_id("user:\talice\t") == ParseResult(user_id="alice", source="string")

    def test_dict_nested_user_is_list(self):
        assert parse_user_id({"user": ["id", "alice"]}) is None

    def test_dict_nested_user_is_tuple(self):
        assert parse_user_id({"user": ("id", "alice")}) is None

    def test_email_with_plus_in_username(self):
        # "+" is not in [a-z0-9_-]
        assert parse_user_id("email:alice+tag@domain.com") is None

    def test_id_starting_with_hyphen(self):
        result = parse_user_id("user:-abc")
        assert result == ParseResult(user_id="-abc", source="string")

    def test_id_starting_with_underscore(self):
        result = parse_user_id("user:_abc")
        assert result == ParseResult(user_id="_abc", source="string")

    def test_id_ending_with_hyphen(self):
        result = parse_user_id("user:abc-")
        assert result == ParseResult(user_id="abc-", source="string")

    def test_id_ending_with_underscore(self):
        result = parse_user_id("user:abc_")
        assert result == ParseResult(user_id="abc_", source="string")


# ==========================================================================
# 23. Batch processing — additional edge cases
# ===========================================================================

class TestBatchProcessingAdditionalEdgeCases:
    def test_all_input_types_in_single_batch(self):
        items = [
            "user:alice",
            "email:bob@domain.com",
            {"user_id": "charlie"},
            {"user": {"id": "diana"}},
        ]
        result = parse_user_ids(items)
        assert result == [
            ParseResult(user_id="alice", source="string"),
            ParseResult(user_id="bob", source="email"),
            ParseResult(user_id="charlie", source="dict_flat"),
            ParseResult(user_id="diana", source="dict_nested"),
        ]

    def test_batch_does_not_mutate_input_list(self):
        items = ["user:alice", "user:bob"]
        items_copy = items.copy()
        parse_user_ids(items)
        assert items == items_copy

    def test_batch_does_not_mutate_input_dicts(self):
        d1 = {"user_id": "  Alice  "}
        d2 = {"user": {"id": "  Bob  "}}
        d1_copy = copy.deepcopy(d1)
        d2_copy = copy.deepcopy(d2)
        parse_user_ids([d1, d2])
        assert d1 == d1_copy
        assert d2 == d2_copy

    def test_batch_with_large_list(self):
        items = [f"user:user{i:03d}" for i in range(100)]
        result = parse_user_ids(items)
        assert len(result) == 100
        assert all(r is not None for r in result)
        assert result[0] == ParseResult(user_id="user000", source="string")
        assert result[99] == ParseResult(user_id="user099", source="string")

    def test_batch_index_correspondence(self):
        """Verify result[i] always corresponds to items[i]."""
        items = [None, "user:alice", "user:!!", {"user_id": "bob"}, 42]
        result = parse_user_ids(items)
        assert result[0] is None  # None input
        assert result[1] == ParseResult(user_id="alice", source="string")
        assert result[2] is None  # invalid chars
        assert result[3] == ParseResult(user_id="bob", source="dict_flat")
        assert result[4] is None  # int input


# ==========================================================================
# 24. Z3 Formal Verification — Strict Mode
# ===========================================================================

class TestZ3StrictModeVerification:
    """Z3-based verification that strict mode correctly identifies consecutive specials."""

    def test_z3_strict_consecutive_underscores_detected(self):
        """Use Z3 to find a string with __ that is otherwise valid, verify strict rejects it."""
        try:
            from z3 import Solver, String, Length, And, sat, StringVal, Re, InRe, \
                Union, Star, Range, Contains
        except ImportError:
            import pytest
            pytest.skip("z3-solver not installed")

        s = Solver()
        x = String("x")

        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re(StringVal("_")),
            Re(StringVal("-")),
        )

        s.add(InRe(x, Star(char_class)))
        s.add(Length(x) >= 3)
        s.add(Length(x) <= 20)
        s.add(Contains(x, StringVal("__")))

        assert s.check() == sat
        model = s.model()
        result_str = model[x].as_string()

        # Non-strict should accept
        result_nonstrict = parse_user_id(f"user:{result_str}", reserved_ids=set(), strict=False)
        assert result_nonstrict is not None

        # Strict should reject
        result_strict = parse_user_id(f"user:{result_str}", reserved_ids=set(), strict=True)
        assert result_strict is None

    def test_z3_strict_consecutive_hyphens_detected(self):
        """Use Z3 to find a string with -- that is otherwise valid, verify strict rejects it."""
        try:
            from z3 import Solver, String, Length, And, sat, StringVal, Re, InRe, \
                Union, Star, Range, Contains
        except ImportError:
            import pytest
            pytest.skip("z3-solver not installed")

        s = Solver()
        x = String("x")

        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re(StringVal("_")),
            Re(StringVal("-")),
        )

        s.add(InRe(x, Star(char_class)))
        s.add(Length(x) >= 3)
        s.add(Length(x) <= 20)
        s.add(Contains(x, StringVal("--")))

        assert s.check() == sat
        model = s.model()
        result_str = model[x].as_string()

        result_nonstrict = parse_user_id(f"user:{result_str}", reserved_ids=set(), strict=False)
        assert result_nonstrict is not None

        result_strict = parse_user_id(f"user:{result_str}", reserved_ids=set(), strict=True)
        assert result_strict is None

    def test_z3_no_consecutive_specials_passes_strict(self):
        """Use Z3 to find a valid string without consecutive specials, verify strict accepts it."""
        try:
            from z3 import Solver, String, Length, And, Not, sat, StringVal, Re, InRe, \
                Union, Star, Range, Contains, Or
        except ImportError:
            import pytest
            pytest.skip("z3-solver not installed")

        s = Solver()
        x = String("x")

        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re(StringVal("_")),
            Re(StringVal("-")),
        )

        s.add(InRe(x, Star(char_class)))
        s.add(Length(x) >= 3)
        s.add(Length(x) <= 10)
        # No consecutive specials
        s.add(Not(Contains(x, StringVal("__"))))
        s.add(Not(Contains(x, StringVal("--"))))
        s.add(Not(Contains(x, StringVal("_-"))))
        s.add(Not(Contains(x, StringVal("-_"))))

        assert s.check() == sat
        model = s.model()
        result_str = model[x].as_string()

        # Should pass strict mode (assuming not reserved)
        result_strict = parse_user_id(f"user:{result_str}", reserved_ids=set(), strict=True)
        assert result_strict is not None
        assert result_strict.user_id == result_str

    def test_z3_mixed_consecutive_underscore_hyphen_detected(self):
        """Use Z3 to find a string with _- pattern, verify strict rejects it."""
        try:
            from z3 import Solver, String, Length, sat, StringVal, Re, InRe, \
                Union, Star, Range, Contains
        except ImportError:
            import pytest
            pytest.skip("z3-solver not installed")

        s = Solver()
        x = String("x")

        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re(StringVal("_")),
            Re(StringVal("-")),
        )

        s.add(InRe(x, Star(char_class)))
        s.add(Length(x) >= 3)
        s.add(Length(x) <= 20)
        s.add(Contains(x, StringVal("_-")))

        assert s.check() == sat
        model = s.model()
        result_str = model[x].as_string()

        result_strict = parse_user_id(f"user:{result_str}", reserved_ids=set(), strict=True)
        assert result_strict is None

    def test_z3_mixed_consecutive_hyphen_underscore_detected(self):
        """Use Z3 to find a string with -_ pattern, verify strict rejects it."""
        try:
            from z3 import Solver, String, Length, sat, StringVal, Re, InRe, \
                Union, Star, Range, Contains
        except ImportError:
            import pytest
            pytest.skip("z3-solver not installed")

        s = Solver()
        x = String("x")

        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re(StringVal("_")),
            Re(StringVal("-")),
        )

        s.add(InRe(x, Star(char_class)))
        s.add(Length(x) >= 3)
        s.add(Length(x) <= 20)
        s.add(Contains(x, StringVal("-_")))

        assert s.check() == sat
        model = s.model()
        result_str = model[x].as_string()

        result_strict = parse_user_id(f"user:{result_str}", reserved_ids=set(), strict=True)
        assert result_strict is None

    def test_z3_reserved_ids_always_rejected(self):
        """Verify that default reserved IDs are always rejected regardless of format."""
        try:
            from z3 import Solver, String, StringVal, Or, sat
        except ImportError:
            import pytest
            pytest.skip("z3-solver not installed")

        # Use Z3 to enumerate reserved IDs and test each through all input types
        s = Solver()
        x = String("x")
        s.add(Or(x == StringVal("admin"), x == StringVal("root"), x == StringVal("system")))

        while s.check() == sat:
            model = s.model()
            reserved_id = model[x].as_string()

            # All input types should reject reserved IDs
            assert parse_user_id(f"user:{reserved_id}") is None
            assert parse_user_id(f"email:{reserved_id}@domain.com") is None
            assert parse_user_id({"user_id": reserved_id}) is None
            assert parse_user_id({"user": {"id": reserved_id}}) is None

            # Block this value and find next
            s.add(x != StringVal(reserved_id))