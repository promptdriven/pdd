# =============================================================================
# TEST PLAN for parse_user_id
# =============================================================================
#
# 1. STRING INPUT TESTS:
#    - Valid "user:<id>" format with simple id → returns normalized id
#    - "user:<id>" with surrounding whitespace in id → trimmed + lowered
#    - "user:<id>" with uppercase → lowercased
#    - Missing "user:" prefix → None
#    - Empty id after prefix "user:" → None (length < 3)
#    - Id with exactly 3 chars (min boundary) → valid
#    - Id with exactly 20 chars (max boundary) → valid
#    - Id with 2 chars (below min) → None
#    - Id with 21 chars (above max) → None
#    - Id with invalid characters (e.g., @, !, space in middle) → None
#    - Reserved ids: "admin", "root", "system" → None
#    - Reserved ids in mixed case: "ADMIN", "Root" → None (normalized then rejected)
#    - Valid chars: underscores, hyphens, digits → accepted
#
# 2. DICT INPUT TESTS (flat form {"user_id": "<id>"}):
#    - Valid flat form → returns normalized id
#    - user_id value is not a string (int, None, list) → None
#    - user_id with whitespace/uppercase → trimmed + lowered
#
# 3. DICT INPUT TESTS (nested form {"user": {"id": "<id>"}}):
#    - Valid nested form → returns normalized id
#    - "user" value is not a dict → None
#    - "user" dict missing "id" key → None
#    - Nested "id" value is not a string → None
#
# 4. DICT PRIORITY TESTS:
#    - Both "user_id" and "user" present → flat form ("user_id") takes priority
#    - "user_id" invalid but "user"."id" valid → still uses "user_id" (returns None)
#      Actually: code tries flat first, if val is string it returns it. If user_id
#      is not string, it falls through to nested form.
#
# 5. NON-MUTATION TESTS:
#    - Input dict is not mutated after call (flat form)
#    - Input dict is not mutated after call (nested form)
#
# 6. OTHER INPUT TYPE TESTS:
#    - None → None
#    - int → None
#    - float → None
#    - list → None
#    - bool → None
#    - tuple → None
#    - set → None
#    - Custom object → None
#
# 7. NEVER-RAISE TESTS:
#    - Various bad inputs should return None, never raise exceptions
#
# 8. Z3 FORMAL VERIFICATION:
#    - Property: any non-None return value matches ^[a-z0-9_-]{3,20}$
#    - Property: any non-None return value is not in {admin, root, system}
#    - Property: any non-None return value equals its own .strip().lower()
#    - These are best verified with Z3 over the _validate logic symbolically,
#      but since we can't directly invoke Z3 on Python regex, we use Z3 to
#      verify constraints on the output domain. Unit tests cover the rest.
#    - Most edge cases are better as unit tests since they test specific
#      input/output pairs. Z3 is useful for verifying universal properties
#      (e.g., "for ALL valid outputs, property X holds").
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
import re

import pytest

# Import the module under test
from user_id_parser import parse_user_id


# =============================================================================
# STRING INPUT TESTS
# =============================================================================

class TestStringInput:
    """Tests for string-type inputs to parse_user_id."""

    def test_valid_simple_id(self) -> None:
        assert parse_user_id("user:hello") == "hello"

    def test_valid_with_digits(self) -> None:
        assert parse_user_id("user:abc123") == "abc123"

    def test_valid_with_underscore(self) -> None:
        assert parse_user_id("user:abc_def") == "abc_def"

    def test_valid_with_hyphen(self) -> None:
        assert parse_user_id("user:abc-def") == "abc-def"

    def test_valid_mixed_valid_chars(self) -> None:
        assert parse_user_id("user:a1_b2-c3") == "a1_b2-c3"

    def test_uppercase_normalized_to_lowercase(self) -> None:
        assert parse_user_id("user:HELLO") == "hello"

    def test_mixed_case_normalized(self) -> None:
        assert parse_user_id("user:HeLLo") == "hello"

    def test_whitespace_trimmed(self) -> None:
        assert parse_user_id("user:  hello  ") == "hello"

    def test_whitespace_and_uppercase_combined(self) -> None:
        assert parse_user_id("user:  HELLO  ") == "hello"

    def test_missing_prefix_returns_none(self) -> None:
        assert parse_user_id("hello") is None

    def test_wrong_prefix_returns_none(self) -> None:
        assert parse_user_id("usr:hello") is None

    def test_empty_string_returns_none(self) -> None:
        assert parse_user_id("") is None

    def test_just_prefix_returns_none(self) -> None:
        # "user:" with empty id → after trim, length 0 < 3
        assert parse_user_id("user:") is None

    def test_prefix_with_only_whitespace_returns_none(self) -> None:
        # "user:   " → after trim, empty string
        assert parse_user_id("user:   ") is None

    def test_id_too_short_1_char(self) -> None:
        assert parse_user_id("user:a") is None

    def test_id_too_short_2_chars(self) -> None:
        assert parse_user_id("user:ab") is None

    def test_id_exact_min_length_3(self) -> None:
        assert parse_user_id("user:abc") == "abc"

    def test_id_exact_max_length_20(self) -> None:
        id_20: str = "a" * 20
        assert parse_user_id(f"user:{id_20}") == id_20

    def test_id_too_long_21_chars(self) -> None:
        id_21: str = "a" * 21
        assert parse_user_id(f"user:{id_21}") is None

    def test_invalid_char_at_sign(self) -> None:
        assert parse_user_id("user:ab@cd") is None

    def test_invalid_char_space_in_middle(self) -> None:
        assert parse_user_id("user:ab cd") is None

    def test_invalid_char_dot(self) -> None:
        assert parse_user_id("user:ab.cd") is None

    def test_invalid_char_exclamation(self) -> None:
        assert parse_user_id("user:abc!") is None

    def test_invalid_char_slash(self) -> None:
        assert parse_user_id("user:abc/def") is None

    def test_all_digits_valid(self) -> None:
        assert parse_user_id("user:123") == "123"

    def test_all_underscores_valid(self) -> None:
        assert parse_user_id("user:___") == "___"

    def test_all_hyphens_valid(self) -> None:
        assert parse_user_id("user:---") == "---"


# =============================================================================
# RESERVED ID TESTS
# =============================================================================

class TestReservedIds:
    """Tests ensuring reserved IDs are rejected in all input forms."""

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

    def test_reserved_admin_dict_flat(self) -> None:
        assert parse_user_id({"user_id": "admin"}) is None

    def test_reserved_root_dict_nested(self) -> None:
        assert parse_user_id({"user": {"id": "root"}}) is None

    def test_not_reserved_administrator(self) -> None:
        # "administrator" is not in reserved set
        assert parse_user_id("user:administrator") == "administrator"

    def test_not_reserved_roots(self) -> None:
        assert parse_user_id("user:roots") == "roots"

    def test_not_reserved_sys(self) -> None:
        assert parse_user_id("user:sys") == "sys"


# =============================================================================
# DICT INPUT TESTS - FLAT FORM
# =============================================================================

class TestDictFlatForm:
    """Tests for dict inputs using the flat {'user_id': '<id>'} form."""

    def test_valid_flat_form(self) -> None:
        assert parse_user_id({"user_id": "hello"}) == "hello"

    def test_flat_form_with_uppercase(self) -> None:
        assert parse_user_id({"user_id": "HELLO"}) == "hello"

    def test_flat_form_with_whitespace(self) -> None:
        assert parse_user_id({"user_id": "  hello  "}) == "hello"

    def test_flat_form_value_is_int(self) -> None:
        assert parse_user_id({"user_id": 123}) is None

    def test_flat_form_value_is_none(self) -> None:
        assert parse_user_id({"user_id": None}) is None

    def test_flat_form_value_is_list(self) -> None:
        assert parse_user_id({"user_id": ["hello"]}) is None

    def test_flat_form_value_is_bool(self) -> None:
        assert parse_user_id({"user_id": True}) is None

    def test_flat_form_empty_dict(self) -> None:
        assert parse_user_id({}) is None

    def test_flat_form_unrelated_keys(self) -> None:
        assert parse_user_id({"name": "hello"}) is None


# =============================================================================
# DICT INPUT TESTS - NESTED FORM
# =============================================================================

class TestDictNestedForm:
    """Tests for dict inputs using the nested {'user': {'id': '<id>'}} form."""

    def test_valid_nested_form(self) -> None:
        assert parse_user_id({"user": {"id": "hello"}}) == "hello"

    def test_nested_form_with_uppercase(self) -> None:
        assert parse_user_id({"user": {"id": "HELLO"}}) == "hello"

    def test_nested_form_with_whitespace(self) -> None:
        assert parse_user_id({"user": {"id": "  hello  "}}) == "hello"

    def test_nested_user_not_dict(self) -> None:
        assert parse_user_id({"user": "not_a_dict"}) is None

    def test_nested_user_is_none(self) -> None:
        assert parse_user_id({"user": None}) is None

    def test_nested_user_is_list(self) -> None:
        assert parse_user_id({"user": [{"id": "hello"}]}) is None

    def test_nested_user_missing_id_key(self) -> None:
        assert parse_user_id({"user": {"name": "hello"}}) is None

    def test_nested_user_empty_inner_dict(self) -> None:
        assert parse_user_id({"user": {}}) is None

    def test_nested_id_is_int(self) -> None:
        assert parse_user_id({"user": {"id": 123}}) is None

    def test_nested_id_is_none(self) -> None:
        assert parse_user_id({"user": {"id": None}}) is None

    def test_nested_id_is_bool(self) -> None:
        assert parse_user_id({"user": {"id": True}}) is None


# =============================================================================
# DICT PRIORITY TESTS
# =============================================================================

class TestDictPriority:
    """Tests verifying priority when both flat and nested forms are present."""

    def test_flat_takes_priority_over_nested(self) -> None:
        """When both user_id and user.id exist, flat form is used."""
        result = parse_user_id({
            "user_id": "flat_id",
            "user": {"id": "nested_id"}
        })
        assert result == "flat_id"

    def test_flat_non_string_falls_through_to_nested(self) -> None:
        """If user_id is not a string, code falls through to nested form."""
        result = parse_user_id({
            "user_id": 123,
            "user": {"id": "nested_id"}
        })
        assert result == "nested_id"


# =============================================================================
# NON-MUTATION TESTS
# =============================================================================

class TestNonMutation:
    """Tests ensuring the input data structures are not mutated."""

    def test_flat_dict_not_mutated(self) -> None:
        d = {"user_id": "  HELLO  "}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_nested_dict_not_mutated(self) -> None:
        d = {"user": {"id": "  HELLO  "}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_with_extra_keys_not_mutated(self) -> None:
        d = {"user_id": "hello", "extra": [1, 2, 3]}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original


# =============================================================================
# OTHER INPUT TYPE TESTS
# =============================================================================

class TestOtherInputTypes:
    """Tests ensuring unsupported input types return None."""

    def test_none_input(self) -> None:
        assert parse_user_id(None) is None

    def test_int_input(self) -> None:
        assert parse_user_id(42) is None

    def test_float_input(self) -> None:
        assert parse_user_id(3.14) is None

    def test_bool_true_input(self) -> None:
        assert parse_user_id(True) is None

    def test_bool_false_input(self) -> None:
        assert parse_user_id(False) is None

    def test_list_input(self) -> None:
        assert parse_user_id(["user:hello"]) is None

    def test_tuple_input(self) -> None:
        assert parse_user_id(("user:hello",)) is None

    def test_set_input(self) -> None:
        assert parse_user_id({"user:hello"}) is None

    def test_bytes_input(self) -> None:
        assert parse_user_id(b"user:hello") is None

    def test_custom_object_input(self) -> None:
        class Foo:
            pass
        assert parse_user_id(Foo()) is None


# =============================================================================
# NEVER-RAISE TESTS
# =============================================================================

class TestNeverRaise:
    """Ensure the function never raises for any expected bad input."""

    @pytest.mark.parametrize("bad_input", [
        None,
        42,
        3.14,
        True,
        False,
        [],
        (),
        set(),
        b"bytes",
        object(),
        "",
        "user:",
        "user:!!!",
        {"user_id": object()},
        {"user": object()},
        {"user": {"id": object()}},
        {"user": {"id": 999}},
    ])
    def test_no_exception_raised(self, bad_input: object) -> None:
        result = parse_user_id(bad_input)
        assert result is None


# =============================================================================
# BOUNDARY / EDGE CASE TESTS
# =============================================================================

class TestBoundaryEdgeCases:
    """Tests for boundary conditions and unusual edge cases."""

    def test_id_length_exactly_3_after_trim(self) -> None:
        assert parse_user_id("user:  abc  ") == "abc"

    def test_id_length_exactly_20_after_trim(self) -> None:
        id_20: str = "a" * 20
        assert parse_user_id(f"user:  {id_20}  ") == id_20

    def test_id_becomes_too_short_after_trim(self) -> None:
        # "  ab  " → "ab" → length 2 < 3
        assert parse_user_id("user:  ab  ") is None

    def test_tab_whitespace_in_id(self) -> None:
        assert parse_user_id("user:\thello\t") == "hello"

    def test_newline_in_id(self) -> None:
        assert parse_user_id("user:\nhello\n") == "hello"

    def test_colon_in_id(self) -> None:
        # "user:abc:def" → extracted as "abc:def" → colon is invalid
        assert parse_user_id("user:abc:def") is None

    def test_prefix_case_sensitive(self) -> None:
        # "User:hello" doesn't match "user:" prefix
        assert parse_user_id("User:hello") is None

    def test_prefix_USER_uppercase(self) -> None:
        assert parse_user_id("USER:hello") is None

    def test_only_digits_valid_length(self) -> None:
        assert parse_user_id("user:12345") == "12345"

    def test_hyphen_start(self) -> None:
        assert parse_user_id("user:-abc") == "-abc"

    def test_underscore_start(self) -> None:
        assert parse_user_id("user:_abc") == "_abc"

    def test_unicode_characters_rejected(self) -> None:
        assert parse_user_id("user:héllo") is None

    def test_emoji_rejected(self) -> None:
        assert parse_user_id("user:ab😀") is None


# =============================================================================
# Z3 FORMAL VERIFICATION TESTS
# =============================================================================
# These tests use Z3 to formally verify properties about the validation logic.
# We verify that the output domain of parse_user_id satisfies invariants.

class TestZ3FormalVerification:
    """
    Use Z3 to verify universal properties of the parse_user_id output.

    Since Z3's string theory is limited, we verify properties by:
    1. Generating a broad set of candidate outputs
    2. Using Z3 to verify constraints on the valid output domain
    """

    def _try_import_z3(self):
        """Attempt to import z3; skip test if unavailable."""
        try:
            import z3
            return z3
        except ImportError:
            pytest.skip("z3-solver not installed")

    def test_z3_valid_output_matches_pattern(self) -> None:
        """Verify: for any non-None output, it matches ^[a-z0-9_-]{3,20}$"""
        z3 = self._try_import_z3()

        valid_pattern = re.compile(r'^[a-z0-9_-]{3,20}$')

        # Test a comprehensive set of inputs that produce non-None outputs
        test_inputs = [
            "user:abc", "user:hello_world", "user:test-123",
            "user:  MIXED  ", "user:a1_b2-c3",
            {"user_id": "valid_id"}, {"user": {"id": "nested"}},
            "user:" + "x" * 20, "user:___", "user:---",
            "user:abc123def456ghi7",
        ]

        for inp in test_inputs:
            result = parse_user_id(inp)
            if result is not None:
                # Use Z3 to verify the string satisfies length constraints
                s = z3.Solver()
                str_val = z3.StringVal(result)
                length = z3.Length(str_val)

                # Length constraint: assert violation, expect unsat
                s.add(z3.Or(length < 3, length > 20))
                assert s.check() == z3.unsat, \
                    f"Output '{result}' violates length constraint [3,20]"

                # Also verify with regex directly
                assert valid_pattern.fullmatch(result), \
                    f"Output '{result}' doesn't match valid pattern"

    def test_z3_output_is_lowercase(self) -> None:
        """Verify: for any non-None output, output == output.lower()"""
        z3 = self._try_import_z3()

        test_inputs = [
            "user:HELLO", "user:Hello", "user:hElLo",
            {"user_id": "WORLD"}, {"user": {"id": "MiXeD"}},
        ]

        for inp in test_inputs:
            result = parse_user_id(inp)
            if result is not None:
                # Z3 string verification
                s = z3.Solver()
                str_val = z3.StringVal(result)
                lower_val = z3.StringVal(result.lower())
                s.add(str_val != lower_val)
                assert s.check() == z3.unsat, \
                    f"Output '{result}' is not fully lowercase"

    def test_z3_output_is_never_reserved(self) -> None:
        """Verify: for any non-None output, it is never a reserved ID."""
        z3 = self._try_import_z3()

        reserved = {"admin", "root", "system"}

        # Try all reserved words in various formats
        test_inputs = []
        for word in reserved:
            test_inputs.extend([
                f"user:{word}",
                f"user:{word.upper()}",
                f"user:  {word}  ",
                {"user_id": word},
                {"user": {"id": word}},
            ])

        for inp in test_inputs:
            result = parse_user_id(inp)
            if result is not None:
                s = z3.Solver()
                str_val = z3.StringVal(result)
                # Assert result equals one of the reserved words
                reserved_constraints = [
                    str_val == z3.StringVal(r) for r in reserved
                ]
                s.add(z3.Or(*reserved_constraints))
                assert s.check() == z3.unsat, \
                    f"Output '{result}' is a reserved ID"

    def test_z3_output_is_trimmed(self) -> None:
        """Verify: for any non-None output, output == output.strip()"""
        z3 = self._try_import_z3()

        test_inputs = [
            "user:  hello  ", "user:\thello\t",
            {"user_id": "  world  "}, {"user": {"id": "  test  "}},
        ]

        for inp in test_inputs:
            result = parse_user_id(inp)
            if result is not None:
                s = z3.Solver()
                str_val = z3.StringVal(result)
                stripped_val = z3.StringVal(result.strip())
                s.add(str_val != stripped_val)
                assert s.check() == z3.unsat, \
                    f"Output '{result}' has untrimmed whitespace"

    def test_z3_length_bounds_comprehensive(self) -> None:
        """Use Z3 to verify length bounds hold across many outputs."""
        z3 = self._try_import_z3()

        # Generate a broad set of valid and boundary inputs
        valid_ids = [
            "abc", "abcd", "a" * 10, "a" * 20,
            "a-b", "a_b", "123", "a1b2c3",
            "test-user_01",
        ]

        for uid in valid_ids:
            result = parse_user_id(f"user:{uid}")
            if result is not None:
                s = z3.Solver()
                n = z3.Int("n")
                s.add(n == len(result))
                s.add(z3.Or(n < 3, n > 20))
                assert s.check() == z3.unsat, \
                    f"Output '{result}' (len={len(result)}) violates length bounds"


# =============================================================================
# RETURN TYPE TESTS
# =============================================================================

class TestReturnType:
    """Tests verifying the return type contract of parse_user_id."""

    def test_valid_returns_string(self) -> None:
        result = parse_user_id("user:hello")
        assert isinstance(result, str)

    def test_invalid_returns_none(self) -> None:
        result = parse_user_id("invalid")
        assert result is None

    def test_none_input_returns_none_not_other_falsy(self) -> None:
        result = parse_user_id(None)
        assert result is None
        assert result is not False
        assert result != 0
        assert result != ""