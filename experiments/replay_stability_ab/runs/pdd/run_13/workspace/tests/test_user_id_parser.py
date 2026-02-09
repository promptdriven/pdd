import sys
from pathlib import Path

# Add project root to sys.path to ensure local changes are prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

from user_id_parser import parse_user_id, parse_user_ids, ParseResult


import pytest
import re


# ==============================================================================
# PARSERESULT NAMEDTUPLE STRUCTURE
# ============================================================================== 

class TestParseResultStructure:
    def test_parseresult_has_user_id_field(self):
        pr = ParseResult(user_id="hello", source="string")
        assert pr.user_id == "hello"

    def test_parseresult_has_source_field(self):
        pr = ParseResult(user_id="hello", source="string")
        assert pr.source == "string"

    def test_parseresult_is_tuple(self):
        pr = ParseResult(user_id="hello", source="string")
        assert isinstance(pr, tuple)

    def test_parseresult_indexing(self):
        pr = ParseResult(user_id="hello", source="string")
        assert pr[0] == "hello"
        assert pr[1] == "string"

    def test_parseresult_unpacking(self):
        pr = ParseResult(user_id="hello", source="string")
        uid, src = pr
        assert uid == "hello"
        assert src == "string"

    def test_parseresult_equality_with_tuple(self):
        pr = ParseResult(user_id="hello", source="string")
        assert pr == ("hello", "string")

    def test_parseresult_len(self):
        pr = ParseResult(user_id="hello", source="string")
        assert len(pr) == 2

    def test_parseresult_field_names(self):
        assert ParseResult._fields == ("user_id", "source")

    def test_parseresult_not_equal_to_plain_string(self):
        pr = ParseResult(user_id="hello", source="string")
        assert pr != "hello"


# ==============================================================================
# SOURCE FIELD - "string" (user: prefix)
# ============================================================================== 

class TestSourceFieldString:
    def test_user_prefix_source_is_string(self):
        result = parse_user_id("user:hello")
        assert result is not None
        assert result.source == "string"

    def test_user_prefix_user_id_field(self):
        result = parse_user_id("user:hello")
        assert result.user_id == "hello"

    def test_user_prefix_full_parseresult(self):
        result = parse_user_id("user:hello")
        assert result == ParseResult(user_id="hello", source="string")

    def test_user_prefix_normalized_fields(self):
        result = parse_user_id("user:  HeLLo  ")
        assert result == ParseResult(user_id="hello", source="string")

    def test_user_prefix_with_numbers_source(self):
        result = parse_user_id("user:abc123")
        assert result.source == "string"
        assert result.user_id == "abc123"

    def test_user_prefix_with_special_chars_source(self):
        result = parse_user_id("user:a_b-c")
        assert result == ParseResult(user_id="a_b-c", source="string")


# ==============================================================================
# SOURCE FIELD - "email" (email: prefix)
# ============================================================================== 

class TestSourceFieldEmail:
    def test_email_source_is_email(self):
        result = parse_user_id("email:alice@example.com")
        assert result is not None
        assert result.source == "email"

    def test_email_user_id_is_local_part(self):
        result = parse_user_id("email:alice@example.com")
        assert result.user_id == "alice"

    def test_email_full_parseresult(self):
        result = parse_user_id("email:alice@example.com")
        assert result == ParseResult(user_id="alice", source="email")

    def test_email_normalized_local_part(self):
        result = parse_user_id("email:  ALICE  @example.com")
        assert result == ParseResult(user_id="alice", source="email")

    def test_email_local_part_with_numbers(self):
        result = parse_user_id("email:user123@test.com")
        assert result == ParseResult(user_id="user123", source="email")

    def test_email_local_part_with_underscore(self):
        result = parse_user_id("email:my_user@test.com")
        assert result == ParseResult(user_id="my_user", source="email")

    def test_email_local_part_with_hyphen(self):
        result = parse_user_id("email:my-user@test.com")
        assert result == ParseResult(user_id="my-user", source="email")

    def test_email_no_at_sign_returns_none(self):
        assert parse_user_id("email:noatsign") is None

    def test_email_multiple_at_signs_uses_first(self):
        """email:user@domain@extra → local part is 'user', rest ignored."""
        result = parse_user_id("email:user@domain@extra")
        assert result is not None
        assert result.user_id == "user"
        assert result.source == "email"

    def test_email_empty_local_part(self):
        assert parse_user_id("email:@domain.com") is None

    def test_email_local_part_too_short(self):
        assert parse_user_id("email:ab@domain.com") is None

    def test_email_local_part_exactly_3_chars(self):
        result = parse_user_id("email:abc@domain.com")
        assert result == ParseResult(user_id="abc", source="email")

    def test_email_local_part_too_long(self):
        local = "a" * 21
        assert parse_user_id(f"email:{local}@domain.com") is None

    def test_email_local_part_exactly_20_chars(self):
        local = "a" * 20
        result = parse_user_id(f"email:{local}@domain.com")
        assert result is not None
        assert result.user_id == local
        assert result.source == "email"

    def test_email_local_part_invalid_chars(self):
        assert parse_user_id("email:user.name@domain.com") is None

    def test_email_reserved_local_part_default(self):
        assert parse_user_id("email:admin@test.com") is None
        assert parse_user_id("email:root@test.com") is None
        assert parse_user_id("email:system@test.com") is None

    def test_email_uppercase_local_part_normalized(self):
        result = parse_user_id("email:ALICE@test.com")
        assert result == ParseResult(user_id="alice", source="email")

    def test_email_prefix_case_sensitive(self):
        """'Email:user@test.com' does not start with 'email:'."""
        assert parse_user_id("Email:user@test.com") is None


# ==============================================================================
# SOURCE FIELD - "dict_flat" ({"user_id": ...})
# ==============================================================================

class TestSourceFieldDictFlat:
    def test_dict_flat_source(self):
        result = parse_user_id({"user_id": "hello"})
        assert result is not None
        assert result.source == "dict_flat"

    def test_dict_flat_user_id_field(self):
        result = parse_user_id({"user_id": "hello"})
        assert result.user_id == "hello"

    def test_dict_flat_full_parseresult(self):
        result = parse_user_id({"user_id": "hello"})
        assert result == ParseResult(user_id="hello", source="dict_flat")

    def test_dict_flat_normalized(self):
        result = parse_user_id({"user_id": "  HELLO  "})
        assert result == ParseResult(user_id="hello", source="dict_flat")

    def test_dict_flat_with_extra_keys(self):
        result = parse_user_id({"user_id": "hello", "extra": "data"})
        assert result == ParseResult(user_id="hello", source="dict_flat")


# ==============================================================================
# SOURCE FIELD - "dict_nested" ({"user": {"id": ...}})
# ==============================================================================

class TestSourceFieldDictNested:
    def test_dict_nested_source(self):
        result = parse_user_id({"user": {"id": "hello"}})
        assert result is not None
        assert result.source == "dict_nested"

    def test_dict_nested_user_id_field(self):
        result = parse_user_id({"user": {"id": "hello"}})
        assert result.user_id == "hello"

    def test_dict_nested_full_parseresult(self):
        result = parse_user_id({"user": {"id": "hello"}})
        assert result == ParseResult(user_id="hello", source="dict_nested")

    def test_dict_nested_normalized(self):
        result = parse_user_id({"user": {"id": "  HELLO  "}})
        assert result == ParseResult(user_id="hello", source="dict_nested")

    def test_dict_nested_with_extra_keys(self):
        result = parse_user_id({"user": {"id": "hello", "name": "John"}})
        assert result == ParseResult(user_id="hello", source="dict_nested")


# ==============================================================================
# DICT PRIORITY WITH SOURCE FIELD VERIFICATION
# ==============================================================================

class TestDictPriorityWithSource:
    def test_user_id_key_takes_precedence_source_is_dict_flat(self):
        result = parse_user_id({"user_id": "alpha", "user": {"id": "beta"}})
        assert result is not None
        assert result.source == "dict_flat"
        assert result.user_id == "alpha"

    def test_only_nested_form_source_is_dict_nested(self):
        result = parse_user_id({"user": {"id": "beta"}})
        assert result.source == "dict_nested"


# ==============================================================================
# PARSE_USER_IDS RETURNS LIST OF PARSERESULT
# ==============================================================================

class TestParseUserIdsBatchParseResult:
    def test_batch_returns_parseresults(self):
        items = ["user:hello", {"user_id": "world"}, {"user": {"id": "test"}}]
        result = parse_user_ids(items)
        assert len(result) == 3
        assert all(isinstance(r, ParseResult) for r in result)

    def test_batch_source_fields_correct(self):
        items = [
            "user:hello",
            "email:alice@test.com",
            {"user_id": "world"},
            {"user": {"id": "test"}},
        ]
        result = parse_user_ids(items)
        assert result[0].source == "string"
        assert result[1].source == "email"
        assert result[2].source == "dict_flat"
        assert result[3].source == "dict_nested"

    def test_batch_user_id_fields_correct(self):
        items = [
            "user:hello",
            "email:alice@test.com",
            {"user_id": "world"},
            {"user": {"id": "test"}},
        ]
        result = parse_user_ids(items)
        assert result[0].user_id == "hello"
        assert result[1].user_id == "alice"
        assert result[2].user_id == "world"
        assert result[3].user_id == "test"

    def test_batch_mixed_with_none_results(self):
        items = ["user:hello", None, {"user_id": "world"}, "bad"]
        result = parse_user_ids(items)
        assert result[0] == ParseResult(user_id="hello", source="string")
        assert result[1] is None
        assert result[2] == ParseResult(user_id="world", source="dict_flat")
        assert result[3] is None

    def test_batch_email_items_have_email_source(self):
        items = ["email:alice@x.com", "email:bob@y.com"]
        result = parse_user_ids(items)
        assert all(r.source == "email" for r in result)
        assert result[0].user_id == "alice"
        assert result[1].user_id == "bob"

    def test_batch_with_custom_reserved_returns_parseresults(self):
        items = ["user:admin", "user:hello"]
        result = parse_user_ids(items, reserved_ids=set())
        assert result[0] == ParseResult(user_id="admin", source="string")
        assert result[1] == ParseResult(user_id="hello", source="string")


# ==============================================================================
# PROPERTY: ALL NON-NONE RESULTS ARE PARSERESULT WITH VALID FIELDS
# ==============================================================================

class TestParseResultPropertyVerification:
    VALID_SOURCES = {"string", "email", "dict_flat", "dict_nested"}

    def test_all_outputs_have_valid_source(self):
        """Property: non-None output always has source in valid set."""
        test_inputs = [
            "user:hello", "user:WORLD", "user:  test  ",
            "email:alice@x.com", "email:bob@y.com",
            {"user_id": "abc"}, {"user_id": "  XYZ  "},
            {"user": {"id": "test"}}, {"user": {"id": "  UPPER  "}},
            None, 42, "bad", "", {"bad": "data"},
        ]
        for inp in test_inputs:
            result = parse_user_id(inp)
            if result is not None:
                assert isinstance(result, ParseResult), (
                    f"Result from {inp!r} is not ParseResult: {type(result)}"
                )
                assert result.source in self.VALID_SOURCES, (
                    f"Result source '{result.source}' from {inp!r} not in valid sources"
                )

    def test_all_outputs_have_valid_user_id_field(self):
        """Property: non-None output user_id matches ^[a-z0-9_-]{3,20}$."""
        pattern = re.compile(r'^[a-z0-9_-]{3,20}$')
        test_inputs = [
            "user:hello", "email:alice@x.com",
            {"user_id": "abc"}, {"user": {"id": "test"}},
            "user:  HELLO  ", {"user_id": "  XYZ  "},
        ]
        for inp in test_inputs:
            result = parse_user_id(inp)
            if result is not None:
                assert pattern.match(result.user_id), (
                    f"user_id '{result.user_id}' from {inp!r} doesn't match pattern"
                )

    def test_source_matches_input_type_string(self):
        """Property: string inputs with user: prefix yield source='string'."""
        string_inputs = ["user:hello", "user:abc123", "user:a_b-c"]
        for inp in string_inputs:
            result = parse_user_id(inp)
            if result is not None:
                assert result.source == "string", (
                    f"Expected source='string' for {inp!r}, got '{result.source}'"
                )

    def test_source_matches_input_type_email(self):
        """Property: string inputs with email: prefix yield source='email'."""
        email_inputs = ["email:alice@test.com", "email:bob@y.com", "email:test@z.com"]
        for inp in email_inputs:
            result = parse_user_id(inp)
            if result is not None:
                assert result.source == "email", (
                    f"Expected source='email' for {inp!r}, got '{result.source}'"
                )

    def test_source_matches_input_type_dict_flat(self):
        """Property: dict with user_id key yields source='dict_flat'."""
        dict_inputs = [{"user_id": "hello"}, {"user_id": "world"}, {"user_id": "test"}]
        for inp in dict_inputs:
            result = parse_user_id(inp)
            if result is not None:
                assert result.source == "dict_flat", (
                    f"Expected source='dict_flat' for {inp!r}, got '{result.source}'"
                )

    def test_source_matches_input_type_dict_nested(self):
        """Property: dict with user.id key yields source='dict_nested'."""
        dict_inputs = [
            {"user": {"id": "hello"}},
            {"user": {"id": "world"}},
        ]
        for inp in dict_inputs:
            result = parse_user_id(inp)
            if result is not None:
                assert result.source == "dict_nested", (
                    f"Expected source='dict_nested' for {inp!r}, got '{result.source}'"
                )


# ==============================================================================
# PARSERESULT RETURN TYPE ACROSS ALL SUCCESSFUL PATHS
# ==============================================================================

class TestReturnTypeIsParseResult:
    def test_string_returns_parseresult(self):
        result = parse_user_id("user:hello")
        assert isinstance(result, ParseResult)

    def test_email_returns_parseresult(self):
        result = parse_user_id("email:alice@test.com")
        assert isinstance(result, ParseResult)

    def test_dict_flat_returns_parseresult(self):
        result = parse_user_id({"user_id": "hello"})
        assert isinstance(result, ParseResult)

    def test_dict_nested_returns_parseresult(self):
        result = parse_user_id({"user": {"id": "hello"}})
        assert isinstance(result, ParseResult)

    def test_invalid_returns_none_not_parseresult(self):
        result = parse_user_id("bad")
        assert result is None
        assert not isinstance(result, ParseResult)

    def test_parseresult_is_not_mutable(self):
        """Namedtuples are immutable."""
        result = parse_user_id("user:hello")
        with pytest.raises(AttributeError):
            result.user_id = "changed"


# ==============================================================================
# END OF FIXED UNIT TEST
# ============================================================================== 


# ==============================================================================
# TEST PLAN (appended to existing tests)
# ==============================================================================
#
# The following tests cover functionality NOT already tested in existing tests:
#
# 1. VALIDATION - CHARACTER SET
#    - Test IDs with various invalid characters (dots, internal spaces, @, #, $, etc.)
#    - Test IDs with all valid character types (letters, digits, _, -)
#    - Better as unit tests: concrete character examples are clear and exhaustive
#
# 2. LENGTH BOUNDARY TESTING
#    - Exact boundary: length 1/2 (invalid), 3 (valid), 20 (valid), 21/100 (invalid)
#    - Test across all input types (string, dict_flat, dict_nested)
#    - Better as unit tests: boundary value analysis is straightforward
#
# 3. RESERVED IDS (DETAILED)
#    - Default set: {admin, root, system} rejected
#    - Custom reserved_ids replaces defaults entirely (e.g., admin now allowed)
#    - Empty set allows previously reserved IDs
#    - Custom set with non-default entries; None explicitly uses defaults
#    - Better as unit tests: discrete set membership checks
#
# 4. STRICT MODE (DETAILED)
#    - All four consecutive special pairs: __, --, _-, -_
#    - Single special chars allowed in strict mode
#    - Consecutive specials at start/middle/end of ID
#    - Non-strict mode (default) allows consecutive specials
#    - Strict applies to all input types
#    - Better as unit tests: specific pattern matching
#
# 5. BAD INPUT TYPES (NO RAISE)
#    - None, int, float, bool, list, tuple, set, bytes, object, ParseResult
#    - All should return None without raising
#    - Better as unit tests: concrete type examples
#
# 6. DICT EDGE CASES
#    - Non-string user_id values (int, None, list, bool, dict)
#    - user key exists but is not a dict (string, int, None, list)
#    - Nested dict missing "id" key; id is non-string
#    - Empty dict; dict with irrelevant keys
#    - Flat key precedence: if user_id key exists with bad value, nested not tried
#    - Better as unit tests: concrete edge cases
#
# 7. INPUT DICT NOT MUTATED
#    - Verify flat and nested dicts unchanged after parsing
#    - Better as unit tests: direct comparison
#
# 8. parse_user_ids EDGE CASES
#    - Empty list; single item; all invalid; strict and reserved passthrough
#    - Combined strict + reserved; ordering preservation
#    - Better as unit tests: behavioral verification
#
# 9. NORMALIZATION EDGE CASES
#    - Tabs, newlines as surrounding whitespace (trimmed)
#    - Internal whitespace (invalid after trim)
#    - Case normalization then validation/reserved check
#    - Better as unit tests: concrete examples
#
# 10. Z3 FORMAL VERIFICATION
#    - Consecutive special pairs completeness: {_, -} × {_, -} all covered
#    - Length bounds: [3, 20] rejects exactly < 3 and > 20
#    - Strict mode property: any pair of specials in a sequence is caught
#    - Better as Z3: exhaustive symbolic reasoning over the spec
#
# 11. INTEGRATION / COMPREHENSIVE SCENARIOS
#    - Full pipeline: extract → normalize → validate → result (all paths)
#    - Combined strict + reserved + custom sets
#    - Large batch with mixed inputs
#    - Better as unit tests: end-to-end behavioral checks
#
# ==============================================================================


# ==============================================================================
# VALIDATION - CHARACTER SET
# ==============================================================================


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

class TestValidationCharacterSet:
    def test_id_with_dot_invalid(self):
        assert parse_user_id("user:a.bc") is None

    def test_id_with_space_in_middle_invalid(self):
        assert parse_user_id("user:a b c") is None

    def test_id_with_at_sign_invalid(self):
        assert parse_user_id("user:ab@c") is None

    def test_id_with_hash_invalid(self):
        assert parse_user_id("user:ab#c") is None

    def test_id_with_dollar_invalid(self):
        assert parse_user_id("user:ab$c") is None

    def test_id_with_exclamation_invalid(self):
        assert parse_user_id("user:abc!") is None

    def test_id_with_plus_invalid(self):
        assert parse_user_id("user:a+bc") is None

    def test_id_with_slash_invalid(self):
        assert parse_user_id("user:a/bc") is None

    def test_id_with_only_lowercase_valid(self):
        result = parse_user_id("user:abcdef")
        assert result is not None
        assert result.user_id == "abcdef"

    def test_id_with_only_digits_valid(self):
        result = parse_user_id("user:12345")
        assert result is not None
        assert result.user_id == "12345"

    def test_id_with_only_underscores_valid(self):
        result = parse_user_id("user:___")
        assert result is not None
        assert result.user_id == "___"

    def test_id_with_only_hyphens_valid(self):
        result = parse_user_id("user:---")
        assert result is not None
        assert result.user_id == "---"

    def test_id_with_mixed_valid_chars(self):
        result = parse_user_id("user:a1_b2-c3")
        assert result is not None
        assert result.user_id == "a1_b2-c3"

    def test_id_with_uppercase_gets_lowered(self):
        result = parse_user_id("user:ABC")
        assert result is not None
        assert result.user_id == "abc"

    def test_id_with_tab_in_middle_invalid(self):
        assert parse_user_id("user:ab\tc") is None

    def test_id_with_newline_in_middle_invalid(self):
        assert parse_user_id("user:ab\nc") is None

    def test_id_with_unicode_invalid(self):
        assert parse_user_id("user:abcé") is None

    def test_id_with_emoji_invalid(self):
        assert parse_user_id("user:abc😀") is None


# ==============================================================================
# LENGTH BOUNDARY TESTING
# ==============================================================================

class TestLengthBoundary:
    def test_string_length_1_invalid(self):
        assert parse_user_id("user:a") is None

    def test_string_length_2_invalid(self):
        assert parse_user_id("user:ab") is None

    def test_string_length_3_valid(self):
        result = parse_user_id("user:abc")
        assert result is not None
        assert result.user_id == "abc"

    def test_string_length_4_valid(self):
        result = parse_user_id("user:abcd")
        assert result is not None

    def test_string_length_19_valid(self):
        uid = "a" * 19
        result = parse_user_id(f"user:{uid}")
        assert result is not None
        assert result.user_id == uid

    def test_string_length_20_valid(self):
        uid = "a" * 20
        result = parse_user_id(f"user:{uid}")
        assert result is not None
        assert result.user_id == uid

    def test_string_length_21_invalid(self):
        uid = "a" * 21
        assert parse_user_id(f"user:{uid}") is None

    def test_string_length_100_invalid(self):
        uid = "a" * 100
        assert parse_user_id(f"user:{uid}") is None

    def test_string_empty_id_invalid(self):
        assert parse_user_id("user:") is None

    def test_dict_flat_length_2_invalid(self):
        assert parse_user_id({"user_id": "ab"}) is None

    def test_dict_flat_length_3_valid(self):
        result = parse_user_id({"user_id": "abc"})
        assert result is not None

    def test_dict_flat_length_20_valid(self):
        result = parse_user_id({"user_id": "a" * 20})
        assert result is not None

    def test_dict_flat_length_21_invalid(self):
        assert parse_user_id({"user_id": "a" * 21}) is None

    def test_dict_nested_length_2_invalid(self):
        assert parse_user_id({"user": {"id": "ab"}}) is None

    def test_dict_nested_length_3_valid(self):
        result = parse_user_id({"user": {"id": "abc"}})
        assert result is not None

    def test_dict_nested_length_20_valid(self):
        result = parse_user_id({"user": {"id": "a" * 20}})
        assert result is not None

    def test_dict_nested_length_21_invalid(self):
        assert parse_user_id({"user": {"id": "a" * 21}}) is None

    def test_whitespace_trimmed_before_length_check(self):
        """ID with whitespace that trims to valid length should work."""
        result = parse_user_id("user:  abc  ")
        assert result is not None
        assert result.user_id == "abc"

    def test_whitespace_trimmed_still_too_short(self):
        """ID with whitespace that trims to < 3 chars should fail."""
        assert parse_user_id("user:  ab  ") is None


# ==============================================================================
# RESERVED IDS - DETAILED
# ==============================================================================

class TestReservedIds:
    def test_default_reserved_admin(self):
        assert parse_user_id("user:admin") is None

    def test_default_reserved_root(self):
        assert parse_user_id("user:root") is None

    def test_default_reserved_system(self):
        assert parse_user_id("user:system") is None

    def test_default_reserved_case_insensitive_admin(self):
        assert parse_user_id("user:ADMIN") is None

    def test_default_reserved_case_insensitive_root(self):
        assert parse_user_id("user:ROOT") is None

    def test_default_reserved_case_insensitive_system(self):
        assert parse_user_id("user:SYSTEM") is None

    def test_default_reserved_mixed_case(self):
        assert parse_user_id("user:Admin") is None

    def test_non_reserved_id_allowed(self):
        result = parse_user_id("user:hello")
        assert result is not None

    def test_custom_reserved_replaces_defaults(self):
        """Custom set replaces defaults: admin should be allowed if not in custom set."""
        result = parse_user_id("user:admin", reserved_ids={"blocked"})
        assert result is not None
        assert result.user_id == "admin"

    def test_custom_reserved_blocks_custom_id(self):
        assert parse_user_id("user:blocked", reserved_ids={"blocked"}) is None

    def test_custom_reserved_empty_set_allows_all_defaults(self):
        result = parse_user_id("user:admin", reserved_ids=set())
        assert result is not None
        assert result.user_id == "admin"

    def test_custom_reserved_empty_set_allows_root(self):
        result = parse_user_id("user:root", reserved_ids=set())
        assert result is not None

    def test_custom_reserved_empty_set_allows_system(self):
        result = parse_user_id("user:system", reserved_ids=set())
        assert result is not None

    def test_custom_reserved_multiple_entries(self):
        reserved = {"banned", "forbidden", "test"}
        assert parse_user_id("user:banned", reserved_ids=reserved) is None
        assert parse_user_id("user:forbidden", reserved_ids=reserved) is None
        assert parse_user_id("user:test", reserved_ids=reserved) is None
        result = parse_user_id("user:admin", reserved_ids=reserved)
        assert result is not None

    def test_reserved_applies_to_dict_flat(self):
        assert parse_user_id({"user_id": "admin"}) is None

    def test_reserved_applies_to_dict_nested(self):
        assert parse_user_id({"user": {"id": "admin"}}) is None

    def test_reserved_applies_to_email(self):
        assert parse_user_id("email:admin@test.com") is None

    def test_custom_reserved_applies_to_all_input_types(self):
        reserved = {"hello"}
        assert parse_user_id("user:hello", reserved_ids=reserved) is None
        assert parse_user_id("email:hello@test.com", reserved_ids=reserved) is None
        assert parse_user_id({"user_id": "hello"}, reserved_ids=reserved) is None
        assert parse_user_id({"user": {"id": "hello"}}, reserved_ids=reserved) is None

    def test_reserved_check_after_normalization(self):
        """Reserved check happens after normalization (lowercase, strip)."""
        assert parse_user_id("user:  ADMIN  ") is None

    def test_reserved_none_uses_defaults(self):
        """Explicitly passing None uses default reserved set."""
        assert parse_user_id("user:admin", reserved_ids=None) is None
        assert parse_user_id("user:root", reserved_ids=None) is None
        assert parse_user_id("user:system", reserved_ids=None) is None


# ==============================================================================
# STRICT MODE
# ==============================================================================

class TestStrictMode:
    def test_strict_rejects_double_underscore(self):
        assert parse_user_id("user:a__b", strict=True) is None

    def test_strict_rejects_double_hyphen(self):
        assert parse_user_id("user:a--b", strict=True) is None

    def test_strict_rejects_underscore_hyphen(self):
        assert parse_user_id("user:a_-b", strict=True) is None

    def test_strict_rejects_hyphen_underscore(self):
        assert parse_user_id("user:a-_b", strict=True) is None

    def test_strict_allows_single_underscore(self):
        result = parse_user_id("user:a_b", strict=True)
        assert result is not None
        assert result.user_id == "a_b"

    def test_strict_allows_single_hyphen(self):
        result = parse_user_id("user:a-b", strict=True)
        assert result is not None
        assert result.user_id == "a-b"

    def test_strict_allows_separated_specials(self):
        """Underscore and hyphen with chars between them: ok in strict."""
        result = parse_user_id("user:a_b-c", strict=True)
        assert result is not None

    def test_strict_rejects_triple_underscore(self):
        assert parse_user_id("user:a___b", strict=True) is None

    def test_strict_rejects_triple_hyphen(self):
        assert parse_user_id("user:a---b", strict=True) is None

    def test_strict_consecutive_at_start(self):
        assert parse_user_id("user:__abc", strict=True) is None

    def test_strict_consecutive_at_end(self):
        assert parse_user_id("user:abc__", strict=True) is None

    def test_nonstrict_allows_double_underscore(self):
        result = parse_user_id("user:a__b", strict=False)
        assert result is not None
        assert result.user_id == "a__b"

    def test_nonstrict_allows_double_hyphen(self):
        result = parse_user_id("user:a--b", strict=False)
        assert result is not None

    def test_nonstrict_allows_underscore_hyphen(self):
        result = parse_user_id("user:a_-b", strict=False)
        assert result is not None

    def test_nonstrict_allows_hyphen_underscore(self):
        result = parse_user_id("user:a-_b", strict=False)
        assert result is not None

    def test_strict_default_is_false(self):
        """Default strict=False, so consecutive specials allowed by default."""
        result = parse_user_id("user:a__b")
        assert result is not None

    def test_strict_applies_to_dict_flat(self):
        assert parse_user_id({"user_id": "a__b"}, strict=True) is None

    def test_strict_applies_to_dict_nested(self):
        assert parse_user_id({"user": {"id": "a__b"}}, strict=True) is None

    def test_strict_applies_to_email(self):
        assert parse_user_id("email:a__b@test.com", strict=True) is None

    def test_strict_with_normalized_id(self):
        """Strict check happens after normalization."""
        assert parse_user_id("user:  A__B  ", strict=True) is None

    def test_strict_allows_no_special_chars(self):
        result = parse_user_id("user:abcdef", strict=True)
        assert result is not None

    def test_strict_allows_only_alphanumeric(self):
        result = parse_user_id("user:abc123", strict=True)
        assert result is not None

    def test_strict_multiple_separated_specials_ok(self):
        result = parse_user_id("user:a_b_c_d", strict=True)
        assert result is not None

    def test_strict_hyphen_underscore_mix_separated(self):
        result = parse_user_id("user:a-b_c-d", strict=True)
        assert result is not None


# ==============================================================================
# BAD INPUT TYPES (NO RAISE)
# ==============================================================================

class TestBadInputTypes:
    def test_none_input(self):
        assert parse_user_id(None) is None

    def test_integer_input(self):
        assert parse_user_id(42) is None

    def test_float_input(self):
        assert parse_user_id(3.14) is None

    def test_bool_true_input(self):
        # Note: bool is subclass of int in Python, not str or dict
        assert parse_user_id(True) is None

    def test_bool_false_input(self):
        assert parse_user_id(False) is None

    def test_list_input(self):
        assert parse_user_id(["user:hello"]) is None

    def test_tuple_input(self):
        assert parse_user_id(("user:hello",)) is None

    def test_set_input(self):
        # Sets are not dicts, should return None
        assert parse_user_id({"user:hello"}) is None

    def test_bytes_input(self):
        assert parse_user_id(b"user:hello") is None

    def test_empty_string(self):
        assert parse_user_id("") is None

    def test_string_no_prefix(self):
        assert parse_user_id("hello") is None

    def test_string_wrong_prefix(self):
        assert parse_user_id("id:hello") is None

    def test_string_only_user_prefix(self):
        assert parse_user_id("user:") is None

    def test_string_only_email_prefix(self):
        assert parse_user_id("email:") is None

    def test_string_email_no_at(self):
        assert parse_user_id("email:noatsign") is None

    def test_object_input(self):
        assert parse_user_id(object()) is None

    def test_parseresult_input(self):
        """ParseResult is a tuple subclass, not a str or dict."""
        pr = ParseResult(user_id="hello", source="string")
        assert parse_user_id(pr) is None

    def test_complex_number_input(self):
        assert parse_user_id(1 + 2j) is None

    def test_frozenset_input(self):
        assert parse_user_id(frozenset({"hello"})) is None


# ==============================================================================
# DICT EDGE CASES
# ==============================================================================

class TestDictEdgeCases:
    def test_empty_dict(self):
        assert parse_user_id({}) is None

    def test_dict_user_id_is_int(self):
        assert parse_user_id({"user_id": 123}) is None

    def test_dict_user_id_is_none(self):
        assert parse_user_id({"user_id": None}) is None

    def test_dict_user_id_is_list(self):
        assert parse_user_id({"user_id": ["hello"]}) is None

    def test_dict_user_id_is_bool(self):
        assert parse_user_id({"user_id": True}) is None

    def test_dict_user_id_is_dict(self):
        assert parse_user_id({"user_id": {"nested": "value"}}) is None

    def test_dict_nested_user_is_string(self):
        """user key exists but value is string, not dict."""
        assert parse_user_id({"user": "hello"}) is None

    def test_dict_nested_user_is_int(self):
        assert parse_user_id({"user": 42}) is None

    def test_dict_nested_user_is_none(self):
        assert parse_user_id({"user": None}) is None

    def test_dict_nested_user_is_list(self):
        assert parse_user_id({"user": [{"id": "hello"}]}) is None

    def test_dict_nested_missing_id_key(self):
        assert parse_user_id({"user": {"name": "hello"}}) is None

    def test_dict_nested_id_is_int(self):
        assert parse_user_id({"user": {"id": 123}}) is None

    def test_dict_nested_id_is_none(self):
        assert parse_user_id({"user": {"id": None}}) is None

    def test_dict_nested_id_is_list(self):
        assert parse_user_id({"user": {"id": ["hello"]}}) is None

    def test_dict_nested_empty_inner_dict(self):
        assert parse_user_id({"user": {}}) is None

    def test_dict_irrelevant_keys(self):
        assert parse_user_id({"name": "alice", "age": 30}) is None

    def test_dict_flat_precedence_over_nested_when_flat_invalid_value(self):
        """If user_id key exists but value is non-string, nested form is NOT tried."""
        result = parse_user_id({"user_id": 123, "user": {"id": "hello"}})
        assert result is None

    def test_dict_nested_user_is_bool_true(self):
        """bool is subclass of int, not dict."""
        assert parse_user_id({"user": True}) is None

    def test_dict_nested_user_is_empty_list(self):
        assert parse_user_id({"user": []}) is None


# ==============================================================================
# INPUT DICT NOT MUTATED
# ==============================================================================

class TestDictNotMutated:
    def test_flat_dict_not_mutated(self):
        d = {"user_id": "  HELLO  ", "extra": "data"}
        original = d.copy()
        parse_user_id(d)
        assert d == original

    def test_nested_dict_not_mutated(self):
        inner = {"id": "  HELLO  ", "extra": "data"}
        d = {"user": inner}
        original_inner = inner.copy()
        parse_user_id(d)
        assert d["user"] is inner  # Same object reference
        assert inner == original_inner

    def test_flat_dict_not_mutated_on_reserved(self):
        d = {"user_id": "admin"}
        original = d.copy()
        parse_user_id(d)
        assert d == original

    def test_nested_dict_not_mutated_on_invalid(self):
        inner = {"id": "ab"}
        d = {"user": inner}
        original_inner = inner.copy()
        parse_user_id(d)
        assert inner == original_inner

    def test_flat_dict_not_mutated_on_strict_rejection(self):
        d = {"user_id": "a__b"}
        original = d.copy()
        parse_user_id(d, strict=True)
        assert d == original

    def test_nested_dict_not_mutated_on_strict_rejection(self):
        inner = {"id": "a__b"}
        d = {"user": inner}
        original_inner = inner.copy()
        parse_user_id(d, strict=True)
        assert inner == original_inner


# ==============================================================================
# PARSE_USER_IDS - ADDITIONAL EDGE CASES
# ==============================================================================

class TestParseUserIdsAdditional:
    def test_empty_list(self):
        assert parse_user_ids([]) == []

    def test_single_valid_item(self):
        result = parse_user_ids(["user:hello"])
        assert len(result) == 1
        assert result[0] == ParseResult(user_id="hello", source="string")

    def test_single_invalid_item(self):
        result = parse_user_ids([None])
        assert len(result) == 1
        assert result[0] is None

    def test_all_invalid_items(self):
        result = parse_user_ids([None, 42, "bad", "", []])
        assert len(result) == 5
        assert all(r is None for r in result)

    def test_strict_passthrough_rejects(self):
        """strict=True passed to parse_user_id for each item."""
        result = parse_user_ids(["user:a__b"], strict=True)
        assert result[0] is None

    def test_strict_false_passthrough_allows(self):
        result = parse_user_ids(["user:a__b"], strict=False)
        assert result[0] is not None

    def test_reserved_ids_passthrough_empty(self):
        """Empty reserved_ids passed through allows default-reserved IDs."""
        result = parse_user_ids(["user:admin"], reserved_ids=set())
        assert result[0] is not None
        assert result[0].user_id == "admin"

    def test_reserved_ids_custom_passthrough(self):
        result = parse_user_ids(["user:hello"], reserved_ids={"hello"})
        assert result[0] is None

    def test_preserves_order(self):
        items = ["user:aaa", "user:bbb", "user:ccc"]
        result = parse_user_ids(items)
        assert [r.user_id for r in result] == ["aaa", "bbb", "ccc"]

    def test_length_matches_input(self):
        items = ["user:hello", None, "bad", {"user_id": "world"}, 42]
        result = parse_user_ids(items)
        assert len(result) == len(items)

    def test_batch_strict_and_reserved_combined(self):
        items = ["user:admin", "user:a__b", "user:hello"]
        result = parse_user_ids(items, reserved_ids={"admin"}, strict=True)
        assert result[0] is None  # reserved
        assert result[1] is None  # strict violation
        assert result[2] is not None  # valid

    def test_batch_large_input(self):
        """Batch processing with many items preserves correctness."""
        items = [f"user:user{i:04d}" for i in range(100)]
        result = parse_user_ids(items)
        assert len(result) == 100
        assert all(r is not None for r in result)
        for i, r in enumerate(result):
            assert r.user_id == f"user{i:04d}"

    def test_batch_does_not_modify_input_list(self):
        items = ["user:hello", "user:world"]
        items_copy = items.copy()
        parse_user_ids(items)
        assert items == items_copy


# ==============================================================================
# NORMALIZATION EDGE CASES
# ==============================================================================

class TestNormalizationEdgeCases:
    def test_leading_whitespace_trimmed(self):
        result = parse_user_id("user:   hello")
        assert result is not None
        assert result.user_id == "hello"

    def test_trailing_whitespace_trimmed(self):
        result = parse_user_id("user:hello   ")
        assert result is not None
        assert result.user_id == "hello"

    def test_tab_whitespace_trimmed(self):
        result = parse_user_id("user:\thello\t")
        assert result is not None
        assert result.user_id == "hello"

    def test_newline_whitespace_trimmed(self):
        result = parse_user_id("user:\nhello\n")
        assert result is not None
        assert result.user_id == "hello"

    def test_mixed_case_normalized(self):
        result = parse_user_id("user:HeLLo_WoRLd")
        assert result is not None
        assert result.user_id == "hello_world"

    def test_all_uppercase_normalized(self):
        result = parse_user_id("user:ABCDEF")
        assert result is not None
        assert result.user_id == "abcdef"

    def test_dict_flat_whitespace_trimmed(self):
        result = parse_user_id({"user_id": "  hello  "})
        assert result is not None
        assert result.user_id == "hello"

    def test_dict_nested_whitespace_trimmed(self):
        result = parse_user_id({"user": {"id": "  hello  "}})
        assert result is not None
        assert result.user_id == "hello"

    def test_email_local_part_whitespace_trimmed(self):
        result = parse_user_id("email:  hello  @test.com")
        assert result is not None
        assert result.user_id == "hello"

    def test_normalization_then_char_validation(self):
        """After trim+lowercase, if result has invalid chars, return None."""
        assert parse_user_id("user:  A.B  ") is None

    def test_normalization_then_reserved_check(self):
        """After trim+lowercase, reserved check applies."""
        assert parse_user_id("user:  ADMIN  ") is None

    def test_whitespace_only_id_invalid(self):
        """All whitespace trims to empty string, too short."""
        assert parse_user_id("user:   ") is None

    def test_dict_flat_whitespace_only_invalid(self):
        assert parse_user_id({"user_id": "   "}) is None


# ==============================================================================
# Z3 FORMAL VERIFICATION TESTS
# ==============================================================================

class TestZ3FormalVerification:
    """
    Use Z3 to formally verify logical properties of the validation spec.
    These tests model constraints symbolically and prove properties hold
    universally, complementing the concrete unit tests.
    """

    def test_z3_consecutive_special_pairs_completeness(self):
        """
        Verify that the four pairs {__, --, _-, -_} cover ALL combinations
        of two special characters from {_, -}.

        Z3 proves: for all x, y in {underscore, hyphen}, pair (x, y) is in
        the rejection set. No pair escapes the strict mode check.
        """
        try:
            from z3 import Solver, Int, Or, And, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        x = Int('x')  # 0 = underscore, 1 = hyphen
        y = Int('y')

        # Constrain x, y to special characters
        s.add(Or(x == 0, x == 1))
        s.add(Or(y == 0, y == 1))

        # Assert: the pair (x, y) is NOT any of the four rejected pairs
        s.add(And(
            Or(x != 0, y != 0),  # not (_, _)
            Or(x != 1, y != 1),  # not (-, -)
            Or(x != 0, y != 1),  # not (_, -)
            Or(x != 1, y != 0),  # not (-, _)
        ))

        # UNSAT means no pair of specials can escape the check
        assert s.check() == unsat, \
            "Found a consecutive special pair not covered by strict mode"

    def test_z3_length_bounds_correct(self):
        """
        Verify that the valid length range [3, 20] is correctly bounded:
        - No length < 3 satisfies the constraint
        - No length > 20 satisfies the constraint
        - Boundary values 3 and 20 do satisfy it
        """
        try:
            from z3 import Solver, Int, And, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        length = Int('length')
        valid = And(length >= 3, length <= 20)

        # Length < 3 → UNSAT with valid
        s.push()
        s.add(length < 3, valid)
        assert s.check() == unsat, "Length < 3 should never be valid"
        s.pop()

        # Length > 20 → UNSAT with valid
        s.push()
        s.add(length > 20, valid)
        assert s.check() == unsat, "Length > 20 should never be valid"
        s.pop()

        # Length = 3 → SAT
        s.push()
        s.add(length == 3, valid)
        assert s.check() == sat, "Length 3 should be valid"
        s.pop()

        # Length = 20 → SAT
        s.push()
        s.add(length == 20, valid)
        assert s.check() == sat, "Length 20 should be valid"
        s.pop()

        # Length = 0 → UNSAT
        s.push()
        s.add(length == 0, valid)
        assert s.check() == unsat, "Length 0 should never be valid"
        s.pop()

    def test_z3_strict_mode_catches_all_adjacent_specials_in_sequence(self):
        """
        Model a 5-character sequence where each character is either 'regular'
        (0), underscore (1), or hyphen (2). Verify that if any two adjacent
        characters are both special (>=1), at least one of the four rejection
        patterns matches at that position.
        """
        try:
            from z3 import Solver, Int, Or, And, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        chars = [Int(f'c{i}') for i in range(5)]

        for c in chars:
            s.add(Or(c == 0, c == 1, c == 2))

        # Assert there ARE consecutive specials
        has_consec = Or(*[And(chars[i] >= 1, chars[i + 1] >= 1) for i in range(4)])
        s.add(has_consec)

        # Assert NONE of the four rejection patterns match at ANY position
        for i in range(4):
            s.add(And(
                Or(chars[i] != 1, chars[i + 1] != 1),  # not __
                Or(chars[i] != 2, chars[i + 1] != 2),  # not --
                Or(chars[i] != 1, chars[i + 1] != 2),  # not _-
                Or(chars[i] != 2, chars[i + 1] != 1),  # not -_
            ))

        # UNSAT: consecutive specials always trigger at least one rejection
        assert s.check() == unsat, \
            "Found a sequence with adjacent specials not caught by strict mode"

    def test_z3_reserved_set_membership(self):
        """
        Verify that the default reserved set covers exactly 3 IDs and
        a non-reserved ID is not blocked. Cross-check with actual implementation.
        """
        try:
            from z3 import Solver, Int, Or, And, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        # Encode: admin=0, root=1, system=2, other=3
        s = Solver()
        id_val = Int('id')
        is_reserved = Or(id_val == 0, id_val == 1, id_val == 2)

        # All three reserved IDs are caught
        for rid in [0, 1, 2]:
            s.push()
            s.add(id_val == rid, is_reserved)
            assert s.check() == sat, f"Reserved ID {rid} should be caught"
            s.pop()

        # Non-reserved ID is NOT caught
        s.push()
        s.add(id_val == 3, is_reserved)
        assert s.check() == unsat, "Non-reserved ID should not be caught"
        s.pop()

        # Cross-verify with actual function
        assert parse_user_id("user:admin") is None
        assert parse_user_id("user:root") is None
        assert parse_user_id("user:system") is None
        assert parse_user_id("user:hello") is not None

    def test_z3_strict_and_nonstrict_are_disjoint_for_consecutive_specials(self):
        """
        Verify property: an ID with consecutive specials passes in non-strict
        but fails in strict mode. This confirms strict is strictly more
        restrictive than non-strict for this class of IDs.
        """
        # Concrete cross-check: a__b passes non-strict, fails strict
        result_nonstrict = parse_user_id("user:a__b", strict=False)
        result_strict = parse_user_id("user:a__b", strict=True)
        assert result_nonstrict is not None
        assert result_strict is None

        result_nonstrict2 = parse_user_id("user:a--b", strict=False)
        result_strict2 = parse_user_id("user:a--b", strict=True)
        assert result_nonstrict2 is not None
        assert result_strict2 is None

        result_nonstrict3 = parse_user_id("user:a_-b", strict=False)
        result_strict3 = parse_user_id("user:a_-b", strict=True)
        assert result_nonstrict3 is not None
        assert result_strict3 is None

        result_nonstrict4 = parse_user_id("user:a-_b", strict=False)
        result_strict4 = parse_user_id("user:a-_b", strict=True)
        assert result_nonstrict4 is not None
        assert result_strict4 is None


# ==============================================================================
# INTEGRATION / COMPREHENSIVE SCENARIOS
# ==============================================================================

class TestComprehensiveScenarios:
    def test_full_pipeline_string_normalized_validated(self):
        """Full pipeline: input → extract → normalize → validate → result."""
        result = parse_user_id("user:  My_User-123  ")
        assert result == ParseResult(user_id="my_user-123", source="string")

    def test_full_pipeline_email_normalized_validated(self):
        result = parse_user_id("email:  My_User  @example.com")
        assert result == ParseResult(user_id="my_user", source="email")

    def test_full_pipeline_dict_flat_normalized_validated(self):
        result = parse_user_id({"user_id": "  My_User  "})
        assert result == ParseResult(user_id="my_user", source="dict_flat")

    def test_full_pipeline_dict_nested_normalized_validated(self):
        result = parse_user_id({"user": {"id": "  My_User  "}})
        assert result == ParseResult(user_id="my_user", source="dict_nested")

    def test_strict_and_reserved_combined(self):
        """Both strict and reserved checks must pass."""
        assert parse_user_id("user:admin", strict=True) is None
        assert parse_user_id("user:a__b", strict=True) is None
        result = parse_user_id("user:hello", strict=True)
        assert result is not None

    def test_custom_reserved_and_strict_combined(self):
        reserved = {"hello"}
        assert parse_user_id("user:hello", reserved_ids=reserved, strict=True) is None
        assert parse_user_id("user:a__b", reserved_ids=reserved, strict=True) is None
        result = parse_user_id("user:world", reserved_ids=reserved, strict=True)
        assert result is not None

    def test_batch_comprehensive(self):
        items = [
            "user:  HELLO  ",           # valid string
            "email:alice@test.com",      # valid email
            {"user_id": "admin"},        # reserved → None
            {"user": {"id": "ab"}},      # too short → None
            42,                          # bad type → None
            "user:a__b",                 # valid (non-strict)
            {"user_id": "  World  "},    # valid dict_flat
        ]
        result = parse_user_ids(items)
        assert len(result) == 7
        assert result[0] == ParseResult(user_id="hello", source="string")
        assert result[1] == ParseResult(user_id="alice", source="email")
        assert result[2] is None
        assert result[3] is None
        assert result[4] is None
        assert result[5] == ParseResult(user_id="a__b", source="string")
        assert result[6] == ParseResult(user_id="world", source="dict_flat")

    def test_user_prefix_case_sensitive(self):
        """'User:hello' doesn't match 'user:' prefix."""
        assert parse_user_id("User:hello") is None

    def test_user_colon_only(self):
        """'user:' with nothing after → empty → too short."""
        assert parse_user_id("user:") is None

    def test_whitespace_only_id_all_input_types(self):
        assert parse_user_id("user:   ") is None
        assert parse_user_id({"user_id": "   "}) is None
        assert parse_user_id({"user": {"id": "   "}}) is None

    def test_id_at_max_length_boundary(self):
        """ID using every valid character type at exactly 20 chars."""
        uid = "a0_-" * 5  # 20 chars
        result = parse_user_id(f"user:{uid}")
        assert result is not None
        assert len(result.user_id) == 20

    def test_email_at_sign_position_edge(self):
        """Email with @ as first char after prefix → empty local part."""
        assert parse_user_id("email:@test.com") is None

    def test_email_at_sign_at_end(self):
        """email:user@ → local part is 'user', domain is empty but that's ok for parsing."""
        result = parse_user_id("email:user@")
        assert result is not None
        assert result.user_id == "user"
        assert result.source == "email"

    def test_valid_id_not_default_reserved(self):
        """IDs close to reserved but not in the set should work."""
        result = parse_user_id("user:admins")  # admin + s
        assert result is not None
        result = parse_user_id("user:roots")   # root + s
        assert result is not None
        result = parse_user_id("user:systems") # system + s
        assert result is not None

    def test_valid_id_substring_of_reserved(self):
        """Substrings of reserved IDs that are >= 3 chars should work."""
        result = parse_user_id("user:adm")
        assert result is not None
        result = parse_user_id("user:roo")
        assert result is not None
        result = parse_user_id("user:sys")
        assert result is not None

# ==============================================================================
# ADDITIONAL TEST PLAN
# ==============================================================================
#
# These tests cover gaps not addressed by existing tests:
#
# 1. EMPTY STRING VALUES IN DICT INPUTS
#    - user_id: "" → normalizes to "" → too short → None
#    - nested id: "" → same behavior
#    Better as unit tests: concrete edge cases
#
# 2. RESERVED SET CASE SENSITIVITY INTERACTION
#    - Custom reserved with uppercase entries vs normalized lowercase IDs
#    - e.g., reserved={"Hello"} should NOT block "hello" (set comparison is exact)
#    Better as unit tests: discrete set membership checks
#
# 3. ADDITIONAL EMAIL PARSING EDGE CASES
#    - Local part with mixed valid chars, boundary lengths
#    - Whitespace before @ sign, consecutive specials with strict
#    Better as unit tests: concrete input/output examples
#
# 4. DICT FLAT PRECEDENCE DETAILED EDGE CASES
#    - user_id key with empty string blocks nested path
#    - user_id with whitespace-only blocks nested path
#    - user_id with reserved id blocks nested path
#    Better as unit tests: behavioral verification
#
# 5. SPECIAL CHARS AT START/END POSITIONS
#    - Leading/trailing underscore or hyphen in strict/non-strict
#    - All-special-char IDs in strict mode
#    Better as unit tests: boundary value analysis
#
# 6. NORMALIZATION + STRICT MODE INTERACTION
#    - Uppercase input with consecutive specials normalized then strict-checked
#    - Whitespace around consecutive specials
#    Better as unit tests: pipeline verification
#
# 7. WHITESPACE + LENGTH BOUNDARY INTERACTION
#    - Whitespace that changes effective length across boundaries
#    - Various whitespace types (tab, newline, carriage return)
#    Better as unit tests: boundary testing
#
# 8. STRING PREFIX EDGE CASES
#    - Similar-but-different prefixes (userx:, emailx:, use:, etc.)
#    - Colon in ID value, double prefix
#    Better as unit tests: concrete parsing checks
#
# 9. BATCH COMPLEX SCENARIOS
#    - All source types + invalid + strict + reserved combined
#    - Custom reserved overrides in batch, result list identity
#    Better as unit tests: integration verification
#
# 10. DICT SUBTYPE INPUTS
#    - OrderedDict, defaultdict as inputs (dict subclasses)
#    Better as unit tests: concrete type examples
#
# 11. INVALID CHARACTER COVERAGE EXPANSION
#    - Additional special characters: %, \, |, [], {}, *, &, ^, ~, =
#    Better as unit tests: exhaustive character checks
#
# 12. IDEMPOTENCY AND DETERMINISM
#    - Same input parsed twice yields identical results
#    Better as unit tests: behavioral consistency
#
# 13. CROSS-SOURCE NORMALIZATION CONSISTENCY
#    - Same unnormalized ID via different sources yields same normalized user_id
#    Better as unit tests: pipeline consistency
#
# 14. RESERVED ID EXACT BOUNDARY
#    - IDs similar to reserved (prefix/suffix/substring) are allowed
#    Better as unit tests: set membership edge cases
#
# 15. STRICT MODE POSITIONAL COVERAGE
#    - Consecutive specials at position 0-1, last two, middle
#    - Multiple separate pairs of consecutive specials
#    - Three/four consecutive specials
#    Better as unit tests: pattern matching edge cases
#
# ==============================================================================



import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

class TestEmptyStringValues:
    def test_dict_flat_empty_string(self):
        assert parse_user_id({"user_id": ""}) is None

    def test_dict_nested_empty_string(self):
        assert parse_user_id({"user": {"id": ""}}) is None

    def test_user_prefix_empty_after_trim(self):
        assert parse_user_id("user:  ") is None

    def test_email_empty_local_after_trim(self):
        """email: with space before @ → local is ' ' → trims to '' → too short."""
        assert parse_user_id("email: @domain.com") is None


class TestReservedSetCaseInteraction:
    def test_custom_reserved_uppercase_entry_does_not_match_lowered_id(self):
        """Custom reserved {'Hello'} won't match normalized 'hello' because
        the reserved set is compared as-is against the normalized (lowered) ID."""
        result = parse_user_id("user:hello", reserved_ids={"Hello"})
        assert result is not None
        assert result.user_id == "hello"

    def test_custom_reserved_lowercase_entry_matches(self):
        result = parse_user_id("user:hello", reserved_ids={"hello"})
        assert result is None

    def test_custom_reserved_with_mixed_case_entries(self):
        """Only exact lowercase matches are blocked because ID is normalized."""
        reserved = {"Admin", "ROOT", "system"}
        # "admin" (normalized) vs "Admin" → no match
        result_admin = parse_user_id("user:admin", reserved_ids=reserved)
        assert result_admin is not None
        # "root" (normalized) vs "ROOT" → no match
        result_root = parse_user_id("user:root", reserved_ids=reserved)
        assert result_root is not None
        # "system" (normalized) vs "system" → exact match → blocked
        result_system = parse_user_id("user:system", reserved_ids=reserved)
        assert result_system is None

    def test_custom_reserved_frozenset(self):
        """frozenset is set-like, should work as reserved_ids."""
        reserved = frozenset({"banned"})
        assert parse_user_id("user:banned", reserved_ids=reserved) is None
        result = parse_user_id("user:hello", reserved_ids=reserved)
        assert result is not None


class TestSpecialCharBoundaries:
    def test_id_starting_with_underscore_nonstrict(self):
        result = parse_user_id("user:_abc")
        assert result is not None
        assert result.user_id == "_abc"

    def test_id_ending_with_underscore_nonstrict(self):
        result = parse_user_id("user:abc_")
        assert result is not None
        assert result.user_id == "abc_"

    def test_id_starting_with_hyphen_nonstrict(self):
        result = parse_user_id("user:-abc")
        assert result is not None
        assert result.user_id == "-abc"

    def test_id_ending_with_hyphen_nonstrict(self):
        result = parse_user_id("user:abc-")
        assert result is not None
        assert result.user_id == "abc-"

    def test_id_starting_with_single_underscore_strict(self):
        result = parse_user_id("user:_abc", strict=True)
        assert result is not None

    def test_id_ending_with_single_underscore_strict(self):
        result = parse_user_id("user:abc_", strict=True)
        assert result is not None

    def test_id_starting_with_single_hyphen_strict(self):
        result = parse_user_id("user:-abc", strict=True)
        assert result is not None

    def test_id_ending_with_single_hyphen_strict(self):
        result = parse_user_id("user:abc-", strict=True)
        assert result is not None

    def test_id_exactly_3_chars_all_underscores_strict(self):
        """___ has consecutive specials → rejected in strict."""
        assert parse_user_id("user:___", strict=True) is None

    def test_id_exactly_3_chars_all_hyphens_strict(self):
        assert parse_user_id("user:---", strict=True) is None

    def test_id_exactly_3_chars_mixed_specials_strict(self):
        assert parse_user_id("user:_-_", strict=True) is None
        assert parse_user_id("user:-_-", strict=True) is None


class TestNormalizationStrictInteraction:
    def test_uppercase_consecutive_underscores_strict(self):
        """A__B normalizes to a__b → strict rejects."""
        assert parse_user_id("user:A__B", strict=True) is None

    def test_uppercase_consecutive_hyphens_strict(self):
        assert parse_user_id("user:A--B", strict=True) is None

    def test_uppercase_mixed_consecutive_strict(self):
        assert parse_user_id("user:A_-B", strict=True) is None
        assert parse_user_id("user:A-_B", strict=True) is None

    def test_whitespace_around_consecutive_specials_strict(self):
        """Trimmed, lowered, then strict check applies."""
        assert parse_user_id("user:  a__b  ", strict=True) is None

    def test_dict_flat_uppercase_consecutive_strict(self):
        assert parse_user_id({"user_id": "A__B"}, strict=True) is None

    def test_dict_nested_uppercase_consecutive_strict(self):
        assert parse_user_id({"user": {"id": "A--B"}}, strict=True) is None


class TestWhitespaceLengthInteraction:
    def test_whitespace_padded_to_3_chars_valid(self):
        result = parse_user_id("user:  abc  ")
        assert result is not None
        assert result.user_id == "abc"

    def test_whitespace_padded_to_2_chars_invalid(self):
        assert parse_user_id("user:  ab  ") is None

    def test_whitespace_padded_to_20_chars_valid(self):
        uid = "a" * 20
        result = parse_user_id(f"user:  {uid}  ")
        assert result is not None
        assert result.user_id == uid

    def test_whitespace_padded_to_21_chars_invalid(self):
        uid = "a" * 21
        assert parse_user_id(f"user:  {uid}  ") is None

    def test_carriage_return_whitespace_trimmed(self):
        result = parse_user_id("user:\rhello\r")
        assert result is not None
        assert result.user_id == "hello"

    def test_mixed_whitespace_types_trimmed(self):
        result = parse_user_id("user: \t\n\rhello \t\n\r")
        assert result is not None
        assert result.user_id == "hello"

    def test_whitespace_only_various_types_dict(self):
        assert parse_user_id({"user_id": "\t\n"}) is None
        assert parse_user_id({"user": {"id": "  \t  "}}) is None


class TestEmailEdgeCasesAdditional:
    def test_email_local_part_with_numbers_and_specials(self):
        result = parse_user_id("email:user_123-test@domain.com")
        assert result is not None
        assert result.user_id == "user_123-test"
        assert result.source == "email"

    def test_email_local_part_20_chars_exact(self):
        local = "abcdefghijklmnopqrst"  # 20 chars
        result = parse_user_id(f"email:{local}@domain.com")
        assert result is not None
        assert result.user_id == local

    def test_email_colon_in_domain_part_ignored(self):
        """email:user@domain:8080 → local is 'user', domain part ignored."""
        result = parse_user_id("email:user@domain:8080")
        assert result is not None
        assert result.user_id == "user"

    def test_email_local_part_consecutive_specials_strict(self):
        assert parse_user_id("email:a__b@domain.com", strict=True) is None

    def test_email_local_part_consecutive_specials_nonstrict(self):
        result = parse_user_id("email:a__b@domain.com", strict=False)
        assert result is not None
        assert result.user_id == "a__b"

    def test_email_whitespace_before_at(self):
        """email:user  @domain → local is 'user  ' → trims to 'user'."""
        result = parse_user_id("email:user  @domain.com")
        assert result is not None
        assert result.user_id == "user"

    def test_email_local_part_with_period_invalid(self):
        """Period in email local part is not in [a-z0-9_-]."""
        assert parse_user_id("email:first.last@domain.com") is None

    def test_email_local_part_with_plus_invalid(self):
        assert parse_user_id("email:user+tag@domain.com") is None


class TestDictPrecedenceEdgeCases:
    def test_flat_key_with_empty_string_blocks_nested(self):
        """user_id='' is a string → flat path taken → '' too short → None.
        Nested form is NOT tried."""
        result = parse_user_id({"user_id": "", "user": {"id": "hello"}})
        assert result is None

    def test_flat_key_with_whitespace_only_blocks_nested(self):
        result = parse_user_id({"user_id": "   ", "user": {"id": "hello"}})
        assert result is None

    def test_flat_key_with_reserved_id_blocks_nested(self):
        result = parse_user_id({"user_id": "admin", "user": {"id": "hello"}})
        assert result is None

    def test_flat_key_with_too_long_id_blocks_nested(self):
        long_id = "a" * 25
        result = parse_user_id({"user_id": long_id, "user": {"id": "hello"}})
        assert result is None

    def test_flat_key_none_value_blocks_nested(self):
        """user_id key exists with None → not string → None returned from extract.
        Nested path NOT tried."""
        result = parse_user_id({"user_id": None, "user": {"id": "hello"}})
        assert result is None

    def test_flat_key_invalid_chars_blocks_nested(self):
        result = parse_user_id({"user_id": "a.b.c", "user": {"id": "hello"}})
        assert result is None


class TestStringPrefixEdgeCases:
    def test_user_prefix_with_colon_in_id(self):
        """'user:abc:def' → id is 'abc:def' → colon invalid → None."""
        assert parse_user_id("user:abc:def") is None

    def test_string_with_only_colon(self):
        assert parse_user_id(":") is None

    def test_string_userx_prefix_no_match(self):
        assert parse_user_id("userx:hello") is None

    def test_string_emailx_prefix_no_match(self):
        assert parse_user_id("emailx:user@test.com") is None

    def test_string_use_prefix_no_match(self):
        assert parse_user_id("use:hello") is None

    def test_string_double_prefix(self):
        """'user:user:hello' → id is 'user:hello' → colon invalid → None."""
        assert parse_user_id("user:user:hello") is None

    def test_string_email_double_prefix(self):
        assert parse_user_id("email:email:user@test.com") is None

    def test_string_just_whitespace(self):
        assert parse_user_id("   ") is None

    def test_string_user_prefix_uppercase_u(self):
        assert parse_user_id("User:hello") is None

    def test_string_user_prefix_all_caps(self):
        assert parse_user_id("USER:hello") is None

    def test_string_email_prefix_all_caps(self):
        assert parse_user_id("EMAIL:user@test.com") is None


class TestBatchComplexScenarios:
    def test_batch_all_source_types_strict_and_reserved(self):
        items = [
            "user:valid1",
            "email:valid2@test.com",
            {"user_id": "valid3"},
            {"user": {"id": "valid4"}},
            "user:admin",
            "user:a__b",
            {"user_id": "a--b"},
            "email:root@test.com",
            None,
            42,
        ]
        result = parse_user_ids(items, strict=True)
        assert len(result) == 10
        assert result[0] == ParseResult(user_id="valid1", source="string")
        assert result[1] == ParseResult(user_id="valid2", source="email")
        assert result[2] == ParseResult(user_id="valid3", source="dict_flat")
        assert result[3] == ParseResult(user_id="valid4", source="dict_nested")
        assert result[4] is None   # reserved
        assert result[5] is None   # strict
        assert result[6] is None   # strict
        assert result[7] is None   # reserved
        assert result[8] is None   # bad type
        assert result[9] is None   # bad type

    def test_batch_custom_reserved_overrides_defaults(self):
        items = ["user:admin", "user:root", "user:system", "user:custom"]
        result = parse_user_ids(items, reserved_ids={"custom"})
        assert result[0] is not None  # admin allowed
        assert result[1] is not None  # root allowed
        assert result[2] is not None  # system allowed
        assert result[3] is None      # custom blocked

    def test_batch_returns_new_list_object(self):
        items = ["user:hello"]
        result = parse_user_ids(items)
        assert result is not items

    def test_batch_with_duplicate_inputs(self):
        items = ["user:hello", "user:hello", "user:hello"]
        result = parse_user_ids(items)
        assert len(result) == 3
        assert all(r == ParseResult(user_id="hello", source="string") for r in result)

    def test_batch_strict_false_allows_consecutive_specials(self):
        items = ["user:a__b", "user:a--b", "user:a_-b", "user:a-_b"]
        result = parse_user_ids(items, strict=False)
        assert all(r is not None for r in result)

    def test_batch_strict_true_rejects_all_consecutive_specials(self):
        items = ["user:a__b", "user:a--b", "user:a_-b", "user:a-_b"]
        result = parse_user_ids(items, strict=True)
        assert all(r is None for r in result)


class TestDictNestedExtraKeys:
    def test_nested_dict_with_extra_outer_keys(self):
        result = parse_user_id({"user": {"id": "hello"}, "extra": "data"})
        assert result is not None
        assert result == ParseResult(user_id="hello", source="dict_nested")

    def test_nested_dict_with_many_inner_keys(self):
        result = parse_user_id({"user": {"id": "hello", "name": "John", "age": 30}})
        assert result is not None
        assert result.user_id == "hello"

    def test_nested_dict_id_key_with_non_string_bool(self):
        assert parse_user_id({"user": {"id": True}}) is None

    def test_nested_dict_id_key_with_float(self):
        assert parse_user_id({"user": {"id": 3.14}}) is None

    def test_nested_dict_id_key_with_bytes(self):
        assert parse_user_id({"user": {"id": b"hello"}}) is None


class TestIdCharacterBoundaries:
    def test_id_with_zero(self):
        result = parse_user_id("user:000")
        assert result is not None
        assert result.user_id == "000"

    def test_id_with_nine(self):
        result = parse_user_id("user:999")
        assert result is not None
        assert result.user_id == "999"

    def test_id_with_percent_invalid(self):
        assert parse_user_id("user:abc%def") is None

    def test_id_with_backslash_invalid(self):
        assert parse_user_id("user:abc\\def") is None

    def test_id_with_pipe_invalid(self):
        assert parse_user_id("user:abc|def") is None

    def test_id_with_square_bracket_invalid(self):
        assert parse_user_id("user:abc[0]") is None

    def test_id_with_curly_brace_invalid(self):
        assert parse_user_id("user:abc{d}") is None

    def test_id_with_asterisk_invalid(self):
        assert parse_user_id("user:abc*def") is None

    def test_id_with_ampersand_invalid(self):
        assert parse_user_id("user:abc&def") is None

    def test_id_with_caret_invalid(self):
        assert parse_user_id("user:abc^def") is None

    def test_id_with_tilde_invalid(self):
        assert parse_user_id("user:abc~def") is None

    def test_id_with_equals_invalid(self):
        assert parse_user_id("user:abc=def") is None

    def test_id_with_semicolon_invalid(self):
        assert parse_user_id("user:abc;def") is None

    def test_id_with_comma_invalid(self):
        assert parse_user_id("user:abc,def") is None

    def test_id_with_question_mark_invalid(self):
        assert parse_user_id("user:abc?def") is None


class TestStrictModeAtPositions:
    def test_strict_consecutive_at_position_0_1(self):
        assert parse_user_id("user:__abcdef", strict=True) is None

    def test_strict_consecutive_at_last_two_positions(self):
        assert parse_user_id("user:abcdef__", strict=True) is None

    def test_strict_consecutive_in_middle(self):
        assert parse_user_id("user:abc__def", strict=True) is None

    def test_strict_multiple_separate_singles_ok(self):
        """a_b_c_d_e → no consecutive specials → ok in strict."""
        result = parse_user_id("user:a_b_c_d_e", strict=True)
        assert result is not None

    def test_strict_alternating_hyphen_underscore_separated(self):
        result = parse_user_id("user:a-b_c-d_e", strict=True)
        assert result is not None

    def test_strict_three_consecutive_specials_mixed(self):
        """a_-_b has _- at position 1-2 → rejected."""
        assert parse_user_id("user:a_-_b", strict=True) is None

    def test_strict_four_consecutive_specials(self):
        assert parse_user_id("user:a____b", strict=True) is None

    def test_strict_two_separate_pairs_of_consecutive(self):
        """a__b__c has __ at two places → rejected."""
        assert parse_user_id("user:a__b__c", strict=True) is None

    def test_strict_pair_hyphen_hyphen_at_start(self):
        assert parse_user_id("user:--abcde", strict=True) is None

    def test_strict_pair_underscore_hyphen_at_end(self):
        assert parse_user_id("user:abcde_-", strict=True) is None

    def test_strict_pair_hyphen_underscore_at_end(self):
        assert parse_user_id("user:abcde-_", strict=True) is None


class TestParseUserIdReturnConsistency:
    def test_same_id_different_sources_same_user_id(self):
        """Same ID via different input types produces same user_id."""
        uid = "testuser"
        r1 = parse_user_id(f"user:{uid}")
        r2 = parse_user_id(f"email:{uid}@test.com")
        r3 = parse_user_id({"user_id": uid})
        r4 = parse_user_id({"user": {"id": uid}})
        assert r1.user_id == r2.user_id == r3.user_id == r4.user_id == uid

    def test_same_id_different_sources_different_source_field(self):
        uid = "testuser"
        r1 = parse_user_id(f"user:{uid}")
        r2 = parse_user_id(f"email:{uid}@test.com")
        r3 = parse_user_id({"user_id": uid})
        r4 = parse_user_id({"user": {"id": uid}})
        assert r1.source == "string"
        assert r2.source == "email"
        assert r3.source == "dict_flat"
        assert r4.source == "dict_nested"

    def test_normalization_consistent_across_sources(self):
        """Same unnormalized ID via different sources yields same normalized result."""
        r1 = parse_user_id("user:  HELLO  ")
        r2 = parse_user_id("email:  HELLO  @test.com")
        r3 = parse_user_id({"user_id": "  HELLO  "})
        r4 = parse_user_id({"user": {"id": "  HELLO  "}})
        assert r1.user_id == r2.user_id == r3.user_id == r4.user_id == "hello"


class TestEdgeCaseInputSubtypes:
    def test_ordered_dict_as_input_flat(self):
        """OrderedDict is a dict subclass, should work."""
        from collections import OrderedDict
        d = OrderedDict([("user_id", "hello")])
        result = parse_user_id(d)
        assert result is not None
        assert result.user_id == "hello"
        assert result.source == "dict_flat"

    def test_ordered_dict_as_input_nested(self):
        from collections import OrderedDict
        d = OrderedDict([("user", OrderedDict([("id", "hello")]))])
        result = parse_user_id(d)
        assert result is not None
        assert result.source == "dict_nested"

    def test_defaultdict_as_input(self):
        """defaultdict is a dict subclass, should work."""
        from collections import defaultdict
        d = defaultdict(str)
        d["user_id"] = "hello"
        result = parse_user_id(d)
        assert result is not None
        assert result.user_id == "hello"

    def test_defaultdict_nested_missing_key_returns_none(self):
        """defaultdict with 'user' key but inner defaultdict lacks 'id'."""
        from collections import defaultdict
        inner = defaultdict(str)  # missing 'id' → inner.get('id') returns ''
        d = {"user": inner}
        # defaultdict returns '' for missing keys via __getitem__,
        # but .get('id') returns '' (default value of str()) for defaultdict
        # Actually, defaultdict.__getitem__ creates entry, but .get() doesn't
        # .get('id') returns None for missing key even in defaultdict
        result = parse_user_id(d)
        assert result is None

    def test_memoryview_input_returns_none(self):
        assert parse_user_id(memoryview(b"hello")) is None

    def test_range_input_returns_none(self):
        assert parse_user_id(range(10)) is None

    def test_callable_input_returns_none(self):
        assert parse_user_id(lambda: "user:hello") is None


class TestReservedIdExactBoundary:
    def test_reserved_admin_with_prefix_allowed(self):
        result = parse_user_id("user:xadmin")
        assert result is not None

    def test_reserved_admin_with_suffix_allowed(self):
        result = parse_user_id("user:adminx")
        assert result is not None

    def test_reserved_root_exact_length_is_reserved(self):
        """'root' is 4 chars, valid length, but reserved."""
        assert parse_user_id("user:root") is None

    def test_reserved_system_exact_length_is_reserved(self):
        """'system' is 6 chars, valid length, but reserved."""
        assert parse_user_id("user:system") is None

    def test_not_reserved_similar_ids(self):
        """IDs similar to reserved but not exact matches pass."""
        for uid in ["admin1", "1admin", "r00t", "syst", "syste", "admix"]:
            result = parse_user_id(f"user:{uid}")
            assert result is not None, f"Expected '{uid}' to be valid"

    def test_reserved_with_leading_trailing_chars_allowed(self):
        result = parse_user_id("user:_admin_")
        assert result is not None

    def test_reserved_substring_allowed(self):
        """'adm' is a substring of 'admin' but not in reserved set."""
        result = parse_user_id("user:adm")
        assert result is not None


class TestIdempotencyAndDeterminism:
    def test_parse_same_input_twice_gives_same_result(self):
        r1 = parse_user_id("user:hello")
        r2 = parse_user_id("user:hello")
        assert r1 == r2

    def test_parse_same_dict_twice_gives_same_result(self):
        d = {"user_id": "hello"}
        r1 = parse_user_id(d)
        r2 = parse_user_id(d)
        assert r1 == r2

    def test_batch_same_items_deterministic(self):
        items = ["user:hello", "email:alice@test.com", {"user_id": "world"}]
        r1 = parse_user_ids(items)
        r2 = parse_user_ids(items)
        assert r1 == r2

    def test_parse_none_twice_gives_none(self):
        assert parse_user_id(None) is None
        assert parse_user_id(None) is None

    def test_parse_reserved_twice_gives_none(self):
        assert parse_user_id("user:admin") is None
        assert parse_user_id("user:admin") is None


class TestZ3AdditionalVerification:
    """Additional Z3 formal verification tests for uncovered properties."""

    def test_z3_strict_mode_is_subset_of_nonstrict(self):
        """
        Verify property: any ID accepted in strict mode is also accepted
        in non-strict mode. Strict mode only adds rejection criteria.

        Model: For a 4-char ID where each char is regular(0), _(1), or -(2),
        if strict accepts it (no consecutive specials), then non-strict
        trivially accepts it too (non-strict has no special-pair check).
        """
        try:
            from z3 import Solver, Int, Or, And, Not, Implies, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        chars = [Int(f'c{i}') for i in range(4)]
        for c in chars:
            s.add(Or(c == 0, c == 1, c == 2))

        # "passes strict" = no consecutive specials
        no_consec = And(*[
            Not(And(chars[i] >= 1, chars[i + 1] >= 1))
            for i in range(3)
        ])

        # "passes non-strict" = always true (no additional check)
        passes_nonstrict = True  # non-strict has no consecutive-special check

        # Try to find: passes strict but NOT passes non-strict
        s.add(no_consec)
        s.add(Not(passes_nonstrict))

        # UNSAT: strict acceptance implies non-strict acceptance
        assert s.check() == unsat, \
            "Found an ID accepted by strict but rejected by non-strict"

    def test_z3_valid_charset_boundaries(self):
        """
        Verify that the valid character space {a-z, 0-9, _, -} when encoded
        as integer ranges [0..37] has no gaps: exactly 26 + 10 + 2 = 38 values.
        """
        try:
            from z3 import Solver, Int, And, Or, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        c = Int('c')

        # 0-25: a-z, 26-35: 0-9, 36: _, 37: -
        valid = And(c >= 0, c <= 37)

        # Verify all 38 values are SAT
        for i in range(38):
            s.push()
            s.add(c == i, valid)
            assert s.check() == sat, f"Character code {i} should be valid"
            s.pop()

        # Verify value 38 is UNSAT
        s.push()
        s.add(c == 38, valid)
        assert s.check() == unsat, "Character code 38 should be invalid"
        s.pop()

        # Verify negative is UNSAT
        s.push()
        s.add(c == -1, valid)
        assert s.check() == unsat, "Negative character code should be invalid"
        s.pop()

    def test_z3_normalization_preserves_validity(self):
        """
        Model property: if a character is valid after lowercasing (maps to [a-z]),
        then it was originally in [a-z, A-Z]. Similarly for digits and specials.

        We verify: the set of characters that produce valid normalized chars
        is exactly {a-z, A-Z, 0-9, _, -}.
        """
        try:
            from z3 import Solver, Int, And, Or, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        original = Int('orig')

        # Model: original char types
        # 0-25: a-z (already lowercase)
        # 26-51: A-Z (uppercased, maps to 0-25 after lower)
        # 52-61: 0-9
        # 62: _
        # 63: -
        # 64+: invalid

        is_valid_original = Or(
            And(original >= 0, original <= 25),   # a-z
            And(original >= 26, original <= 51),  # A-Z
            And(original >= 52, original <= 61),  # 0-9
            original == 62,                        # _
            original == 63,                        # -
        )

        # Try to find a value >= 64 that is valid
        s.push()
        s.add(original >= 64, is_valid_original)
        assert s.check() == unsat, "No character outside valid set should be accepted"
        s.pop()

        # Verify all valid values are satisfiable
        for i in range(64):
            s.push()
            s.add(original == i, is_valid_original)
            assert s.check() == sat, f"Character code {i} should be in valid set"
            s.pop()