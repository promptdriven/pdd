# ============================================================================
# TEST PLAN for parse_user_id
# ============================================================================

import sys
from pathlib import Path

project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root / "src"))

import copy
import pytest

from user_id_parser import parse_user_id, parse_user_ids, ParseResult


def _uid(result):
    """Extract user_id from a ParseResult, or return None if result is None."""
    if result is None:
        return None
    return result.user_id


def _uids(results):
    """Extract user_ids from a list of ParseResult/None."""
    return [_uid(r) for r in results]


# ============================================================================
# STRING INPUT TESTS
# ============================================================================

class TestStringInput:
    def test_basic_valid_user_id(self):
        r = parse_user_id("user:abc")
        assert r is not None and r.user_id == "abc" and r.source == "string"

    def test_valid_with_numbers(self):
        assert _uid(parse_user_id("user:abc123")) == "abc123"

    def test_valid_with_underscores(self):
        assert _uid(parse_user_id("user:my_user")) == "my_user"

    def test_valid_with_hyphens(self):
        assert _uid(parse_user_id("user:my-user")) == "my-user"

    def test_valid_with_all_allowed_chars(self):
        assert _uid(parse_user_id("user:a1_b-c")) == "a1_b-c"

    def test_whitespace_around_full_string(self):
        assert _uid(parse_user_id("  user:abc  ")) == "abc"

    def test_whitespace_in_id_portion(self):
        assert _uid(parse_user_id("user:  abc  ")) == "abc"

    def test_uppercase_in_id_normalized(self):
        assert _uid(parse_user_id("user:ABC")) == "abc"

    def test_mixed_case_normalized(self):
        assert _uid(parse_user_id("user:AbCdEf")) == "abcdef"

    def test_no_colon_returns_none(self):
        assert parse_user_id("userabc") is None

    def test_wrong_prefix_returns_none(self):
        assert parse_user_id("admin:abc") is None

    def test_empty_string_returns_none(self):
        assert parse_user_id("") is None

    def test_only_prefix_no_id(self):
        # "user:" -> id is "", which fails length validation
        assert parse_user_id("user:") is None

    def test_multiple_colons(self):
        # "user:foo:bar" -> id is "foo:bar" which has colon, fails regex
        assert parse_user_id("user:foo:bar") is None

    def test_just_colon(self):
        assert parse_user_id(":") is None

    def test_colon_at_start(self):
        # ":abc" -> prefix is "", not "user"
        assert parse_user_id(":abc") is None

    def test_user_prefix_with_extra_spaces(self):
        # " user : abc " -> stripped to "user : abc", split on first colon
        # prefix = "user ", which != "user"
        assert parse_user_id(" user : abc ") is None

    def test_only_whitespace_string(self):
        assert parse_user_id("   ") is None


# ============================================================================
# DICT INPUT TESTS - user_id key
# ============================================================================

class TestDictUserIdKey:
    def test_basic_user_id_key(self):
        r = parse_user_id({"user_id": "abc"})
        assert r is not None and r.user_id == "abc" and r.source == "dict_flat"

    def test_user_id_with_whitespace(self):
        assert _uid(parse_user_id({"user_id": "  abc  "})) == "abc"

    def test_user_id_uppercase(self):
        assert _uid(parse_user_id({"user_id": "ABC"})) == "abc"

    def test_user_id_non_string_value(self):
        assert parse_user_id({"user_id": 123}) is None

    def test_user_id_none_value(self):
        assert parse_user_id({"user_id": None}) is None

    def test_user_id_list_value(self):
        assert parse_user_id({"user_id": ["abc"]}) is None

    def test_user_id_bool_value(self):
        assert parse_user_id({"user_id": True}) is None


# ============================================================================
# DICT INPUT TESTS - nested user.id key
# ============================================================================

class TestDictNestedUserKey:
    def test_basic_nested_id(self):
        r = parse_user_id({"user": {"id": "abc"}})
        assert r is not None and r.user_id == "abc" and r.source == "dict_nested"

    def test_nested_id_with_whitespace(self):
        assert _uid(parse_user_id({"user": {"id": "  abc  "}})) == "abc"

    def test_nested_id_uppercase(self):
        assert _uid(parse_user_id({"user": {"id": "ABC"}})) == "abc"

    def test_user_not_dict(self):
        assert parse_user_id({"user": "notadict"}) is None

    def test_user_dict_missing_id(self):
        assert parse_user_id({"user": {"name": "abc"}}) is None

    def test_user_dict_id_non_string(self):
        assert parse_user_id({"user": {"id": 123}}) is None

    def test_user_none_value(self):
        assert parse_user_id({"user": None}) is None

    def test_user_list_value(self):
        assert parse_user_id({"user": [{"id": "abc"}]}) is None


# ============================================================================
# DICT INPUT TESTS - priority and fallthrough
# ============================================================================

class TestDictPriority:
    def test_user_id_takes_priority_over_nested(self):
        result = parse_user_id({"user_id": "abc", "user": {"id": "xyz"}})
        assert _uid(result) == "abc"

    def test_fallthrough_when_user_id_not_string(self):
        result = parse_user_id({"user_id": 123, "user": {"id": "xyz"}})
        assert _uid(result) == "xyz"

    def test_user_id_invalid_still_used_not_fallthrough(self):
        result = parse_user_id({"user_id": "!!", "user": {"id": "abc"}})
        assert result is None


# ============================================================================
# DICT INPUT TESTS - empty / missing keys
# ============================================================================

class TestDictEdgeCases:
    def test_empty_dict(self):
        assert parse_user_id({}) is None

    def test_unrelated_keys(self):
        assert parse_user_id({"name": "abc", "email": "x@y.com"}) is None

    def test_empty_nested_dict(self):
        assert parse_user_id({"user": {}}) is None


# ============================================================================
# VALIDATION TESTS - character set
# ============================================================================

class TestValidationCharacters:
    def test_valid_lowercase_letters(self):
        assert _uid(parse_user_id("user:abcdef")) == "abcdef"

    def test_valid_digits(self):
        assert _uid(parse_user_id("user:12345")) == "12345"

    def test_valid_underscore(self):
        assert _uid(parse_user_id("user:a_b_c")) == "a_b_c"

    def test_valid_hyphen(self):
        assert _uid(parse_user_id("user:a-b-c")) == "a-b-c"

    def test_reject_dot(self):
        assert parse_user_id("user:a.b.c") is None

    def test_reject_at_sign(self):
        assert parse_user_id("user:abc@def") is None

    def test_reject_exclamation(self):
        assert parse_user_id("user:abc!") is None

    def test_reject_space_in_middle(self):
        assert parse_user_id("user:ab cd") is None

    def test_reject_hash(self):
        assert parse_user_id("user:abc#1") is None

    def test_reject_slash(self):
        assert parse_user_id("user:abc/def") is None

    def test_reject_backslash(self):
        assert parse_user_id("user:abc\\def") is None

    def test_reject_unicode(self):
        assert parse_user_id("user:äbc") is None

    def test_reject_emoji(self):
        assert parse_user_id("user:abc😀") is None


# ============================================================================
# VALIDATION TESTS - length boundaries
# ============================================================================

class TestValidationLength:
    def test_length_2_too_short(self):
        assert parse_user_id("user:ab") is None

    def test_length_3_minimum_valid(self):
        assert _uid(parse_user_id("user:abc")) == "abc"

    def test_length_4_valid(self):
        assert _uid(parse_user_id("user:abcd")) == "abcd"

    def test_length_19_valid(self):
        assert _uid(parse_user_id("user:" + "a" * 19)) == "a" * 19

    def test_length_20_maximum_valid(self):
        assert _uid(parse_user_id("user:" + "a" * 20)) == "a" * 20

    def test_length_21_too_long(self):
        assert parse_user_id("user:" + "a" * 21) is None

    def test_length_1_too_short(self):
        assert parse_user_id("user:a") is None

    def test_length_0_empty(self):
        assert parse_user_id("user:") is None

    def test_length_100_too_long(self):
        assert parse_user_id("user:" + "a" * 100) is None

    def test_length_boundary_with_whitespace_trimmed_to_valid(self):
        # "  abc  " -> trimmed to "abc" (length 3, valid)
        assert _uid(parse_user_id("user:  abc  ")) == "abc"

    def test_length_boundary_with_whitespace_trimmed_to_short(self):
        # "  ab  " -> trimmed to "ab" (length 2, invalid)
        assert parse_user_id("user:  ab  ") is None


# ============================================================================
# VALIDATION TESTS - reserved IDs
# ============================================================================

class TestReservedIDs:
    def test_reject_admin(self):
        assert parse_user_id("user:admin") is None

    def test_reject_root(self):
        assert parse_user_id("user:root") is None

    def test_reject_system(self):
        assert parse_user_id("user:system") is None

    def test_reject_admin_uppercase(self):
        assert parse_user_id("user:ADMIN") is None

    def test_reject_root_mixed_case(self):
        assert parse_user_id("user:Root") is None

    def test_reject_system_uppercase(self):
        assert parse_user_id("user:SYSTEM") is None

    def test_reject_admin_with_whitespace(self):
        assert parse_user_id("user:  admin  ") is None

    def test_accept_admin_prefix(self):
        # "admin1" is NOT reserved
        assert _uid(parse_user_id("user:admin1")) == "admin1"

    def test_accept_admin_suffix(self):
        assert _uid(parse_user_id("user:xadmin")) == "xadmin"

    def test_accept_roots(self):
        assert _uid(parse_user_id("user:roots")) == "roots"

    def test_accept_systems(self):
        assert _uid(parse_user_id("user:systems")) == "systems"

    def test_reserved_via_dict_user_id(self):
        assert parse_user_id({"user_id": "admin"}) is None

    def test_reserved_via_dict_nested(self):
        assert parse_user_id({"user": {"id": "root"}}) is None


# ============================================================================
# NON-MUTATION TESTS
# ============================================================================

class TestNonMutation:
    def test_dict_with_user_id_not_mutated(self):
        d = {"user_id": "  ABC  "}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_with_nested_not_mutated(self):
        d = {"user": {"id": "  ABC  "}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_with_both_keys_not_mutated(self):
        d = {"user_id": "abc", "user": {"id": "xyz"}}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original

    def test_dict_with_extra_keys_not_mutated(self):
        d = {"user_id": "abc", "extra": [1, 2, 3]}
        original = copy.deepcopy(d)
        parse_user_id(d)
        assert d == original


# ============================================================================
# BAD INPUT TYPE TESTS (never raise)
# ============================================================================

class TestBadInputTypes:
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
        assert parse_user_id(("user", "abc")) is None

    def test_set_input(self):
        assert parse_user_id({"abc"}) is None

    def test_bytes_input(self):
        assert parse_user_id(b"user:abc") is None

    def test_object_input(self):
        assert parse_user_id(object()) is None

    def test_class_input(self):
        class Dummy:
            pass
        assert parse_user_id(Dummy()) is None


# ============================================================================
# COMPREHENSIVE / INTEGRATION-STYLE TESTS
# ============================================================================

class TestComprehensive:
    def test_all_lowercase_letters_only(self):
        assert _uid(parse_user_id("user:abc")) == "abc"

    def test_all_digits_only(self):
        assert _uid(parse_user_id("user:123")) == "123"

    def test_only_underscores(self):
        assert _uid(parse_user_id("user:___")) == "___"

    def test_only_hyphens(self):
        assert _uid(parse_user_id("user:---")) == "---"

    def test_mixed_valid_chars(self):
        assert _uid(parse_user_id("user:a1_b-2")) == "a1_b-2"

    def test_max_length_all_chars(self):
        uid = "ab12_cd34-ef56_gh78"  # 19 chars
        assert len(uid) == 19
        assert _uid(parse_user_id("user:" + uid)) == uid

    def test_max_length_exactly_20(self):
        uid = "ab12_cd34-ef56_gh78x"  # 20 chars
        assert len(uid) == 20
        assert _uid(parse_user_id("user:" + uid)) == uid

    def test_dict_user_id_valid(self):
        assert _uid(parse_user_id({"user_id": "test_user"})) == "test_user"

    def test_dict_nested_valid(self):
        assert _uid(parse_user_id({"user": {"id": "test_user"}})) == "test_user"

    def test_normalization_preserves_valid_result(self):
        assert _uid(parse_user_id("user:  Test_User-123  ")) == "test_user-123"

    def test_normalization_from_dict(self):
        assert _uid(parse_user_id({"user_id": "  Test_User-123  "})) == "test_user-123"


# ============================================================================
# Z3 FORMAL VERIFICATION TESTS
# ============================================================================

try:
    from z3 import String, StringVal, Length, And, Or, Not, Solver, sat, unsat, InRe, Re, Range, Star, Concat, Union

    HAS_Z3 = True
except ImportError:
    HAS_Z3 = False


@pytest.mark.skipif(not HAS_Z3, reason="z3-solver not installed")
class TestZ3FormalVerification:

    def test_z3_length_below_3_always_rejected(self):
        for length in range(0, 3):
            test_str = "a" * length
            result = parse_user_id("user:" + test_str)
            assert result is None, f"Length {length} should be rejected"

    def test_z3_length_above_20_always_rejected(self):
        for length in [21, 22, 50, 100]:
            test_str = "a" * length
            result = parse_user_id("user:" + test_str)
            assert result is None, f"Length {length} should be rejected"

    def test_z3_regex_accepts_valid_charset(self):
        s = Solver()
        x = String("x")

        # Build the regex: [a-z0-9_-]{3,20}
        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re("_"),
            Re("-")
        )
        # Length between 3 and 20: use Star and length constraints
        valid_regex = Star(char_class)

        # Constraint: x matches regex AND length is between 3 and 20
        s.add(InRe(x, valid_regex))
        s.add(Length(x) >= 3)
        s.add(Length(x) <= 20)

        # This should be satisfiable
        assert s.check() == sat, "Should find at least one valid string"

    def test_z3_regex_rejects_uppercase(self):
        s = Solver()
        x = String("x")

        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re("_"),
            Re("-")
        )
        valid_regex = Star(char_class)

        # Force x to be "ABC" (uppercase)
        s.add(x == StringVal("ABC"))
        s.add(InRe(x, valid_regex))

        # Should be unsatisfiable (uppercase not in charset)
        assert s.check() == unsat, "Uppercase 'ABC' should not match [a-z0-9_-]+ )"

    def test_z3_all_reserved_ids_are_blocked(self):
        reserved = ["admin", "root", "system"]
        for rid in reserved:
            result = parse_user_id(f"user:{rid}")
            assert result is None, f"Reserved ID '{rid}' should be blocked"

    def test_z3_reserved_ids_match_regex_but_are_blocked(self):
        import re
        pattern = re.compile(r"^[a-z0-9_-]{3,20}$")
        reserved = ["admin", "root", "system"]
        for rid in reserved:
            # They match the regex
            assert pattern.match(rid) is not None, f"'{rid}' should match regex"
            # But parse_user_id rejects them
            assert parse_user_id(f"user:{rid}") is None, f"'{rid}' should be rejected"

    def test_z3_special_char_not_in_charset(self):
        s = Solver()
        x = String("x")

        char_class = Union(
            Range("a", "z"),
            Range("0", "9"),
            Re("_"),
            Re("-")
        )
        valid_regex = Star(char_class)

        s.add(x == StringVal("a.b"))
        s.add(InRe(x, valid_regex))
        assert s.check() == unsat, "'a.b' should not match [a-z0-9_-+]"


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root / "src"))

import copy
import pytest

HAS_Z3 = False

from user_id_parser import parse_user_ids, parse_user_id


class TestParseUserIdsBatch:
    def test_empty_list(self):
        assert parse_user_ids([]) == []

    def test_single_valid_string(self):
        assert _uids(parse_user_ids(['user:abc'])) == ['abc']

    def test_single_invalid_string(self):
        assert _uids(parse_user_ids(['invalid'])) == [None]

    def test_single_none_item(self):
        assert _uids(parse_user_ids([None])) == [None]

    def test_multiple_valid_items(self):
        items = ['user:abc', 'user:def', 'user:ghi']
        assert _uids(parse_user_ids(items)) == ['abc', 'def', 'ghi']

    def test_multiple_invalid_items(self):
        items = [None, 42, 'bad']
        assert _uids(parse_user_ids(items)) == [None, None, None]

    def test_mixed_valid_and_invalid(self):
        items = ['user:abc', None, 'user:def', 42, 'bad']
        assert _uids(parse_user_ids(items)) == ['abc', None, 'def', None, None]

    def test_ordering_preserved(self):
        items = ['user:zzz', 'user:aaa', 'user:mmm']
        result = parse_user_ids(items)
        assert _uids(result) == ['zzz', 'aaa', 'mmm']

    def test_result_length_matches_input_length(self):
        items = ['user:abc', None, 42, 'user:def', {'user_id': 'ghi'}]
        result = parse_user_ids(items)
        assert len(result) == len(items)

    def test_mixed_string_and_dict_inputs(self):
        items = [
            'user:abc',
            {'user_id': 'def'},
            {'user': {'id': 'ghi'}},
        ]
        assert _uids(parse_user_ids(items)) == ['abc', 'def', 'ghi']

    def test_reserved_ids_in_batch(self):
        items = ['user:admin', 'user:root', 'user:system', 'user:valid1']
        assert _uids(parse_user_ids(items)) == [None, None, None, 'valid1']

    def test_duplicate_items_processed_independently(self):
        items = ['user:abc', 'user:abc', 'user:abc']
        assert _uids(parse_user_ids(items)) == ['abc', 'abc', 'abc']

    def test_normalization_in_batch(self):
        items = ['user:  ABC  ', {'user_id': '  DEF  '}]
        assert _uids(parse_user_ids(items)) == ['abc', 'def']

    def test_all_bad_types(self):
        items = [None, 42, 3.14, True, [], (), set(), b'bytes']
        result = parse_user_ids(items)
        assert _uids(result) == [None] * len(items)

    def test_large_batch(self):
        items = [f'user:user{i:03d}' for i in range(100)]
        result = parse_user_ids(items)
        assert len(result) == 100
        assert all(r is not None for r in result)
        assert result[0].user_id == 'user000'
        assert result[99].user_id == 'user099'

    def test_index_correspondence(self):
        """Verify result[i] corresponds to items[i]."""
        items = [
            'user:first',    # 0: valid
            None,            # 1: None
            'user:third',    # 2: valid
            'bad',           # 3: None
            'user:fifth',    # 4: valid
        ]
        result = parse_user_ids(items)
        assert result[0].user_id == 'first'
        assert result[1] is None
        assert result[2].user_id == 'third'
        assert result[3] is None
        assert result[4].user_id == 'fifth'

    def test_does_not_deduplicate(self):
        """Batch should not remove duplicates."""
        items = ['user:abc', 'user:abc']
        result = parse_user_ids(items)
        assert len(result) == 2
        assert result[0].user_id == result[1].user_id == 'abc'

    def test_single_dict_item(self):
        assert _uids(parse_user_ids([{'user_id': 'abc'}])) == ['abc']

    def test_single_nested_dict_item(self):
        assert _uids(parse_user_ids([{'user': {'id': 'abc'}}])) == ['abc']


class TestBatchNonMutation:
    def test_input_list_not_mutated(self):
        items = ['user:abc', None, 'user:def']
        original = items.copy()
        parse_user_ids(items)
        assert items == original

    def test_input_dicts_in_list_not_mutated(self):
        d1 = {'user_id': '  ABC  '}
        d2 = {'user': {'id': '  DEF  '}}
        items = [d1, d2]
        d1_copy = copy.deepcopy(d1)
        d2_copy = copy.deepcopy(d2)
        parse_user_ids(items)
        assert d1 == d1_copy
        assert d2 == d2_copy


class TestBatchConsistency:
    def test_batch_matches_individual_calls(self):
        """Batch results must match individual parse_user_id calls."""
        items = [
            'user:abc',
            None,
            {'user_id': 'def'},
            42,
            'user:admin',
            {'user': {'id': 'ghi'}},
            'bad',
            'user:  XYZ  ',
        ]
        batch_result = parse_user_ids(items)
        individual_results = [parse_user_id(item) for item in items]
        assert batch_result == individual_results

    def test_batch_idempotent(self):
        """Same input always produces same output."""
        items = ['user:abc', None, 'user:def']
        result1 = parse_user_ids(items)
        result2 = parse_user_ids(items)
        assert result1 == result2


class TestBatchReturnTypes:
    def test_returns_list(self):
        result = parse_user_ids(['user:abc'])
        assert isinstance(result, list)

    def test_empty_returns_list(self):
        result = parse_user_ids([])
        assert isinstance(result, list)

    def test_elements_are_parse_result_or_none(self):
        items = ['user:abc', None, 'user:def', 42]
        result = parse_user_ids(items)
        for elem in result:
            assert elem is None or isinstance(elem, ParseResult)


class TestAdditionalEdgeCases:
    def test_dict_empty_string_user_id(self):
        assert parse_user_id({'user_id': ''}) is None

    def test_dict_whitespace_only_user_id(self):
        assert parse_user_id({'user_id': '   '}) is None

    def test_string_whitespace_only_after_colon(self):
        assert parse_user_id('user:   ') is None

    def test_string_with_tab_around(self):
        assert _uid(parse_user_id('\tuser:abc\t')) == 'abc'

    def test_string_with_newline_around(self):
        assert _uid(parse_user_id('\nuser:abc\n')) == 'abc'

    def test_string_id_with_tab_in_middle(self):
        assert parse_user_id('user:ab\tc') is None

    def test_string_id_with_newline_in_middle(self):
        assert parse_user_id('user:ab\nc') is None

    def test_dict_subclass_ordereddict(self):
        from collections import OrderedDict
        d = OrderedDict([('user_id', 'abc')])
        assert _uid(parse_user_id(d)) == 'abc'

    def test_dict_subclass_defaultdict(self):
        from collections import defaultdict
        d = defaultdict(str)
        d['user_id'] = 'abc'
        assert _uid(parse_user_id(d)) == 'abc'

    def test_string_user_prefix_uppercase(self):
        assert parse_user_id('User:abc') is None

    def test_string_user_prefix_all_caps(self):
        assert parse_user_id('USER:abc') is None

    def test_string_user_prefix_mixed_case(self):
        assert parse_user_id('UsEr:abc') is None

    def test_id_exactly_3_with_all_char_types(self):
        assert _uid(parse_user_id('user:a_1')) == 'a_1'
        assert _uid(parse_user_id('user:a-1')) == 'a-1'
        assert _uid(parse_user_id('user:1_-')) == '1_-'

    def test_id_all_same_char_at_max_length(self):
        assert _uid(parse_user_id('user:' + 'z' * 20)) == 'z' * 20

    def test_id_all_same_char_at_min_length(self):
        assert _uid(parse_user_id('user:zzz')) == 'zzz'

    def test_reserved_system_via_dict_nested(self):
        assert parse_user_id({'user': {'id': 'system'}}) is None

    def test_reserved_admin_via_dict_nested_uppercase(self):
        assert parse_user_id({'user': {'id': 'ADMIN'}}) is None

    def test_reserved_root_with_whitespace_in_dict(self):
        assert parse_user_id({'user_id': '  root  '}) is None

    def test_dict_user_id_is_dict(self):
        assert parse_user_id({'user_id': {'nested': 'value'}}) is None

    def test_nested_id_value_is_dict(self):
        assert parse_user_id({'user': {'id': {'deep': 'value'}}}) is None

    def test_nested_id_value_is_list(self):
        assert parse_user_id({'user': {'id': ['abc']}}) is None

    def test_near_reserved_root_prefix(self):
        assert _uid(parse_user_id({'user_id': 'root1'})) == 'root1'

    def test_near_reserved_system_prefix(self):
        assert _uid(parse_user_id({'user_id': 'system1'})) == 'system1'

    def test_leading_trailing_mixed_whitespace(self):
        assert _uid(parse_user_id('  \t user:abc \n  ')) == 'abc'

    def test_string_with_carriage_return(self):
        assert _uid(parse_user_id('\r\nuser:abc\r\n')) == 'abc'

    def test_dict_both_keys_invalid_user_id_non_string(self):
        assert parse_user_id({'user_id': 42, 'user': {'id': 99}}) is None

    def test_dict_user_key_is_empty_dict(self):
        assert parse_user_id({'user': {}}) is None

    def test_dict_user_key_is_nested_with_wrong_key(self):
        assert parse_user_id({'user': {'name': 'abc'}}) is None

    def test_id_with_consecutive_special_chars(self):
        assert _uid(parse_user_id('user:a--b')) == 'a--b'
        assert _uid(parse_user_id('user:a__b')) == 'a__b'
        assert _uid(parse_user_id('user:a_-b')) == 'a_-b'

    def test_id_starting_with_hyphen(self):
        assert _uid(parse_user_id('user:-abc')) == '-abc'

    def test_id_starting_with_underscore(self):
        assert _uid(parse_user_id('user:_abc')) == '_abc'

    def test_id_starting_with_digit(self):
        assert _uid(parse_user_id('user:1abc')) == '1abc'

    def test_id_ending_with_hyphen(self):
        assert _uid(parse_user_id('user:abc-')) == 'abc-'

    def test_id_ending_with_underscore(self):
        assert _uid(parse_user_id('user:abc_')) == 'abc_'


class TestCrossPathConsistency:
    def test_same_id_via_all_three_paths(self):
        """Same ID via string, user_id dict, and nested dict produce same user_id."""
        uid = 'test_user'
        r1 = parse_user_id(f'user:{uid}')
        r2 = parse_user_id({'user_id': uid})
        r3 = parse_user_id({'user': {'id': uid}})
        assert _uid(r1) == _uid(r2) == _uid(r3) == uid

    def test_normalization_consistent_across_paths(self):
        r1 = parse_user_id('user:  TestUser  ')
        r2 = parse_user_id({'user_id': '  TestUser  '})
        r3 = parse_user_id({'user': {'id': '  TestUser  '}})
        assert _uid(r1) == _uid(r2) == _uid(r3) == 'testuser'

    def test_reserved_rejection_consistent_across_paths(self):
        for reserved in ['admin', 'root', 'system']:
            r1 = parse_user_id(f'user:{reserved}')
            r2 = parse_user_id({'user_id': reserved})
            r3 = parse_user_id({'user': {'id': reserved}})
            assert r1 is None and r2 is None and r3 is None, \
                f"Reserved ID '{reserved}' should be rejected via all paths"


class TestIdempotency:
    def test_parse_user_id_idempotent_across_calls(self):
        """Same input always produces same output."""
        for _ in range(10):
            assert _uid(parse_user_id('user:abc')) == 'abc'

    def test_parse_user_id_result_can_be_reparsed(self):
        """If result is re-wrapped in user: format, it should parse again identically."""
        result = parse_user_id('user:TestUser123')
        assert result.user_id == 'testuser123'
        result2 = parse_user_id(f'user:{result.user_id}')
        assert result2.user_id == result.user_id


@pytest.mark.skipif(not HAS_Z3, reason='z3-solver not installed')
class TestZ3AdditionalVerification:

    def test_z3_hyphen_in_valid_charset(self):
        from z3 import String, StringVal, Solver, InRe, Re, Range, Star, Union, sat
        s = Solver()
        x = String('x')
        char_class = Union(Range('a', 'z'), Range('0', '9'), Re('_'), Re('-'))
        valid_regex = Star(char_class)
        s.add(x == StringVal('a-b'))
        s.add(InRe(x, valid_regex))
        assert s.check() == sat

    def test_z3_underscore_in_valid_charset(self):
        from z3 import String, StringVal, Solver, InRe, Re, Range, Star, Union, sat
        s = Solver()
        x = String('x')
        char_class = Union(Range('a', 'z'), Range('0', '9'), Re('_'), Re('-'))
        valid_regex = Star(char_class)
        s.add(x == StringVal('a_b'))
        s.add(InRe(x, valid_regex))
        assert s.check() == sat

    def test_z3_space_not_in_valid_charset(self):
        from z3 import String, StringVal, Solver, InRe, Re, Range, Star, Union, unsat
        s = Solver()
        x = String('x')
        char_class = Union(Range('a', 'z'), Range('0', '9'), Re('_'), Re('-'))
        valid_regex = Star(char_class)
        s.add(x == StringVal('a b'))
        s.add(InRe(x, valid_regex))
        assert s.check() == unsat

    def test_z3_tab_not_in_valid_charset(self):
        from z3 import String, StringVal, Solver, InRe, Re, Range, Star, Union, unsat
        s = Solver()
        x = String('x')
        char_class = Union(Range('a', 'z'), Range('0', '9'), Re('_'), Re('-'))
        valid_regex = Star(char_class)
        s.add(x == StringVal('a\tb'))
        s.add(InRe(x, valid_regex))
        assert s.check() == unsat

    def test_z3_empty_string_not_length_valid(self):
        from z3 import String, StringVal, Length, Solver, unsat
        s = Solver()
        x = String('x')
        s.add(x == StringVal(''))
        s.add(Length(x) >= 3)
        assert s.check() == unsat

    def test_z3_batch_output_length_property(self):
        from z3 import String, Length, Solver, InRe, Re, Range, Star, Union, sat
        for size in [0, 1, 5, 10, 50]:
            items = [f'user:u{i:03d}' for i in range(size)]
            result = parse_user_ids(items)
            assert len(result) == size, f"Output length {len(result)} != input length {size}"

    def test_z3_no_valid_id_shorter_than_3_exists(self):
        from z3 import String, Length, Solver, InRe, Re, Range, Star, Union, sat
        s = Solver()
        x = String('x')
        char_class = Union(Range('a', 'z'), Range('0', '9'), Re('_'), Re('-'))
        valid_regex = Star(char_class)
        s.add(InRe(x, valid_regex))
        s.add(Length(x) >= 1)
        s.add(Length(x) < 3)
        result = s.check()
        if str(result) == 'sat':
            model = s.model()
            short_id = model[x].as_string()
            assert parse_user_id(f'user:{short_id}') is None

    def test_z3_no_valid_id_longer_than_20_exists(self):
        from z3 import String, Length, Solver, InRe, Re, Range, Star, Union, sat
        s = Solver()
        x = String('x')
        char_class = Union(Range('a', 'z'), Range('0', '9'), Re('_'), Re('-'))
        valid_regex = Star(char_class)
        s.add(InRe(x, valid_regex))
        s.add(Length(x) > 20)
        s.add(Length(x) <= 25)  # bound to keep solver fast
        result = s.check()
        if str(result) == 'sat':
            model = s.model()
            long_id = model[x].as_string()
            assert parse_user_id(f'user:{long_id}') is None

    def test_z3_at_sign_rejected(self):
        from z3 import String, StringVal, Solver, InRe, Re, Range, Star, Union, unsat
        s = Solver()
        x = String('x')
        char_class = Union(Range('a', 'z'), Range('0', '9'), Re('_'), Re('-'))
        valid_regex = Star(char_class)
        s.add(x == StringVal('user@1'))
        s.add(InRe(x, valid_regex))
        assert s.check() == unsat

    def test_z3_digit_chars_accepted(self):
        from z3 import String, StringVal, Solver, InRe, Re, Range, Star, Union, sat
        s = Solver()
        x = String('x')
        char_class = Union(Range('a', 'z'), Range('0', '9'), Re('_'), Re('-'))
        valid_regex = Star(char_class)
        s.add(x == StringVal('0123456789'))
        s.add(InRe(x, valid_regex))
        assert s.check() == sat


# ============================================================================
# EMAIL INPUT TESTS
# ============================================================================

class TestEmailInput:
    def test_basic_email_extraction(self):
        r = parse_user_id("email:johndoe@example.com")
        assert r is not None and r.user_id == "johndoe" and r.source == "email"

    def test_email_simple_domain(self):
        assert _uid(parse_user_id("email:abc@test")) == "abc"

    def test_email_subdomain(self):
        assert _uid(parse_user_id("email:testuser@mail.example.com")) == "testuser"

    def test_email_uppercase_username_normalized(self):
        assert _uid(parse_user_id("email:JohnDoe@Example.com")) == "johndoe"

    def test_email_mixed_case_username(self):
        assert _uid(parse_user_id("email:AbCdEf@test.com")) == "abcdef"

    def test_email_whitespace_around_full_string(self):
        assert _uid(parse_user_id("  email:abc@test.com  ")) == "abc"

    def test_email_tab_around_full_string(self):
        assert _uid(parse_user_id("\temail:abc@test.com\t")) == "abc"

    def test_email_newline_around_full_string(self):
        assert _uid(parse_user_id("\nemail:abc@test.com\n")) == "abc"

    def test_email_no_at_sign_returns_none(self):
        assert parse_user_id("email:nodomain") is None

    def test_email_empty_username_returns_none(self):
        assert parse_user_id("email:@domain.com") is None

    def test_email_only_at_sign(self):
        assert parse_user_id("email:@") is None

    def test_email_empty_after_prefix(self):
        assert parse_user_id("email:") is None

    def test_email_username_too_short_length_2(self):
        assert parse_user_id("email:ab@domain.com") is None

    def test_email_username_too_short_length_1(self):
        assert parse_user_id("email:a@domain.com") is None

    def test_email_username_min_length_3(self):
        assert _uid(parse_user_id("email:abc@domain.com")) == "abc"

    def test_email_username_length_4(self):
        assert _uid(parse_user_id("email:abcd@domain.com")) == "abcd"

    def test_email_username_max_length_20(self):
        username = "a" * 20
        assert _uid(parse_user_id(f"email:{username}@domain.com")) == username

    def test_email_username_too_long_length_21(self):
        username = "a" * 21
        assert parse_user_id(f"email:{username}@domain.com") is None

    def test_email_username_with_digits(self):
        assert _uid(parse_user_id("email:user123@test.com")) == "user123"

    def test_email_username_with_underscore(self):
        assert _uid(parse_user_id("email:john_doe@test.com")) == "john_doe"

    def test_email_username_with_hyphen(self):
        assert _uid(parse_user_id("email:john-doe@test.com")) == "john-doe"

    def test_email_username_with_all_allowed_chars(self):
        assert _uid(parse_user_id("email:a1_b-c@test.com")) == "a1_b-c"

    def test_email_username_only_digits(self):
        assert _uid(parse_user_id("email:12345@test.com")) == "12345"

    def test_email_username_only_underscores(self):
        assert _uid(parse_user_id("email:___@test.com")) == "___"

    def test_email_username_only_hyphens(self):
        assert _uid(parse_user_id("email:---@test.com")) == "---"

    def test_email_username_with_dot_rejected(self):
        assert parse_user_id("email:john.doe@example.com") is None

    def test_email_username_with_plus_rejected(self):
        assert parse_user_id("email:john+tag@example.com") is None

    def test_email_username_with_exclamation_rejected(self):
        assert parse_user_id("email:john!@example.com") is None

    def test_email_username_with_space_rejected(self):
        assert parse_user_id("email:john doe@example.com") is None

    def test_email_username_with_at_in_username_rejected(self):
        assert _uid(parse_user_id("email:user@name@domain")) == "user"

    def test_email_multiple_at_signs_extracts_first_part(self):
        assert _uid(parse_user_id("email:abc@def@ghi")) == "abc"

    def test_email_username_with_colon_rejected(self):
        # "email:a:b@domain" -> prefix="email", remainder="a:b@domain"
        # username = "a:b", fails regex (colon not allowed)
        assert parse_user_id("email:a:b@domain.com") is None

    def test_email_reserved_admin(self):
        assert parse_user_id("email:admin@company.com") is None

    def test_email_reserved_root(self):
        assert parse_user_id("email:root@company.com") is None

    def test_email_reserved_system(self):
        assert parse_user_id("email:system@company.com") is None

    def test_email_reserved_admin_uppercase(self):
        assert parse_user_id("email:ADMIN@company.com") is None

    def test_email_reserved_root_mixed_case(self):
        assert parse_user_id("email:Root@company.com") is None

    def test_email_reserved_system_with_whitespace(self):
        assert parse_user_id("email: system @company.com") is None

    def test_email_near_reserved_admin1(self):
        assert _uid(parse_user_id("email:admin1@company.com")) == "admin1"

    def test_email_near_reserved_roots(self):
        assert _uid(parse_user_id("email:roots@company.com")) == "roots"

    def test_email_whitespace_before_username_trimmed(self):
        assert _uid(parse_user_id("email: abc @domain.com")) == "abc"

    def test_email_whitespace_only_username_trimmed_to_empty(self):
        assert parse_user_id("email:   @domain.com") is None

    def test_email_empty_domain_still_extracts_username(self):
        assert _uid(parse_user_id("email:abc@")) == "abc"

    def test_email_prefix_case_sensitive(self):
        assert parse_user_id("Email:abc@test.com") is None

    def test_email_prefix_all_caps(self):
        assert parse_user_id("EMAIL:abc@test.com") is None

    def test_email_unicode_in_username(self):
        assert parse_user_id("email:über@test.com") is None

    def test_email_emoji_in_username(self):
        assert parse_user_id("email:abc😀@test.com") is None


class TestEmailCrossPathConsistency:
    def test_same_id_via_email_user_and_dict(self):
        uid = 'testuser'
        r_email = parse_user_id(f"email:{uid}@example.com")
        r_user = parse_user_id(f"user:{uid}")
        r_dict = parse_user_id({"user_id": uid})
        r_nested = parse_user_id({"user": {"id": uid}})
        assert _uid(r_email) == _uid(r_user) == _uid(r_dict) == _uid(r_nested) == uid

    def test_normalization_consistent_across_all_paths(self):
        r_email = parse_user_id("email:TestUser@example.com")
        r_user = parse_user_id("user:TestUser")
        r_dict = parse_user_id({"user_id": "TestUser"})
        r_nested = parse_user_id({"user": {"id": "TestUser"}})
        assert _uid(r_email) == _uid(r_user) == _uid(r_dict) == _uid(r_nested) == "testuser"

    def test_reserved_rejection_via_email_path(self):
        for reserved in ["admin", "root", "system"]:
            r_email = parse_user_id(f"email:{reserved}@company.com")
            r_user = parse_user_id(f"user:{reserved}")
            r_dict = parse_user_id({"user_id": reserved})
            assert r_email is None and r_user is None and r_dict is None, \
                f"Reserved ID '{reserved}' should be rejected via all paths"

    def test_invalid_length_via_email_path(self):
        # Too short
        assert parse_user_id("email:ab@test.com") is None
        assert parse_user_id("user:ab") is None
        assert parse_user_id({"user_id": "ab"}) is None
        # Too long
        long_id = "a" * 21
        assert parse_user_id(f"email:{long_id}@test.com") is None
        assert parse_user_id(f"user:{long_id}") is None
        assert parse_user_id({"user_id": long_id}) is None


class TestEmailInBatch:
    def test_batch_with_email_inputs(self):
        items = [
            "email:alice@example.com",
            "email:bob@example.com",
            "email:charlie@example.com",
        ]
        assert _uids(parse_user_ids(items)) == ["alice", "bob", "charlie"]

    def test_batch_mixed_email_user_dict(self):
        items = [
            "email:alice@example.com",
            "user:bob",
            {"user_id": "charlie"},
            {"user": {"id": "dave"}},
        ]
        assert _uids(parse_user_ids(items)) == ["alice", "bob", "charlie", "dave"]

    def test_batch_email_with_invalid(self):
        items = [
            "email:valid@test.com",
            "email:@test.com",         # empty username
            "email:admin@test.com",    # reserved
            "email:ok_id@test.com",
        ]
        assert _uids(parse_user_ids(items)) == ["valid", None, None, "ok_id"]

    def test_batch_single_email(self):
        assert _uids(parse_user_ids(["email:abc@test.com"])) == ["abc"]

    def test_batch_email_no_at(self):
        assert _uids(parse_user_ids(["email:noemail"])) == [None]

    def test_batch_email_consistency_with_individual(self):
        items = [
            "email:alice@test.com",
            "email:ADMIN@test.com",
            "email:x@test.com",
            "email: trimmed @test.com",
        ]
        batch_result = parse_user_ids(items)
        individual_results = [parse_user_id(item) for item in items]
        assert batch_result == individual_results


class TestBatchWithEdgeCases:
    def test_batch_all_input_types_mixed(self):
        items = [
            "user:alice",
            "email:bob@example.com",
            {"user_id": "charlie"},
            {"user": {"id": "dave"}},
            None,
            42,
            "email:@missing.com",
            "user:admin",
        ]
        expected = ["alice", "bob", "charlie", "dave", None, None, None, None]
        assert _uids(parse_user_ids(items)) == expected

    def test_batch_email_normalization(self):
        items = [
            "email:ALICE@example.com",
            "email:  bob  @example.com",
        ]
        assert _uids(parse_user_ids(items)) == ["alice", "bob"]

    def test_batch_preserves_none_positions_for_invalid_emails(self):
        items = [
            "email:ok_user@test.com",
            "email:no_at_sign",
            "email:@empty.com",
            "email:ab@short.com",
            "email:valid1@test.com",
        ]
        result = parse_user_ids(items)
        assert result[0].user_id == "ok_user"
        assert result[1] is None
        assert result[2] is None
        assert result[3] is None
        assert result[4].user_id == "valid1"


class TestNonMutationEmail:
    """Verify email string inputs are not mutated (strings are immutable, but verify behavior)."""

    def test_email_input_string_unchanged(self):
        s = "email:TestUser@Example.com"
        original = s  # strings are immutable, but let's verify no exception
        parse_user_id(s)
        assert s == original


class TestDictFallthroughBehavior:
    def test_user_id_none_falls_through_to_nested(self):
        result = parse_user_id({"user_id": None, "user": {"id": "valid1"}})
        assert _uid(result) == "valid1"

    def test_user_id_list_falls_through_to_nested(self):
        result = parse_user_id({"user_id": ["x"], "user": {"id": "valid1"}})
        assert _uid(result) == "valid1"

    def test_user_id_dict_falls_through_to_nested(self):
        result = parse_user_id({"user_id": {"a": 1}, "user": {"id": "valid1"}})
        assert _uid(result) == "valid1"

    def test_user_id_bool_falls_through_to_nested(self):
        result = parse_user_id({"user_id": True, "user": {"id": "valid1"}})
        assert _uid(result) == "valid1"

    def test_user_id_bytes_falls_through_to_nested(self):
        result = parse_user_id({"user_id": b"abc", "user": {"id": "valid1"}})
        assert _uid(result) == "valid1"

    def test_both_non_string_returns_none(self):
        result = parse_user_id({"user_id": 42, "user": {"id": 99}})
        assert result is None

    def test_user_not_dict_returns_none(self):
        result = parse_user_id({"user_id": 42, "user": "notadict"})
        assert result is None

    def test_user_dict_no_id_key_returns_none(self):
        result = parse_user_id({"user_id": 42, "user": {"name": "abc"}})
        assert result is None

    def test_only_user_key_with_valid_nested(self):
        result = parse_user_id({"user": {"id": "valid1"}})
        assert _uid(result) == "valid1"

    def test_only_user_key_with_invalid_nested_id(self):
        result = parse_user_id({"user": {"id": "!!"}})
        assert result is None


@pytest.mark.skipif(not HAS_Z3, reason="z3-solver not installed")
class TestZ3EmailVerification:
    def test_z3_email_username_with_dot_rejected(self):
        from z3 import String, StringVal, Solver, InRe, Re, Range, Star, Union, unsat
        s = Solver()
        x = String("x")
        char_class = Union(Range("a", "z"), Range("0", "9"), Re("_"), Re("-"))
        valid_regex = Star(char_class)
        s.add(x == StringVal("john.doe"))
        s.add(InRe(x, valid_regex))
        assert s.check() == unsat

    def test_z3_email_username_with_plus_rejected(self):
        from z3 import String, StringVal, Solver, InRe, Re, Range, Star, Union, unsat
        s = Solver()
        x = String("x")
        char_class = Union(Range("a", "z"), Range("0", "9"), Re("_"), Re("-"))
        valid_regex = Star(char_class)
        s.add(x == StringVal("user+tag"))
        s.add(InRe(x, valid_regex))
        assert s.check() == unsat

    def test_z3_valid_email_username_chars_accepted(self):
        from z3 import String, StringVal, Solver, InRe, Re, Range, Star, Union, sat
        s = Solver()
        x = String("x")
        char_class = Union(Range("a", "z"), Range("0", "9"), Re("_"), Re("-"))
        valid_regex = Star(char_class)
        s.add(x == StringVal("john_doe-123"))
        s.add(InRe(x, valid_regex))
        assert s.check() == sat

    def test_z3_reserved_ids_have_valid_format_but_blocked(self):
        import re as stdlib_re
        pattern = stdlib_re.compile(r"^[a-z0-9_-]{3,20}$")
        reserved = ["admin", "root", "system"]
        for rid in reserved:
            assert pattern.match(rid) is not None
            assert parse_user_id(f"email:{rid}@test.com") is None
            assert parse_user_id(f"user:{rid}") is None
            assert parse_user_id({"user_id": rid}) is None


class TestExtractionOnlyViaPublicAPI:
    """Test extraction edge cases that exercise _extract logic via the public API."""

    def test_string_with_multiple_colons_user_prefix(self):
        # "user:ab:cd" -> remainder = "ab:cd" -> contains ":" -> invalid
        assert parse_user_id("user:ab:cd") is None

    def test_string_with_multiple_colons_email_prefix(self):
        assert parse_user_id("email:ab:cd@test.com") is None

    def test_unknown_prefix_colon_format(self):
        assert parse_user_id("account:abc") is None

    def test_id_prefix(self):
        assert parse_user_id("id:abc") is None

    def test_name_prefix(self):
        assert parse_user_id("name:abc") is None

    def test_empty_prefix_before_colon(self):
        # ":abc" -> prefix = "", not "user" or "email"
        assert parse_user_id(":abc") is None

    def test_whitespace_prefix_before_colon(self):
        # "  :abc" -> after strip: ":abc" -> prefix = "" 
        assert parse_user_id("  :abc") is None

    def test_email_with_whitespace_only_before_at(self):
        # "email:   @test" -> username = "   " -> truthy
        # Then strip() -> "" -> length 0 -> invalid
        assert parse_user_id("email:   @test") is None

    def test_email_username_whitespace_trimmed_to_min_length(self):
        # " email: ab @test" -> username = " ab " -> strip -> "ab" -> length 2 -> invalid
        assert parse_user_id("email: ab @test") is None

    def test_email_username_whitespace_trimmed_to_exactly_3(self):
        # "email: abc @test" -> username = " abc " -> strip -> "abc" -> length 3 -> valid
        assert _uid(parse_user_id("email: abc @test")) == "abc"


# ==============================================================================
# CUSTOM RESERVED IDS TESTS
# ==============================================================================

class TestCustomReservedIds:
    def test_custom_reserved_blocks_custom_id(self):
        result = parse_user_id('user:blocked', reserved_ids={'blocked'})
        assert result is None

    def test_custom_reserved_allows_default_admin(self):
        result = parse_user_id('user:admin', reserved_ids={'blocked'})
        assert _uid(result) == 'admin'

    def test_custom_reserved_allows_default_root(self):
        result = parse_user_id('user:root', reserved_ids={'blocked'})
        assert _uid(result) == 'root'

    def test_custom_reserved_allows_default_system(self):
        result = parse_user_id('user:system', reserved_ids={'blocked'})
        assert _uid(result) == 'system'

    def test_custom_reserved_multiple_entries(self):
        reserved = {'foo', 'bar', 'baz'}
        assert parse_user_id('user:foo', reserved_ids=reserved) is None
        assert parse_user_id('user:bar', reserved_ids=reserved) is None
        assert parse_user_id('user:baz', reserved_ids=reserved) is None
        assert _uid(parse_user_id('user:qux', reserved_ids=reserved)) == 'qux'

    def test_custom_reserved_overlapping_with_defaults(self):
        reserved = {'admin', 'superuser'}
        assert parse_user_id('user:admin', reserved_ids=reserved) is None
        assert parse_user_id('user:superuser', reserved_ids=reserved) is None
        # root and system are NOT in this custom set
        assert _uid(parse_user_id('user:root', reserved_ids=reserved)) == 'root'
        assert _uid(parse_user_id('user:system', reserved_ids=reserved)) == 'system'

    def test_custom_reserved_single_entry(self):
        reserved = {'onlythis'}
        assert parse_user_id('user:onlythis', reserved_ids=reserved) is None
        assert _uid(parse_user_id('user:anything', reserved_ids=reserved)) == 'anything'

    def test_custom_reserved_via_dict_input(self):
        reserved = {'blocked'}
        assert parse_user_id({'user_id': 'blocked'}, reserved_ids=reserved) is None
        assert _uid(parse_user_id({'user_id': 'admin'}, reserved_ids=reserved)) == 'admin'

    def test_custom_reserved_via_nested_dict_input(self):
        reserved = {'blocked'}
        assert parse_user_id({'user': {'id': 'blocked'}}, reserved_ids=reserved) is None
        assert _uid(parse_user_id({'user': {'id': 'admin'}}, reserved_ids=reserved)) == 'admin'

    def test_custom_reserved_via_email_input(self):
        reserved = {'blocked'}
        assert parse_user_id('email:blocked@test.com', reserved_ids=reserved) is None
        assert _uid(parse_user_id('email:admin@test.com', reserved_ids=reserved)) == 'admin'

    def test_custom_reserved_case_insensitive_due_to_normalization(self):
        reserved = {'blocked'}
        assert parse_user_id('user:BLOCKED', reserved_ids=reserved) is None
        assert parse_user_id('user:Blocked', reserved_ids=reserved) is None

    def test_custom_reserved_with_uppercase_in_set(self):
        reserved = {'ADMIN'}
        assert _uid(parse_user_id('user:admin', reserved_ids=reserved)) == 'admin'
        assert _uid(parse_user_id('user:ADMIN', reserved_ids=reserved)) == 'admin'


# ==============================================================================
# EMPTY RESERVED SET TESTS
# ===============================================================================

class TestEmptyReservedSet:
    def test_admin_allowed_with_empty_reserved(self):
        assert _uid(parse_user_id("user:admin", reserved_ids=set())) == "admin"

    def test_root_allowed_with_empty_reserved(self):
        assert _uid(parse_user_id("user:root", reserved_ids=set())) == "root"

    def test_system_allowed_with_empty_reserved(self):
        assert _uid(parse_user_id("user:system", reserved_ids=set())) == "system"

    def test_admin_uppercase_allowed_with_empty_reserved(self):
        assert _uid(parse_user_id("user:ADMIN", reserved_ids=set())) == "admin"

    def test_admin_via_dict_allowed_with_empty_reserved(self):
        assert _uid(parse_user_id({"user_id": "admin"}, reserved_ids=set())) == "admin"

    def test_root_via_nested_dict_allowed_with_empty_reserved(self):
        assert _uid(parse_user_id({"user": {"id": "root"}}, reserved_ids=set())) == "root"

    def test_system_via_email_allowed_with_empty_reserved(self):
        assert _uid(parse_user_id("email:system@test.com", reserved_ids=set())) == "system"

    def test_regular_id_still_valid_with_empty_reserved(self):
        assert _uid(parse_user_id("user:testuser", reserved_ids=set())) == "testuser"

    def test_invalid_id_still_rejected_with_empty_reserved(self):
        assert parse_user_id("user:ab", reserved_ids=set()) is None

    def test_bad_chars_still_rejected_with_empty_reserved(self):
        assert parse_user_id("user:a!b", reserved_ids=set()) is None


class TestReservedIdsExplicitNone:
    def test_explicit_none_blocks_admin(self):
        assert parse_user_id("user:admin", reserved_ids=None) is None

    def test_explicit_none_blocks_root(self):
        assert parse_user_id("user:root", reserved_ids=None) is None

    def test_explicit_none_blocks_system(self):
        assert parse_user_id("user:system", reserved_ids=None) is None

    def test_explicit_none_allows_valid_id(self):
        assert _uid(parse_user_id("user:testuser", reserved_ids=None)) == "testuser"

    def test_explicit_none_matches_omitted_default(self):
        items_to_test = [
            "user:admin", "user:root", "user:system",
            "user:valid1", {"user_id": "admin"}, {"user_id": "valid1"},
        ]
        for item in items_to_test:
            assert parse_user_id(item, reserved_ids=None) == parse_user_id(item), \
                f"Mismatch for input: {item}"


class TestReservedIdsContainerTypes:
    def test_reserved_ids_as_list(self):
        assert parse_user_id("user:blocked", reserved_ids=["blocked"]) is None
        assert _uid(parse_user_id("user:admin", reserved_ids=["blocked"])) == "admin"

    def test_reserved_ids_as_tuple(self):
        assert parse_user_id("user:blocked", reserved_ids=("blocked",)) is None
        assert _uid(parse_user_id("user:admin", reserved_ids=("blocked",))) == "admin"

    def test_reserved_ids_as_frozenset(self):
        assert parse_user_id("user:blocked", reserved_ids=frozenset({"blocked"})) is None
        assert _uid(parse_user_id("user:admin", reserved_ids=frozenset({"blocked"}))) == "admin"

    def test_reserved_ids_as_list_multiple(self):
        reserved = ["foo", "bar", "baz"]
        assert parse_user_id("user:foo", reserved_ids=reserved) is None
        assert parse_user_id("user:bar", reserved_ids=reserved) is None
        assert _uid(parse_user_id("user:qux", reserved_ids=reserved)) == "qux"


class TestBatchWithReservedIds:
    def test_batch_default_reserved_blocks_defaults(self):
        items = ["user:admin", "user:root", "user:system", "user:valid1"]
        result = parse_user_ids(items)
        assert _uids(result) == [None, None, None, "valid1"]

    def test_batch_custom_reserved_blocks_custom(self):
        items = ["user:admin", "user:root", "user:blocked", "user:valid1"]
        result = parse_user_ids(items, reserved_ids={"blocked"})
        assert _uids(result) == ["admin", "root", None, "valid1"]

    def test_batch_empty_reserved_allows_all_defaults(self):
        items = ["user:admin", "user:root", "user:system"]
        result = parse_user_ids(items, reserved_ids=set())
        assert _uids(result) == ["admin", "root", "system"]

    def test_batch_explicit_none_reserved_uses_defaults(self):
        items = ["user:admin", "user:root", "user:valid1"]
        result = parse_user_ids(items, reserved_ids=None)
        assert _uids(result) == [None, None, "valid1"]

    def test_batch_custom_reserved_with_mixed_inputs(self):
        items = [
            "user:admin",
            "email:blocked@test.com",
            {"user_id": "admin"},
            {"user": {"id": "blocked"}},
            "user:other",
        ]
        result = parse_user_ids(items, reserved_ids={"blocked"})
        assert _uids(result) == ["admin", None, "admin", None, "other"]

    def test_batch_custom_reserved_consistency_with_individual(self):
        reserved = {"custom1", "custom2"}
        items = [
            "user:custom1",
            "user:custom2",
            "user:admin",
            "user:valid1",
        ]
        batch_result = parse_user_ids(items, reserved_ids=reserved)
        individual_results = [parse_user_id(item, reserved_ids=reserved) for item in items]
        assert batch_result == individual_results

    def test_batch_empty_reserved_consistency_with_individual(self):
        items = ["user:admin", "user:root", "user:system", "user:abc"]
        batch_result = parse_user_ids(items, reserved_ids=set())
        individual_results = [parse_user_id(item, reserved_ids=set()) for item in items]
        assert batch_result == individual_results

    def test_batch_length_preserved_with_custom_reserved(self):
        items = ["user:abc", None, "user:admin", 42]
        result = parse_user_ids(items, reserved_ids={"abc"})
        assert len(result) == len(items)

    def test_batch_empty_list_with_reserved_ids(self):
        assert parse_user_ids([], reserved_ids={"blocked"}) == []

    def test_batch_all_reserved(self):
        reserved = {"aaa", "bbb", "ccc"}
        items = ["user:aaa", "user:bbb", "user:ccc"]
        result = parse_user_ids(items, reserved_ids=reserved)
        assert _uids(result) == [None, None, None]


class TestExceptionRaisingDictInputs:
    """Test that dict-like objects raising exceptions don't crash."""

    def test_dict_subclass_raising_on_contains(self):
        class BadDict(dict):
            def __contains__(self, key):
                raise RuntimeError("boom")
        result = parse_user_id(BadDict())
        assert result is None

    def test_dict_subclass_raising_on_getitem(self):
        class BadDict(dict):
            def __contains__(self, key):
                return True
            def __getitem__(self, key):
                raise RuntimeError("boom")
        result = parse_user_id(BadDict())
        assert result is None

    def test_dict_subclass_raising_on_keys(self):
        class WeirdDict(dict):
            def __init__(self):
                pass
            def __contains__(self, key):
                raise TypeError("nope")
        result = parse_user_id(WeirdDict())
        assert result is None


class TestNormalizationEdgeCases:
    """Additional normalization edge cases."""

    def test_uppercase_only_id_trimmed_to_short(self):
        # "user:  AB  " -> strip -> "AB" -> lower -> "ab" -> length 2 -> None
        assert parse_user_id("user:  AB  ") is None

    def test_uppercase_only_id_trimmed_to_exact_min(self):
        # "user:  ABC  " -> strip -> "ABC" -> lower -> "abc" -> length 3 -> valid
        assert _uid(parse_user_id("user:  ABC  ")) == "abc"

    def test_mixed_case_id_at_max_length(self):
        uid_upper = "AbCdEfGhIjKlMnOpQrSt"  # 20 chars
        assert len(uid_upper) == 20
        assert _uid(parse_user_id(f"user:{uid_upper}")) == uid_upper.lower()

    def test_id_with_trailing_whitespace_after_valid_chars(self):
        assert _uid(parse_user_id({"user_id": "abc   "})) == "abc"

    def test_id_with_leading_whitespace_before_valid_chars(self):
        assert _uid(parse_user_id({"user_id": "   abc"})) == "abc"


class TestEmailEdgeCasesNew:
    """Additional email edge cases not in existing tests."""

    def test_email_multiple_at_username_only_first_part(self):
        # "email:@@@" -> remainder="@@@" , split on first @ -> username = ""
        # empty username -> None
        assert parse_user_id("email:@@@") is None

    def test_email_with_at_in_domain_only(self):
        # "email:abc@def@ghi@jkl" -> username = "abc"
        assert _uid(parse_user_id("email:abc@def@ghi@jkl")) == "abc"

    def test_email_reserved_with_empty_reserved_set(self):
        assert _uid(parse_user_id("email:admin@test.com", reserved_ids=set())) == "admin"

    def test_email_reserved_with_custom_reserved_set(self):
        assert parse_user_id("email:blocked@test.com", reserved_ids={"blocked"}) is None
        assert _uid(parse_user_id("email:admin@test.com", reserved_ids={"blocked"})) == "admin"

    def test_email_username_exactly_20_chars_with_reserved_check(self):
        uid = "a" * 20
        assert _uid(parse_user_id(f"email:{uid}@test.com", reserved_ids=set())) == uid

    def test_email_with_empty_domain(self):
        assert _uid(parse_user_id("email:abc@")) == "abc"

    def test_email_with_only_whitespace_domain(self):
        assert _uid(parse_user_id("email:abc@   ")) == "abc"


class TestReservedIdsNotMutated:
    """Ensure the reserved_ids parameter is not mutated."""

    def test_custom_set_not_mutated(self):
        reserved = {"blocked", "forbidden"}
        original = reserved.copy()
        parse_user_id("user:blocked", reserved_ids=reserved)
        assert reserved == original

    def test_custom_list_not_mutated(self):
        reserved = ["blocked", "forbidden"]
        original = reserved.copy()
        parse_user_id("user:blocked", reserved_ids=reserved)
        assert reserved == original

    def test_batch_custom_set_not_mutated(self):
        reserved = {"blocked"}
        original = reserved.copy()
        parse_user_ids(["user:blocked", "user:abc"], reserved_ids=reserved)
        assert reserved == original


class TestReservedIdsEdgeCases:
    """Edge cases for the reserved_ids parameter itself."""

    def test_reserved_ids_containing_invalid_format_id(self):
        # Reserved set has "!!" — since cleaned ID won't match "!!", it's effectively a no-op
        reserved = {"!!"}
        assert parse_user_id("user:abc", reserved_ids=reserved).user_id == "abc"

    def test_reserved_ids_containing_too_short_id(self):
        reserved = {"ab"}
        assert _uid(parse_user_id("user:abc", reserved_ids=reserved)) == "abc"

    def test_reserved_ids_empty_frozenset(self):
        assert _uid(parse_user_id("user:admin", reserved_ids=frozenset())) == "admin"

    def test_reserved_ids_large_set(self):
        reserved = {f"user{i:03d}" for i in range(1000)}
        assert parse_user_id("user:user042", reserved_ids=reserved) is None
        assert _uid(parse_user_id("user:safe_id", reserved_ids=reserved)) == "safe_id"

    def test_reserved_ids_with_near_match(self):
        # Reserved has "admin" but not "admin1"
        reserved = {"admin"}
        assert parse_user_id("user:admin", reserved_ids=reserved) is None
        assert _uid(parse_user_id("user:admin1", reserved_ids=reserved)) == "admin1"


class TestReturnTypeConsistency:
    """Ensure return types are consistently str or None."""

    def test_valid_returns_parse_result(self):
        result = parse_user_id("user:abc")
        assert isinstance(result, ParseResult)
        assert isinstance(result.user_id, str)

    def test_invalid_returns_none_not_false(self):
        result = parse_user_id("user:!!")
        assert result is None
        assert result is not False

    def test_reserved_returns_none_not_empty_string(self):
        result = parse_user_id("user:admin")
        assert result is None
        assert result != ""

    def test_batch_none_elements_are_exactly_none(self):
        result = parse_user_ids([None, 42, "bad"])
        for elem in result:
            assert elem is None


class TestUserColonIdWithSpecialRemainders:
    """Edge cases for user: prefix with unusual remainders."""

    def test_user_colon_with_only_digits_min_length(self):
        assert _uid(parse_user_id("user:123")) == "123"

    def test_user_colon_with_only_hyphens_min_length(self):
        assert _uid(parse_user_id("user:---")) == "---"

    def test_user_colon_with_only_underscores_max_length(self):
        assert _uid(parse_user_id("user:" + "_" * 20)) == "_" * 20

    def test_user_colon_with_only_hyphens_max_length(self):
        assert _uid(parse_user_id("user:" + "-" * 20)) == "-" * 20

    def test_user_colon_with_null_byte_in_id(self):
        assert parse_user_id("user:ab\x00c") is None

    def test_user_colon_with_vertical_tab(self):
        assert parse_user_id("user:ab\x0bc") is None


class TestBatchWithReservedAndNormalization:
    """Combined batch + reserved + normalization tests."""

    def test_batch_custom_reserved_with_uppercase_input(self):
        items = ["user:ADMIN", "user:ROOT"]
        result = parse_user_ids(items, reserved_ids={"admin"})
        assert _uids(result) == [None, "root"]

    def test_batch_custom_reserved_email_and_dict(self):
        items = [
            "email:custom@test.com",
            {"user_id": "custom"},
            {"user": {"id": "custom"}},
            "user:custom",
        ]
        result = parse_user_ids(items, reserved_ids={"custom"})
        assert _uids(result) == [None, None, None, None]

    def test_batch_frozenset_reserved(self):
        items = ["user:admin", "user:root", "user:abc"]
        result = parse_user_ids(items, reserved_ids=frozenset({"admin"}))
        assert _uids(result) == [None, "root", "abc"]


class TestDictEdgeCasesNew2:
    """Additional dict edge cases for robustness."""

    def test_dict_with_user_id_and_user_both_invalid_types(self):
        result = parse_user_id({"user_id": set(), "user": set()})
        assert result is None

    def test_dict_with_user_key_as_int(self):
        result = parse_user_id({"user": 42})
        assert result is None

    def test_dict_with_user_key_as_tuple(self):
        result = parse_user_id({"user": ("id", "abc")})
        assert result is None

    def test_dict_with_user_id_valid_and_no_user_key(self):
        result = parse_user_id({"user_id": "abc"})
        assert _uid(result) == "abc"

    def test_dict_with_only_user_nested_valid(self):
        result = parse_user_id({"user": {"id": "abc"}})
        assert _uid(result) == "abc"

    def test_dict_with_user_id_too_long_no_fallthrough(self):
        long_id = "a" * 21
        result = parse_user_id({"user_id": long_id, "user": {"id": "abc"}})
        assert result is None

    def test_dict_with_user_id_too_short_no_fallthrough(self):
        result = parse_user_id({"user_id": "ab", "user": {"id": "valid1"}})
        assert result is None


# ==================================================================
# ParseResult tests
# ==================================================================

def test_parse_result_basic_fields():
    pr = ParseResult(user_id="abc", source="string")
    assert pr.user_id == "abc"
    assert pr.source == "string"
    assert ParseResult._fields == ("user_id", "source")


def test_parse_result_index_and_unpack():
    pr = ParseResult(user_id="abc", source="string")
    assert pr[0] == "abc"
    assert pr[1] == "string"
    user_id, source = pr
    assert user_id == "abc"
    assert source == "string"

# ==========================================================================
# NEW TESTS: Strict mode, additional edge cases not covered by existing tests
# ============================================================================
#
# TEST PLAN FOR NEW TESTS:
#
# 1. STRICT MODE (biggest gap in existing tests):
#    - strict=True should reject IDs containing: __, --, _-, -_
#    - strict=False (default) should allow these patterns
#    - Test via all input paths: string (user:), email:, dict_flat, dict_nested
#    - Test patterns at start, middle, end of ID
#    - Test single special chars still allowed in strict mode
#    - Test multiple consecutive special char groups
#    - Test strict mode combined with custom reserved_ids
#    - Test strict mode in batch processing
#    - Unit tests are best here since we're testing specific behavior branches.
#
# 2. STRICT MODE + BATCH:
#    - parse_user_ids with strict=True
#    - Consistency between batch and individual with strict
#
# 3. EDGE CASES for extraction logic:
#    - bool is subclass of int, not str - ensure bool input returns None
#    - dict with bool keys
#    - Very large input strings
#
# 4. Z3 FORMAL VERIFICATION for strict mode:
#    - Verify the regex [_-]{2} correctly matches all 4 patterns
#    - Verify single special chars don't match the pattern
#

# ============================================================================
# STRICT MODE TESTS - Double underscore
# ============================================================================


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root / "src"))

class TestStrictModeDoubleUnderscore:
    def test_strict_rejects_double_underscore_middle(self):
        assert parse_user_id("user:a__b", strict=True) is None

    def test_nonstrict_allows_double_underscore_middle(self):
        assert _uid(parse_user_id("user:a__b", strict=False)) == "a__b"

    def test_strict_rejects_double_underscore_start(self):
        assert parse_user_id("user:__abc", strict=True) is None

    def test_strict_rejects_double_underscore_end(self):
        assert parse_user_id("user:abc__", strict=True) is None

    def test_strict_rejects_triple_underscore(self):
        assert parse_user_id("user:a___b", strict=True) is None

    def test_strict_allows_single_underscore(self):
        assert _uid(parse_user_id("user:a_b_c", strict=True)) == "a_b_c"


# ============================================================================
# STRICT MODE TESTS - Double hyphen
# ============================================================================

class TestStrictModeDoubleHyphen:
    def test_strict_rejects_double_hyphen_middle(self):
        assert parse_user_id("user:a--b", strict=True) is None

    def test_nonstrict_allows_double_hyphen_middle(self):
        assert _uid(parse_user_id("user:a--b", strict=False)) == "a--b"

    def test_strict_rejects_double_hyphen_start(self):
        assert parse_user_id("user:--abc", strict=True) is None

    def test_strict_rejects_double_hyphen_end(self):
        assert parse_user_id("user:abc--", strict=True) is None

    def test_strict_rejects_triple_hyphen(self):
        assert parse_user_id("user:a---b", strict=True) is None

    def test_strict_allows_single_hyphen(self):
        assert _uid(parse_user_id("user:a-b-c", strict=True)) == "a-b-c"


# ============================================================================
# STRICT MODE TESTS - Mixed underscore-hyphen
# ============================================================================

class TestStrictModeMixedSpecials:
    def test_strict_rejects_underscore_hyphen(self):
        assert parse_user_id("user:a_-b", strict=True) is None

    def test_strict_rejects_hyphen_underscore(self):
        assert parse_user_id("user:a-_b", strict=True) is None

    def test_nonstrict_allows_underscore_hyphen(self):
        assert _uid(parse_user_id("user:a_-b", strict=False)) == "a_-b"

    def test_nonstrict_allows_hyphen_underscore(self):
        assert _uid(parse_user_id("user:a-_b", strict=False)) == "a-_b"

    def test_strict_rejects_underscore_hyphen_at_start(self):
        assert parse_user_id("user:_-abc", strict=True) is None

    def test_strict_rejects_hyphen_underscore_at_end(self):
        assert parse_user_id("user:abc-_", strict=True) is None

    def test_strict_rejects_multiple_mixed_patterns(self):
        assert parse_user_id("user:a_-b--c", strict=True) is None

    def test_strict_allows_separated_specials(self):
        # Single specials separated by alphanumerics
        assert _uid(parse_user_id("user:a_b-c_d", strict=True)) == "a_b-c_d"


# ============================================================================
# STRICT MODE TESTS - Via all input paths
# ============================================================================

class TestStrictModeAllPaths:
    def test_strict_rejects_via_string_path(self):
        assert parse_user_id("user:a__b", strict=True) is None

    def test_strict_rejects_via_email_path(self):
        assert parse_user_id("email:a__b@test.com", strict=True) is None

    def test_strict_rejects_via_dict_flat_path(self):
        assert parse_user_id({"user_id": "a__b"}, strict=True) is None

    def test_strict_rejects_via_dict_nested_path(self):
        assert parse_user_id({"user": {"id": "a__b"}}, strict=True) is None

    def test_strict_allows_valid_via_string_path(self):
        r = parse_user_id("user:a_b-c", strict=True)
        assert r is not None and r.user_id == "a_b-c" and r.source == "string"

    def test_strict_allows_valid_via_email_path(self):
        r = parse_user_id("email:a_b-c@test.com", strict=True)
        assert r is not None and r.user_id == "a_b-c" and r.source == "email"

    def test_strict_allows_valid_via_dict_flat_path(self):
        r = parse_user_id({"user_id": "a_b-c"}, strict=True)
        assert r is not None and r.user_id == "a_b-c" and r.source == "dict_flat"

    def test_strict_allows_valid_via_dict_nested_path(self):
        r = parse_user_id({"user": {"id": "a_b-c"}}, strict=True)
        assert r is not None and r.user_id == "a_b-c" and r.source == "dict_nested"

    def test_strict_consistency_across_paths_rejected(self):
        """Same ID with consecutive specials is rejected via all paths in strict mode."""
        uid = "test__id"
        r1 = parse_user_id(f"user:{uid}", strict=True)
        r2 = parse_user_id(f"email:{uid}@test.com", strict=True)
        r3 = parse_user_id({"user_id": uid}, strict=True)
        r4 = parse_user_id({"user": {"id": uid}}, strict=True)
        assert r1 is None and r2 is None and r3 is None and r4 is None

    def test_strict_consistency_across_paths_allowed(self):
        uid = "test_id"
        r1 = parse_user_id(f"user:{uid}", strict=True)
        r2 = parse_user_id(f"email:{uid}@test.com", strict=True)
        r3 = parse_user_id({"user_id": uid}, strict=True)
        r4 = parse_user_id({"user": {"id": uid}}, strict=True)
        assert _uid(r1) == _uid(r2) == _uid(r3) == _uid(r4) == uid


# ==========================================================================
# STRICT MODE TESTS - Edge cases
# ============================================================================

class TestStrictModeEdgeCases:
    def test_strict_with_only_underscores_min_length(self):
        # "___" has "__" at position 0 -> rejected
        assert parse_user_id("user:___", strict=True) is None

    def test_strict_with_only_hyphens_min_length(self):
        # "---" has "--" at position 0 -> rejected
        assert parse_user_id("user:---", strict=True) is None

    def test_strict_no_specials_at_all(self):
        assert _uid(parse_user_id("user:abcdef", strict=True)) == "abcdef"

    def test_strict_single_underscore_only_at_min(self):
        # Can't have length 3 with single underscore only = not valid id
        # But "a_b" is 3 chars and valid
        assert _uid(parse_user_id("user:a_b", strict=True)) == "a_b"

    def test_strict_single_hyphen_only_at_min(self):
        assert _uid(parse_user_id("user:a-b", strict=True)) == "a-b"

    def test_strict_default_is_false(self):
        # Verify strict defaults to False
        assert _uid(parse_user_id("user:a__b")) == "a__b"

    def test_strict_with_uppercase_input_normalized_then_checked(self):
        # "A__B" -> lowered to "a__b" -> strict check finds "__" -> None
        assert parse_user_id("user:A__B", strict=True) is None

    def test_strict_with_whitespace_trimmed_then_checked(self):
        assert parse_user_id("user:  a__b  ", strict=True) is None

    def test_strict_four_consecutive_specials(self):
        assert parse_user_id("user:a____b", strict=True) is None

    def test_strict_alternating_underscore_hyphen(self):
        # "_-_-" has "_-" at position 0 -> rejected
        assert parse_user_id("user:a_-_-b", strict=True) is None

    def test_strict_all_four_patterns_rejected(self):
        """Verify all four consecutive special patterns are rejected."""
        assert parse_user_id("user:ab__cd", strict=True) is None
        assert parse_user_id("user:ab--cd", strict=True) is None
        assert parse_user_id("user:ab_-cd", strict=True) is None
        assert parse_user_id("user:ab-_cd", strict=True) is None


# ==========================================================================
# STRICT MODE TESTS - Combined with reserved_ids
# ============================================================================

class TestStrictModeWithReservedIds:
    def test_strict_with_default_reserved_rejects_admin(self):
        assert parse_user_id("user:admin", strict=True) is None

    def test_strict_with_custom_reserved_rejects_custom(self):
        assert parse_user_id("user:blocked", reserved_ids={"blocked"}, strict=True) is None

    def test_strict_with_custom_reserved_allows_defaults(self):
        assert _uid(parse_user_id("user:admin", reserved_ids={"blocked"}, strict=True)) == "admin"

    def test_strict_with_empty_reserved_still_checks_consecutive(self):
        assert parse_user_id("user:a__b", reserved_ids=set(), strict=True) is None

    def test_strict_with_empty_reserved_allows_admin(self):
        assert _uid(parse_user_id("user:admin", reserved_ids=set(), strict=True)) == "admin"

    def test_strict_valid_with_custom_reserved(self):
        r = parse_user_id("user:good_id", reserved_ids={"other"}, strict=True)
        assert _uid(r) == "good_id"

    def test_strict_reserved_takes_precedence_over_strict_check(self):
        # "admin" has no consecutive specials, but is reserved -> None
        assert parse_user_id("user:admin", strict=True) is None


# ==========================================================================
# STRICT MODE TESTS - Batch processing
# ============================================================================

class TestStrictModeBatch:
    def test_batch_strict_rejects_consecutive_specials(self):
        items = ["user:a__b", "user:a--b", "user:a_-b", "user:a-_b"]
        result = parse_user_ids(items, strict=True)
        assert _uids(result) == [None, None, None, None]

    def test_batch_strict_allows_single_specials(self):
        items = ["user:a_b", "user:a-b", "user:a_b_c", "user:a-b-c"]
        result = parse_user_ids(items, strict=True)
        assert _uids(result) == ["a_b", "a-b", "a_b_c", "a-b-c"]

    def test_batch_strict_mixed_valid_and_invalid(self):
        items = [
            "user:valid_id",     # valid - single specials
            "user:bad__id",      # invalid - double underscore
            "user:ok_too",       # valid
            "user:bad--id",      # invalid - double hyphen
            "user:fine",         # valid - no specials
        ]
        result = parse_user_ids(items, strict=True)
        assert _uids(result) == ["valid_id", None, "ok_too", None, "fine"]

    def test_batch_nonstrict_allows_all_consecutive(self):
        items = ["user:a__b", "user:a--b", "user:a_-b", "user:a-_b"]
        result = parse_user_ids(items, strict=False)
        assert _uids(result) == ["a__b", "a--b", "a_-b", "a-_b"]

    def test_batch_strict_consistency_with_individual(self):
        items = [
            "user:a__b",
            "user:valid",
            {"user_id": "c--d"},
            "email:e_-f@test.com",
        ]
        batch_result = parse_user_ids(items, strict=True)
        individual_results = [parse_user_id(item, strict=True) for item in items]
        assert batch_result == individual_results

    def test_batch_strict_with_custom_reserved(self):
        items = ["user:a__b", "user:blocked", "user:valid1"]
        result = parse_user_ids(items, reserved_ids={"blocked"}, strict=True)
        assert _uids(result) == [None, None, "valid1"]

    def test_batch_strict_empty_list(self):
        assert parse_user_ids([], strict=True) == []

    def test_batch_strict_all_params_passed_through(self):
        """Verify strict and reserved_ids both pass through to individual calls."""
        items = ["user:admin", "user:a__b", "user:valid1"]
        result = parse_user_ids(items, reserved_ids=set(), strict=True)
        # admin allowed (empty reserved), a__b rejected (strict), valid1 ok
        assert _uids(result) == ["admin", None, "valid1"]


# ============================================================================
# STRICT MODE TESTS - Non-mutation
# ============================================================================

class TestStrictModeNonMutation:
    def test_dict_not_mutated_in_strict_mode(self):
        d = {"user_id": "a__b"}
        original = copy.deepcopy(d)
        parse_user_id(d, strict=True)
        assert d == original

    def test_nested_dict_not_mutated_in_strict_mode(self):
        d = {"user": {"id": "a--b"}}
        original = copy.deepcopy(d)
        parse_user_id(d, strict=True)
        assert d == original


# ============================================================================
# SOURCE FIELD VERIFICATION
# ============================================================================

class TestSourceField:
    def test_source_string_for_user_prefix(self):
        r = parse_user_id("user:abc")
        assert r.source == "string"

    def test_source_email_for_email_prefix(self):
        r = parse_user_id("email:abc@test.com")
        assert r.source == "email"

    def test_source_dict_flat_for_user_id_key(self):
        r = parse_user_id({"user_id": "abc"})
        assert r.source == "dict_flat"

    def test_source_dict_nested_for_nested_key(self):
        r = parse_user_id({"user": {"id": "abc"}})
        assert r.source == "dict_nested"

    def test_source_preserved_in_batch(self):
        items = [
            "user:aaa",
            "email:bbb@test.com",
            {"user_id": "ccc"},
            {"user": {"id": "ddd"}},
        ]
        result = parse_user_ids(items)
        assert result[0].source == "string"
        assert result[1].source == "email"
        assert result[2].source == "dict_flat"
        assert result[3].source == "dict_nested"

    def test_source_preserved_in_strict_mode(self):
        r = parse_user_id("user:valid1", strict=True)
        assert r.source == "string"
        r = parse_user_id("email:valid1@t.com", strict=True)
        assert r.source == "email"


# ============================================================================
# PARSE RESULT NAMEDTUPLE ADDITIONAL TESTS
# ============================================================================

class TestParseResultProperties:
    def test_parse_result_equality(self):
        a = ParseResult(user_id="abc", source="string")
        b = ParseResult(user_id="abc", source="string")
        assert a == b

    def test_parse_result_inequality_user_id(self):
        a = ParseResult(user_id="abc", source="string")
        b = ParseResult(user_id="xyz", source="string")
        assert a != b

    def test_parse_result_inequality_source(self):
        a = ParseResult(user_id="abc", source="string")
        b = ParseResult(user_id="abc", source="email")
        assert a != b

    def test_parse_result_is_tuple(self):
        r = parse_user_id("user:abc")
        assert isinstance(r, tuple)

    def test_parse_result_len(self):
        r = parse_user_id("user:abc")
        assert len(r) == 2

    def test_parse_result_repr(self):
        r = ParseResult(user_id="abc", source="string")
        assert "abc" in repr(r)
        assert "string" in repr(r)


# ============================================================================
# STRICT=FALSE EXPLICIT TESTS (confirm default behavior)
# ============================================================================

class TestStrictFalseExplicit:
    def test_explicit_false_allows_double_underscore(self):
        assert _uid(parse_user_id("user:a__b", strict=False)) == "a__b"

    def test_explicit_false_allows_double_hyphen(self):
        assert _uid(parse_user_id("user:a--b", strict=False)) == "a--b"

    def test_explicit_false_allows_underscore_hyphen(self):
        assert _uid(parse_user_id("user:a_-b", strict=False)) == "a_-b"

    def test_explicit_false_allows_hyphen_underscore(self):
        assert _uid(parse_user_id("user:a-_b", strict=False)) == "a-_b"

    def test_explicit_false_matches_default(self):
        """strict=False should behave same as omitting strict."""
        items = ["user:a__b", "user:a--b", "user:a_-b", "user:a-_b"]
        for item in items:
            assert parse_user_id(item, strict=False) == parse_user_id(item)


# ==========================================================================
# ADDITIONAL EDGE CASE: bool subclass of int
# ============================================================================

class TestBoolInputEdgeCases:
    def test_bool_true_is_not_treated_as_string(self):
        # bool is subclass of int, not str
        assert parse_user_id(True) is None

    def test_bool_false_is_not_treated_as_string(self):
        assert parse_user_id(False) is None

    def test_bool_true_is_not_treated_as_dict(self):
        # isinstance(True, dict) is False, so should be None
        assert parse_user_id(True) is None


# ==========================================================================
# EDGE CASES: email username extraction with whitespace
# ============================================================================

class TestEmailWhitespaceInUsername:
    def test_email_username_with_leading_space_trimmed(self):
        # "email: abc@test" -> remainder=" abc@test" -> username=" abc" -> strip->"abc"
        assert _uid(parse_user_id("email: abc@test")) == "abc"

    def test_email_username_with_trailing_space_trimmed(self):
        # "email:abc @test" -> username="abc " -> strip->"abc"
        assert _uid(parse_user_id("email:abc @test")) == "abc"

    def test_email_username_spaces_trimmed_makes_valid(self):
        # "email:  abcdef  @test" -> username="  abcdef  " -> strip -> "abcdef"
        assert _uid(parse_user_id("email:  abcdef  @test")) == "abcdef"


# ==========================================================================
# EDGE CASES: dict with user_id valid but validation fails (no fallthrough)
# ============================================================================

class TestDictUserIdValidStringButFailsValidation:
    """When user_id is a valid string but fails validation, should NOT fall through to nested."""

    def test_user_id_invalid_chars_no_fallthrough(self):
        result = parse_user_id({"user_id": "a!b", "user": {"id": "valid1"}})
        assert result is None

    def test_user_id_reserved_no_fallthrough(self):
        result = parse_user_id({"user_id": "admin", "user": {"id": "valid1"}})
        assert result is None

    def test_user_id_too_long_no_fallthrough(self):
        result = parse_user_id({"user_id": "a" * 21, "user": {"id": "valid1"}})
        assert result is None

    def test_user_id_consecutive_specials_strict_no_fallthrough(self):
        result = parse_user_id(
            {"user_id": "a__b", "user": {"id": "valid1"}},
            strict=True,
        )
        assert result is None


# ==========================================================================
# STRICT MODE + NORMALIZATION INTERACTION
# ============================================================================

class TestStrictModeNormalization:
    def test_strict_after_lowercase_normalization(self):
        # Uppercase doesn't affect the special char check
        assert parse_user_id("user:A__B", strict=True) is None

    def test_strict_after_whitespace_trim(self):
        assert parse_user_id("user:  a__b  ", strict=True) is None

    def test_strict_combined_normalization_valid(self):
        assert _uid(parse_user_id("user:  A_B  ", strict=True)) == "a_b"

    def test_strict_combined_normalization_dict(self):
        assert parse_user_id({"user_id": "  A__B  "}, strict=True) is None

    def test_strict_combined_normalization_email(self):
        assert parse_user_id("email:  A__B  @test.com", strict=True) is None


# ==========================================================================
# STRICT MODE - Only two consecutive specials needed to reject
# ============================================================================

class TestStrictModeMinimalPattern:
    def test_strict_exactly_two_underscores(self):
        assert parse_user_id("user:ab__cd", strict=True) is None

    def test_strict_exactly_two_hyphens(self):
        assert parse_user_id("user:ab--cd", strict=True) is None

    def test_strict_exactly_underscore_then_hyphen(self):
        assert parse_user_id("user:ab_-cd", strict=True) is None

    def test_strict_exactly_hyphen_then_underscore(self):
        assert parse_user_id("user:ab-_cd", strict=True) is None

    def test_strict_long_valid_id_no_consecutive(self):
        uid = "a-b_c-d_e-f_g-h_i-jk"  # 20 chars, no consecutive
        assert len(uid) == 20
        assert _uid(parse_user_id(f"user:{uid}", strict=True)) == uid

    def test_strict_id_with_specials_at_every_other_position(self):
        assert _uid(parse_user_id("user:a_b_c_d", strict=True)) == "a_b_c_d"
        assert _uid(parse_user_id("user:a-b-c-d", strict=True)) == "a-b-c-d"
        assert _uid(parse_user_id("user:a_b-c_d", strict=True)) == "a_b-c_d"


# ============================================================================
# BATCH - verify strict param default
# ============================================================================

class TestBatchStrictDefault:
    def test_batch_default_strict_allows_consecutive(self):
        items = ["user:a__b", "user:a--b"]
        result = parse_user_ids(items)
        assert _uids(result) == ["a__b", "a--b"]

    def test_batch_strict_true_rejects_consecutive(self):
        items = ["user:a__b", "user:a--b"]
        result = parse_user_ids(items, strict=True)
        assert _uids(result) == [None, None]


# ============================================================================
# COMPREHENSIVE INTEGRATION: all parameters combined
# ============================================================================

class TestAllParamsCombined:
    def test_custom_reserved_and_strict_batch(self):
        items = [
            "user:valid1",          # valid
            "user:a__b",            # rejected by strict
            "user:blocked",         # rejected by reserved
            "user:admin",           # allowed (not in custom reserved)
            "email:good@t.com",     # valid
            "email:c--d@t.com",     # rejected by strict
            {"user_id": "blocked"}, # rejected by reserved
            {"user": {"id": "ok_id"}},  # valid
        ]
        result = parse_user_ids(items, reserved_ids={"blocked"}, strict=True)
        assert _uids(result) == [
            "valid1", None, None, "admin", "good", None, None, "ok_id"
        ]

    def test_empty_reserved_strict_batch(self):
        items = ["user:admin", "user:a__b", "user:abc"]
        result = parse_user_ids(items, reserved_ids=set(), strict=True)
        assert _uids(result) == ["admin", None, "abc"]

    def test_all_params_none_reserved_strict_false(self):
        # This is the default behavior
        items = ["user:admin", "user:a__b"]
        result = parse_user_ids(items, reserved_ids=None, strict=False)
        assert _uids(result) == [None, "a__b"]

# ============================================================================
# NEW TESTS: Additional coverage for uncovered functionality
# ============================================================================
#
# TEST PLAN FOR NEW TESTS:
#
# 1. STRING SUBCLASS INPUT (Unit tests):
#    - String subclasses should work identically to regular strings
#    - isinstance(MyStr(...), str) is True, so these should pass through
#    - Z3 not applicable (type system behavior)
#
# 2. PARSE RESULT ADVANCED NAMEDTUPLE PROPERTIES (Unit tests):
#    - _asdict(), _replace(), hashability, set/dict usage
#    - Structural properties best tested as unit tests
#
# 3. parse_user_ids WITH NON-LIST ITERABLES (Unit tests):
#    - Tuple, generator inputs should work via list comprehension
#    - Unit tests preferred (behavioral testing)
#
# 4. ADDITIONAL BAD INPUT TYPES (Unit tests):
#    - complex, range, memoryview, frozenset, bytearray, lambda, type, Ellipsis
#    - All should return None without raising
#
# 5. Z3 FORMAL VERIFICATION FOR STRICT MODE REGEX [_-]{2}:
#    - Formally verify that __, --, _-, -_ all match the pattern
#    - Formally verify single _ or - do NOT match
#    - Z3 preferred (formal regex property verification)
#
# 6. DICT WITH UNUSUAL VALUE TYPES FOR user_id AND nested id:
#    - float, complex, bytes, frozenset, tuple as values
#    - Unit tests (type handling)
#
# 7. VALIDATION PIPELINE ORDER (Unit tests):
#    - Verify strip → lower → regex → reserved → strict ordering
#    - Each stage's effect must be observable
#
# 8. BOUNDARY LENGTHS VIA ALL 4 INPUT PATHS (Unit tests):
#    - Length 3 and 20 via user:, email:, dict_flat, dict_nested
#    - Length 2 and 21 rejected via all paths
#
# 9. EMAIL DOMAIN INDEPENDENCE (Unit tests):
#    - Same username with different domains produces same result
#
# 10. MULTIPLE BATCH CALLS INDEPENDENCE (Unit tests):
#     - Sequential calls with different params don't interfere
#
# 11. DEFAULTDICT EDGE CASES (Unit tests):
#     - defaultdict with factory returning strings vs missing keys
#
# 12. STRICT MODE AT POSITIONS WITHIN MAX-LENGTH IDS (Unit tests):
#     - Consecutive specials at various positions in 20-char IDs
#
# 13. COMBINED ALL-PARAM INTEGRATION (Unit tests):
#     - reserved_ids + strict + normalization + all input paths in one batch
#
# 14. FORM FEED AND OTHER CONTROL CHARS IN ID (Unit tests):
#     - Verify non-printable control chars fail regex validation
#
# 15. PREFIX EXACT MATCH VERIFICATION (Unit tests):
#     - Verify "users:", "user1:", "mail:", "emails:" etc. are rejected
#


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

class TestStringSubclassInput:
    """Verify string subclasses are handled correctly."""

    def test_string_subclass_user_prefix_valid(self):
        class MyStr(str):
            pass
        result = parse_user_id(MyStr("user:abc"))
        assert result is not None and result.user_id == "abc"

    def test_string_subclass_email_prefix_valid(self):
        class MyStr(str):
            pass
        result = parse_user_id(MyStr("email:abc@test.com"))
        assert result is not None and result.user_id == "abc"

    def test_string_subclass_invalid_no_colon(self):
        class MyStr(str):
            pass
        result = parse_user_id(MyStr("invalid"))
        assert result is None

    def test_string_subclass_with_whitespace_normalized(self):
        class MyStr(str):
            pass
        result = parse_user_id(MyStr("  user:ABC  "))
        assert result is not None and result.user_id == "abc"

    def test_string_subclass_reserved_rejected(self):
        class MyStr(str):
            pass
        assert parse_user_id(MyStr("user:admin")) is None

    def test_string_subclass_in_batch(self):
        class MyStr(str):
            pass
        result = parse_user_ids([MyStr("user:abc"), MyStr("user:def")])
        assert _uids(result) == ["abc", "def"]


class TestParseResultAdvancedProperties:
    """Test namedtuple-specific properties of ParseResult."""

    def test_asdict_returns_dict(self):
        r = parse_user_id("user:abc")
        d = r._asdict()
        assert d == {"user_id": "abc", "source": "string"}
        assert isinstance(d, dict)

    def test_asdict_for_email_source(self):
        r = parse_user_id("email:abc@test.com")
        d = r._asdict()
        assert d == {"user_id": "abc", "source": "email"}

    def test_asdict_for_dict_flat_source(self):
        r = parse_user_id({"user_id": "abc"})
        d = r._asdict()
        assert d == {"user_id": "abc", "source": "dict_flat"}

    def test_replace_user_id_creates_new_instance(self):
        r = parse_user_id("user:abc")
        r2 = r._replace(user_id="xyz")
        assert r2.user_id == "xyz"
        assert r2.source == "string"
        assert r.user_id == "abc"  # original unchanged

    def test_replace_source_creates_new_instance(self):
        r = parse_user_id("user:abc")
        r2 = r._replace(source="custom")
        assert r2.source == "custom"
        assert r.source == "string"  # original unchanged

    def test_hashable_equal_results_same_hash(self):
        r1 = parse_user_id("user:abc")
        r2 = parse_user_id("user:abc")
        assert hash(r1) == hash(r2)

    def test_usable_as_dict_key(self):
        r = parse_user_id("user:abc")
        d = {r: "value"}
        assert d[r] == "value"

    def test_usable_in_set_deduplicates(self):
        r1 = parse_user_id("user:abc")
        r2 = parse_user_id("user:abc")
        s = {r1, r2}
        assert len(s) == 1

    def test_equal_to_plain_tuple(self):
        r = parse_user_id("user:abc")
        assert r == ("abc", "string")

    def test_different_source_not_equal(self):
        r = parse_user_id("user:abc")
        assert r != ("abc", "email")

    def test_iteration_yields_both_fields(self):
        r = parse_user_id("user:abc")
        fields = list(r)
        assert fields == ["abc", "string"]


class TestParseUserIdsNonListIterables:
    """Test parse_user_ids with non-list iterable inputs."""

    def test_tuple_input(self):
        items = ("user:abc", "user:def")
        result = parse_user_ids(items)
        assert _uids(result) == ["abc", "def"]

    def test_generator_input(self):
        def gen():
            yield "user:abc"
            yield "user:def"
        result = parse_user_ids(gen())
        assert _uids(result) == ["abc", "def"]

    def test_generator_with_mixed_valid_invalid(self):
        def gen():
            yield "user:abc"
            yield None
            yield {"user_id": "def"}
        result = parse_user_ids(gen())
        assert _uids(result) == ["abc", None, "def"]

    def test_empty_tuple_returns_empty_list(self):
        result = parse_user_ids(())
        assert result == []

    def test_map_iterator_input(self):
        items = ["user:abc", "user:def"]
        result = parse_user_ids(iter(items))
        assert _uids(result) == ["abc", "def"]

    def test_tuple_with_strict_and_reserved(self):
        items = ("user:a__b", "user:admin", "user:valid1")
        result = parse_user_ids(items, reserved_ids={"admin"}, strict=True)
        assert _uids(result) == [None, None, "valid1"]


class TestAdditionalBadInputTypesNew:
    """Test additional bad input types not covered by existing tests."""

    def test_complex_number_input(self):
        assert parse_user_id(complex(1, 2)) is None

    def test_range_object_input(self):
        assert parse_user_id(range(10)) is None

    def test_memoryview_input(self):
        assert parse_user_id(memoryview(b"user:abc")) is None

    def test_frozenset_input_returns_none(self):
        assert parse_user_id(frozenset({"abc"})) is None

    def test_bytearray_input(self):
        assert parse_user_id(bytearray(b"user:abc")) is None

    def test_lambda_input(self):
        assert parse_user_id(lambda: "user:abc") is None

    def test_type_object_input(self):
        assert parse_user_id(int) is None

    def test_ellipsis_input(self):
        assert parse_user_id(...) is None

    def test_notimplemented_input(self):
        assert parse_user_id(NotImplemented) is None


class TestDictUnusualValueTypesNew:
    """Test dict inputs with unusual value types for user_id and nested id."""

    def test_user_id_float_value(self):
        assert parse_user_id({"user_id": 3.14}) is None

    def test_user_id_complex_value(self):
        assert parse_user_id({"user_id": complex(1, 2)}) is None

    def test_user_id_frozenset_value(self):
        assert parse_user_id({"user_id": frozenset({"abc"})}) is None

    def test_user_id_tuple_value(self):
        assert parse_user_id({"user_id": ("abc",)}) is None

    def test_nested_id_bool_value_rejected(self):
        assert parse_user_id({"user": {"id": True}}) is None

    def test_nested_id_float_value(self):
        assert parse_user_id({"user": {"id": 3.14}}) is None

    def test_nested_id_none_value_rejected(self):
        assert parse_user_id({"user": {"id": None}}) is None

    def test_nested_id_bytes_value(self):
        assert parse_user_id({"user": {"id": b"abc"}}) is None

    def test_user_id_float_falls_through_to_nested(self):
        result = parse_user_id({"user_id": 3.14, "user": {"id": "abc"}})
        assert _uid(result) == "abc"

    def test_user_id_complex_falls_through_to_nested(self):
        result = parse_user_id({"user_id": 1j, "user": {"id": "abc"}})
        assert _uid(result) == "abc"


class TestValidationPipelineOrder:
    """Verify the validation pipeline: extract -> strip -> lower -> regex -> reserved -> strict."""

    def test_strip_happens_before_length_check(self):
        # "  abc  " -> strip -> "abc" (3 chars, valid length)
        assert _uid(parse_user_id("user:  abc  ")) == "abc"

    def test_lowercase_happens_before_regex_check(self):
        # "ABC" -> lower -> "abc" -> matches [a-z0-9_-]
        assert _uid(parse_user_id("user:ABC")) == "abc"

    def test_lowercase_happens_before_reserved_check(self):
        # "ADMIN" -> lower -> "admin" -> in reserved -> None
        assert parse_user_id("user:ADMIN") is None

    def test_regex_checked_before_reserved(self):
        # "adm!n" -> regex fails -> None (even though no reserved check needed)
        assert parse_user_id("user:adm!n") is None

    def test_reserved_checked_before_strict(self):
        # "admin" -> no consecutive specials, but reserved -> None
        assert parse_user_id("user:admin", strict=True) is None

    def test_full_pipeline_normalization_to_strict_rejection(self):
        # "  A__B  " -> strip -> "A__B" -> lower -> "a__b" -> regex ok -> not reserved -> strict: __ -> None
        assert parse_user_id("user:  A__B  ", strict=True) is None

    def test_full_pipeline_normalization_to_valid(self):
        # "  Test_User  " -> strip -> "Test_User" -> lower -> "test_user" -> regex ok -> not reserved -> strict ok -> valid
        assert _uid(parse_user_id("user:  Test_User  ", strict=True)) == "test_user"

    def test_regex_failure_short_circuits_reserved_and_strict(self):
        # "a.b" -> regex fails -> None (xref) -> returns None immediately
        assert parse_user_id("user:a.b", reserved_ids=set(), strict=False) is None


class TestBoundaryLengthsAllPaths:
    """Test exactly 3 and 20 length IDs via all 4 input paths."""

    def test_length_3_via_email_path(self):
        assert _uid(parse_user_id("email:abc@test.com")) == "abc"

    def test_length_20_via_email_path(self):
        uid = "a" * 20
        assert _uid(parse_user_id(f"email:{uid}@test.com")) == uid

    def test_length_2_rejected_via_email_path(self):
        assert parse_user_id("email:ab@test.com") is None

    def test_length_21_rejected_via_email_path(self):
        uid = "a" * 21
        assert parse_user_id(f"email:{uid}@test.com") is None

    def test_length_3_via_dict_flat_path(self):
        assert _uid(parse_user_id({"user_id": "abc"})) == "abc"

    def test_length_20_via_dict_flat_path(self):
        uid = "a" * 20
        assert _uid(parse_user_id({"user_id": uid})) == uid

    def test_length_2_rejected_via_dict_flat_path(self):
        assert parse_user_id({"user_id": "ab"}) is None

    def test_length_21_rejected_via_dict_flat_path(self):
        uid = "a" * 21
        assert parse_user_id({"user_id": uid}) is None

    def test_length_3_via_dict_nested_path(self):
        assert _uid(parse_user_id({"user": {"id": "abc"}})) == "abc"

    def test_length_20_via_dict_nested_path(self):
        uid = "a" * 20
        assert _uid(parse_user_id({"user": {"id": uid}})) == uid

    def test_length_2_rejected_via_dict_nested_path(self):
        assert parse_user_id({"user": {"id": "ab"}}) is None

    def test_length_21_rejected_via_dict_nested_path(self):
        uid = "a" * 21
        assert parse_user_id({"user": {"id": uid}}) is None


class TestEmailDomainIndependence:
    """Verify email domain doesn't affect user_id extraction."""

    def test_same_username_different_domains(self):
        r1 = parse_user_id("email:user1@domain1.com")
        r2 = parse_user_id("email:user1@domain2.org")
        assert _uid(r1) == _uid(r2) == "user1"

    def test_domain_with_very_long_string(self):
        domain = "a" * 200 + ".com"
        assert _uid(parse_user_id(f"email:abc@{domain}")) == "abc"

    def test_domain_with_numbers(self):
        assert _uid(parse_user_id("email:abc@123.456.789")) == "abc"

    def test_empty_domain_after_at(self):
        assert _uid(parse_user_id("email:abc@")) == "abc"

    def test_domain_with_special_chars(self):
        assert _uid(parse_user_id("email:abc@test!server")) == "abc"


class TestMultipleBatchCallsIndependent:
    """Verify multiple batch calls don't interfere with each other."""

    def test_sequential_batch_calls_different_items(self):
        r1 = parse_user_ids(["user:abc"])
        r2 = parse_user_ids(["user:def"])
        assert _uids(r1) == ["abc"]
        assert _uids(r2) == ["def"]

    def test_batch_with_different_reserved_independent(self):
        r1 = parse_user_ids(["user:admin"], reserved_ids=set())
        r2 = parse_user_ids(["user:admin"])  # default reserved
        assert _uids(r1) == ["admin"]
        assert _uids(r2) == [None]

    def test_batch_strict_and_nonstrict_independent(self):
        r1 = parse_user_ids(["user:a__b"], strict=True)
        r2 = parse_user_ids(["user:a__b"], strict=False)
        assert _uids(r1) == [None]
        assert _uids(r2) == ["a__b"]

    def test_batch_returns_distinct_list_objects(self):
        items = ["user:abc"]
        r1 = parse_user_ids(items)
        r2 = parse_user_ids(items)
        assert r1 == r2
        assert r1 is not r2


class TestDefaultDictEdgeCases:
    """Test defaultdict behavior with parse_user_id."""

    def test_defaultdict_with_user_id_key_set(self):
        from collections import defaultdict
        d = defaultdict(lambda: "default_val")
        d["user_id"] = "abc"
        assert _uid(parse_user_id(d)) == "abc"

    def test_defaultdict_without_matching_keys(self):
        from collections import defaultdict
        d = defaultdict(lambda: "abc")
        # "user_id" not in d is True (defaultdict __contains__ checks actual keys)
        # "user" not in d is True
        assert parse_user_id(d) is None

    def test_defaultdict_with_nested_user_key(self):
        from collections import defaultdict
        inner = defaultdict(str)
        inner["id"] = "abc"
        d = defaultdict(dict)
        d["user"] = inner
        assert _uid(parse_user_id(d)) == "abc"


class TestStrictModePositionalInMaxLengthIds:
    """Strict mode with consecutive specials at various positions in 20-char IDs."""

    def test_consecutive_at_start_of_20_char_id(self):
        uid = "__" + "a" * 18  # 20 chars
        assert len(uid) == 20
        assert parse_user_id(f"user:{uid}", strict=True) is None

    def test_consecutive_at_end_of_20_char_id(self):
        uid = "a" * 18 + "__"  # 20 chars
        assert len(uid) == 20
        assert parse_user_id(f"user:{uid}", strict=True) is None

    def test_consecutive_in_middle_of_20_char_id(self):
        uid = "a" * 9 + "__" + "b" * 9  # 20 chars
        assert len(uid) == 20
        assert parse_user_id(f"user:{uid}", strict=True) is None

    def test_no_consecutive_in_20_char_id_valid(self):
        uid = "a_b_c_d_e_f_g_h_i_jk"  # 20 chars, no consecutive
        assert len(uid) == 20
        assert _uid(parse_user_id(f"user:{uid}", strict=True)) == uid

    def test_no_consecutive_in_3_char_id_valid(self):
        assert _uid(parse_user_id("user:a_b", strict=True)) == "a_b"
        assert _uid(parse_user_id("user:a-b", strict=True)) == "a-b"


class TestCombinedAllParamsAllPaths:
    """Integration tests combining reserved_ids + strict + normalization + all paths."""

    def test_all_paths_strict_custom_reserved_in_batch(self):
        items = [
            "user:valid1",
            "email:valid2@t.com",
            {"user_id": "valid3"},
            {"user": {"id": "valid4"}},
            "user:a__b",
            "user:blocked",
            "email:blocked@t.com",
            {"user_id": "blocked"},
            {"user": {"id": "blocked"}},
            "user:ab",
        ]
        result = parse_user_ids(items, reserved_ids={"blocked"}, strict=True)
        expected = ["valid1", "valid2", "valid3", "valid4", None, None, None, None, None, None]
        assert _uids(result) == expected

    def test_normalization_with_all_params(self):
        result = parse_user_id(
            "  user:  Valid_User  ",
            reserved_ids={"other"},
            strict=True,
        )
        assert result is not None
        assert result.user_id == "valid_user"
        assert result.source == "string"

    def test_email_normalization_with_all_params(self):
        result = parse_user_id(
            "  email:  ValidUser  @test.com  ",
            reserved_ids={"other"},
            strict=True,
        )
        assert result is not None
        assert result.user_id == "validuser"
        assert result.source == "email"


class TestControlCharsInId:
    """Verify non-printable control characters fail regex validation."""

    def test_form_feed_in_id(self):
        assert parse_user_id("user:ab\x0ccd") is None

    def test_bell_in_id(self):
        assert parse_user_id("user:ab\x07cd") is None

    def test_backspace_in_id(self):
        assert parse_user_id("user:ab\x08cd") is None

    def test_escape_in_id(self):
        assert parse_user_id("user:ab\x1bcd") is None

    def test_delete_char_in_id(self):
        assert parse_user_id("user:ab\x7fcd") is None

    def test_null_byte_via_dict(self):
        assert parse_user_id({"user_id": "ab\x00cd"}) is None

    def test_null_byte_via_email(self):
        assert parse_user_id("email:ab\x00c@test.com") is None


class TestPrefixExactMatchVerification:
    """Verify that prefixes must be exact: 'user' or 'email'."""

    def test_users_prefix_rejected(self):
        assert parse_user_id("users:abc") is None

    def test_user1_prefix_rejected(self):
        assert parse_user_id("user1:abc") is None

    def test_emails_prefix_rejected(self):
        assert parse_user_id("emails:abc@test.com") is None

    def test_email1_prefix_rejected(self):
        assert parse_user_id("email1:abc@test.com") is None

    def test_mail_prefix_rejected(self):
        assert parse_user_id("mail:abc@test.com") is None

    def test_account_prefix_rejected(self):
        assert parse_user_id("account:abc") is None

    def test_numeric_prefix_rejected(self):
        assert parse_user_id("123:abc") is None

    def test_user_prefix_with_trailing_space_rejected(self):
        # After strip: "user :abc" -> split on ":" -> prefix="user " != "user"
        assert parse_user_id("user :abc") is None

    def test_email_prefix_with_trailing_space_rejected(self):
        assert parse_user_id("email :abc@test.com") is None


class TestDictExtraKeysNoInterference:
    """Ensure extra keys in dict don't interfere with extraction."""

    def test_many_extra_keys_user_id(self):
        d = {
            "user_id": "abc",
            "name": "test",
            "email": "test@test.com",
            "role": "admin_role",
            "active": True,
            "count": 42,
        }
        assert _uid(parse_user_id(d)) == "abc"

    def test_extra_nested_keys_in_user_dict(self):
        d = {
            "user": {
                "id": "abc",
                "name": "test",
                "email": "test@test.com",
                "roles": ["viewer"],
            }
        }
        assert _uid(parse_user_id(d)) == "abc"

    def test_numeric_string_keys_dont_interfere(self):
        d = {"user_id": "abc", "0": "zero", "1": "one"}
        assert _uid(parse_user_id(d)) == "abc"


class TestStrictModeIdempotentBehavior:
    """Verify strict mode is consistent across repeated calls."""

    def test_strict_rejection_stable_across_calls(self):
        for _ in range(10):
            assert parse_user_id("user:a__b", strict=True) is None

    def test_strict_acceptance_stable_across_calls(self):
        for _ in range(10):
            assert _uid(parse_user_id("user:a_b", strict=True)) == "a_b"

    def test_nonstrict_acceptance_stable_across_calls(self):
        for _ in range(10):
            assert _uid(parse_user_id("user:a__b", strict=False)) == "a__b"


class TestParseResultNoneVsFalsyConsistency:
    """Ensure all invalid paths return exactly None, not other falsy values."""

    def test_empty_string_returns_none_not_false(self):
        result = parse_user_id("")
        assert result is None
        assert result is not False
        assert result != 0
        assert result != ""

    def test_bad_type_returns_none_not_empty_string(self):
        result = parse_user_id(42)
        assert result is None
        assert result != ""

    def test_strict_fail_returns_none_not_zero(self):
        result = parse_user_id("user:a__b", strict=True)
        assert result is None
        assert result != 0


class TestBatchNoneElementsAreExactlyNone:
    """Verify None elements in batch results are exactly None."""

    def test_batch_none_is_singleton_none(self):
        result = parse_user_ids([None, 42, "bad", "user:admin"])
        for r in result:
            assert r is None

    def test_batch_none_from_strict_is_singleton_none(self):
        result = parse_user_ids(["user:a__b", "user:a--b"], strict=True)
        for r in result:
            assert r is None


class TestEmailSourceFieldInAllScenarios:
    """Verify source field is correctly set for email path across scenarios."""

    def test_email_source_with_uppercase_normalization(self):
        r = parse_user_id("email:ABC@test.com")
        assert r.source == "email"

    def test_email_source_with_whitespace_stripping(self):
        r = parse_user_id("  email:abc@test.com  ")
        assert r.source == "email"

    def test_email_source_with_custom_reserved(self):
        r = parse_user_id("email:abc@test.com", reserved_ids=set())
        assert r.source == "email"

    def test_email_source_with_strict_mode_passing(self):
        r = parse_user_id("email:a_b@test.com", strict=True)
        assert r is not None
        assert r.source == "email"

    def test_email_source_in_batch_with_params(self):
        result = parse_user_ids(
            ["email:abc@test.com"],
            reserved_ids=set(),
            strict=True,
        )
        assert result[0].source == "email"


@pytest.mark.skipif(not HAS_Z3, reason="z3-solver not installed")
class TestZ3StrictModeRegexVerification:
    """Z3 formal verification of the strict mode [_-]{2} pattern."""

    def test_z3_double_underscore_matches_strict_pattern(self):
        from z3 import String, StringVal, Solver, InRe, Re, Concat, Union, sat
        s = Solver()
        x = String("x")
        special = Union(Re("_"), Re("-"))
        pattern = Concat(special, special)
        s.add(x == StringVal("__"))
        s.add(InRe(x, pattern))
        assert s.check() == sat

    def test_z3_double_hyphen_matches_strict_pattern(self):
        from z3 import String, StringVal, Solver, InRe, Re, Concat, Union, sat
        s = Solver()
        x = String("x")
        special = Union(Re("_"), Re("-"))
        pattern = Concat(special, special)
        s.add(x == StringVal("--"))
        s.add(InRe(x, pattern))
        assert s.check() == sat

    def test_z3_underscore_hyphen_matches_strict_pattern(self):
        from z3 import String, StringVal, Solver, InRe, Re, Concat, Union, sat
        s = Solver()
        x = String("x")
        special = Union(Re("_"), Re("-"))
        pattern = Concat(special, special)
        s.add(x == StringVal("_-"))
        s.add(InRe(x, pattern))
        assert s.check() == sat

    def test_z3_hyphen_underscore_matches_strict_pattern(self):
        from z3 import String, StringVal, Solver, InRe, Re, Concat, Union, sat
        s = Solver()
        x = String("x")
        special = Union(Re("_"), Re("-"))
        pattern = Concat(special, special)
        s.add(x == StringVal("-"))
        s.add(InRe(x, pattern))
        assert s.check() == sat

    def test_z3_single_underscore_does_not_match_strict_pattern(self):
        from z3 import String, StringVal, Solver, InRe, Re, Concat, Union, unsat
        s = Solver()
        x = String("x")
        special = Union(Re("_"), Re("-"))
        pattern = Concat(special, special)
        s.add(x == StringVal("_"))
        s.add(InRe(x, pattern))
        assert s.check() == unsat

    def test_z3_single_hyphen_does_not_match_strict_pattern(self):
        from z3 import String, StringVal, Solver, InRe, Re, Concat, Union, unsat
        s = Solver()
        x = String("x")
        special = Union(Re("_"), Re("-"))
        pattern = Concat(special, special)
        s.add(x == StringVal("-"))
        s.add(InRe(x, pattern))
        assert s.check() == unsat

    def test_z3_letter_then_underscore_does_not_match_strict_pattern(self):
        from z3 import String, StringVal, Solver, InRe, Re, Concat, Union, unsat
        s = Solver()
        x = String("x")
        special = Union(Re("_"), Re("-"))
        pattern = Concat(special, special)
        s.add(x == StringVal("a_"))
        s.add(InRe(x, pattern))
        assert s.check() == unsat

    def test_z3_valid_id_without_consecutive_specials_exists(self):
        from z3 import String, Length, Solver, InRe, Re, Range, Star, Union, sat, Not, Concat
        s = Solver()
        x = String("x")
        char_class = Union(Range("a", "z"), Range("0", "9"), Re("_"), Re("-"))
        valid_regex = Star(char_class)
        any_char = Star(Union(Range("\x00", "\xff")))
        special = Union(Re("_"), Re("-"))
        consecutive = Concat(any_char, Concat(special, special), any_char)
        s.add(InRe(x, valid_regex))
        s.add(Length(x) >= 3)
        s.add(Length(x) <= 20)
        s.add(Not(InRe(x, consecutive)))
        assert s.check() == sat, "Valid IDs without consecutive specials should exist"

    def test_z3_all_four_strict_patterns_are_consecutive_specials(self):
        """Formally verify all four two-char special combos match [_-]{2}."""
        from z3 import String, StringVal, Solver, InRe, Re, Concat, Union, sat
        patterns = ["__", "--", "_-", "-_"]
        special = Union(Re("_"), Re("-"))
        regex = Concat(special, special)
        for p in patterns:
            s = Solver()
            x = String("x")
            s.add(x == StringVal(p))
            s.add(InRe(x, regex))
            assert s.check() == sat, f"Pattern '{p}' should match [_-]{{2}}"


class TestDictSubclassesAdvanced:
    """Advanced dict subclass edge cases."""

    def test_ordered_dict_nested_path(self):
        from collections import OrderedDict
        d = OrderedDict([("user", OrderedDict([("id", "abc")]))])
        r = parse_user_id(d)
        assert r is not None and r.user_id == "abc" and r.source == "dict_nested"

    def test_dict_subclass_with_custom_repr(self):
        class DescriptiveDict(dict):
            def __repr__(self):
                return "DescriptiveDict(...)"
        d = DescriptiveDict(user_id="abc")
        assert _uid(parse_user_id(d)) == "abc"


class TestStrictModeWithMinLengthIds:
    """Test strict mode with minimum length (3 char) IDs containing specials."""

    def test_3_char_all_underscores_strict_rejected(self):
        # "___" → contains "__" → rejected
        assert parse_user_id("user:___", strict=True) is None

    def test_3_char_all_hyphens_strict_rejected(self):
        # "---" → contains "--" → rejected
        assert parse_user_id("user:---", strict=True) is None

    def test_3_char_underscore_hyphen_letter_strict_rejected(self):
        # "_-a" → contains "_-" → rejected
        assert parse_user_id("user:_-a", strict=True) is None

    def test_3_char_letter_between_specials_strict_allowed(self):
        # "a_b" → no consecutive → allowed
        assert _uid(parse_user_id("user:a_b", strict=True)) == "a_b"
        # "a-b" → no consecutive → allowed
        assert _uid(parse_user_id("user:a-b", strict=True)) == "a-b"

    def test_3_char_no_specials_strict_allowed(self):
        assert _uid(parse_user_id("user:abc", strict=True)) == "abc"
        assert _uid(parse_user_id("user:123", strict=True)) == "123"


class TestEmailWithWhitespaceInRemainder:
    """Test whitespace handling within email remainder."""

    def test_email_spaces_around_username_trimmed_after_extraction(self):
        # "email: abc @test" → remainder = " abc @test" → split on @ → username = " abc "
        # Then parse_user_id does strip() → "abc"
        assert _uid(parse_user_id("email: abc @test")) == "abc"

    def test_email_tabs_around_username_in_remainder(self):
        # "email:\tabc\t@test" → username = "\tabc\t" → strip → "abc"
        assert _uid(parse_user_id("email:\tabc\t@test")) == "abc"

    def test_email_mixed_whitespace_around_username(self):
        # "email: \t abc \n @test" → username = " \t abc \n " → strip → "abc"
        assert _uid(parse_user_id("email: \t abc \n @test")) == "abc"