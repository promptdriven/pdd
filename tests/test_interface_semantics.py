import pytest

from pdd.interface_semantics import (
    DefaultCompatibility,
    annotations_compatible,
    build_module_default_symbols,
    compare_default_sources,
    signature_entries_compatible,
)


@pytest.mark.parametrize(
    ("left", "right"),
    [
        ("Dict[str, Any]", "dict[str, Any]"),
        ("typing.Dict[str, Any]", "dict[str, Any]"),
        ("List[str]", "list[str]"),
        ("Optional[Set[str]]", "Set[str] | None"),
        ("Optional[Set[str]]", "Union[Set[str], None]"),
        ("Optional[typing.Set[str]]", "typing.Union[set[str], None]"),
        ("set", "Set[str]"),
        # Union members are an unordered set: reordering them is not drift.
        ("Union[str, int]", "Union[int, str]"),
        ("int | str", "str | int"),
        ("Union[str, int, bytes]", "bytes | str | int"),
        # ...including parameterized members reordered, and with aliasing.
        ("Union[List[str], int]", "Union[int, list[str]]"),
        # Nested unions flatten: Union[Union[str, int], bytes] == the flat set.
        ("Union[Union[str, int], bytes]", "bytes | int | str"),
        # Optional wrapping a union is the same as a union that includes None.
        ("Optional[Union[str, int]]", "Union[str, int, None]"),
        # A single-member union collapses to that member.
        ("Union[str]", "str"),
        # A nested optional member hoists its None to the enclosing union:
        # Union[Optional[str], int] == Union[str, int, None].
        ("Union[Optional[str], int]", "Union[str, int, None]"),
        ("Union[Optional[str], int]", "Optional[Union[str, int]]"),
        ("Optional[str] | int", "str | int | None"),
        ("typing.Optional[str] | int", "str | None | int"),
        # Optional[Optional[X]] collapses to Optional[X].
        ("Optional[Optional[str]]", "Optional[str]"),
        # NoneType (bare Name and types.-qualified) is the same as None.
        ("Union[str, NoneType]", "str | None"),
        ("Union[str, NoneType]", "Optional[str]"),
        ("Union[str, types.NoneType]", "str | None"),
    ],
)
def test_semantic_type_aliases_are_compatible(left, right):
    assert annotations_compatible(left, right)


def test_wide_reordered_union_is_compatible_without_factorial_blowup():
    # A reordered 12-member union: a permutation-based matcher would explore
    # 12! (~minutes) and trip the CI timeout, so this passing instantly is the
    # regression guard for the bipartite matcher. The timeout IS the assertion.
    members = [f"T{index}" for index in range(12)]
    left = "Union[" + ", ".join(members) + "]"
    right = "Union[" + ", ".join(reversed(members)) + "]"
    assert annotations_compatible(left, right)


@pytest.mark.parametrize(
    ("left", "right"),
    [
        ("List[str]", "Dict[str, str]"),
        ("Optional[str]", "str"),
        ("mytypes.Set", "Set[str]"),
        # Dropping ``None`` from a 3+-member union narrows the contract (a
        # caller passing None breaks), so it must NOT be treated as compatible.
        ("Union[str, int, None]", "Union[str, int]"),
        ("str | int | None", "str | int"),
        # ...even when the None arrives via a nested optional member.
        ("Union[Optional[str], int]", "Union[str, int]"),
        # Swapping a union member for a different type is still drift.
        ("Union[str, int]", "Union[str, float]"),
    ],
)
def test_semantic_type_incompatible_changes_fail(left, right):
    assert not annotations_compatible(left, right)


@pytest.mark.parametrize(
    ("old_entry", "new_entry"),
    [
        # Adding a default to a previously-required parameter preserves every
        # existing call form (callers always supplied it), so it is NOT a
        # public-surface regression.
        ("[function] (x)", "[function] (x=0)"),
        ("[function] (a, b)", "[function] (a, b=1)"),
        ("[function] (*, strict)", "[function] (*, strict=False)"),
    ],
)
def test_adding_a_default_is_not_a_regression(old_entry, new_entry):
    assert signature_entries_compatible(old_entry, new_entry) is True


@pytest.mark.parametrize(
    ("old_entry", "new_entry"),
    [
        # Dropping a default the old signature had breaks callers that omitted
        # the argument -> genuine regression.
        ("[function] (x=0)", "[function] (x)"),
        ("[function] (*, strict=False)", "[function] (*, strict)"),
        # Changing a default value is conservatively treated as a regression.
        ("[function] (x=0)", "[function] (x=1)"),
    ],
)
def test_removing_or_changing_a_default_is_a_regression(old_entry, new_entry):
    assert signature_entries_compatible(old_entry, new_entry) is False


@pytest.mark.parametrize(
    ("old_entry", "new_entry", "compatible"),
    [
        # Reordering union members in a parameter annotation is not a regression.
        ("[function] (v: str | int)", "[function] (v: int | str)", True),
        # Narrowing a parameter's union by dropping None breaks callers that
        # passed None -> genuine public-surface regression.
        ("[function] (v: str | int | None)", "[function] (v: str | int)", False),
    ],
)
def test_union_parameter_compatibility(old_entry, new_entry, compatible):
    assert signature_entries_compatible(old_entry, new_entry) is compatible


@pytest.mark.parametrize(
    ("old_entry", "new_entry", "compatible"),
    [
        # Inserting a defaulted positional parameter in front of an existing
        # *args rebinds existing positional calls: f(1, 2) used to land the 2
        # in *args, but now binds it to the new parameter -> regression.
        ("[function] (a, *args)", "[function] (a, b=0, *args)", False),
        ("[function] (*args)", "[function] (b=0, *args)", False),
        # A keyword-only parameter added after *args cannot intercept a
        # positional slot, so it stays compatible.
        ("[function] (a, *args)", "[function] (a, *args, b=0)", True),
        # With no *args to steal a positional from, adding a defaulted
        # positional parameter is a backward-compatible widening.
        ("[function] (a)", "[function] (a, b=0)", True),
    ],
)
def test_new_positional_before_varargs_is_a_regression(
    old_entry, new_entry, compatible
):
    assert signature_entries_compatible(old_entry, new_entry) is compatible


@pytest.mark.parametrize(
    ("old_entry", "new_entry", "compatible"),
    [
        # Symmetric to the *args case: a new keyword-capable parameter captures
        # a keyword that previously flowed into **kwargs -- f(a=5) used to land
        # in kwargs['a'], now binds the new parameter -> regression.
        ("[function] (**kwargs)", "[function] (a=0, **kwargs)", False),
        ("[function] (**kwargs)", "[function] (*, a=0, **kwargs)", False),
        # A positional-only parameter cannot be passed by keyword, so it never
        # steals from **kwargs and stays compatible.
        ("[function] (**kwargs)", "[function] (a=0, /, **kwargs)", True),
        # Without **kwargs, adding a defaulted keyword param is a widening.
        ("[function] (a)", "[function] (a, b=0)", True),
    ],
)
def test_new_keyword_param_with_existing_kwargs_is_a_regression(
    old_entry, new_entry, compatible
):
    assert signature_entries_compatible(old_entry, new_entry) is compatible


# ---------------------------------------------------------------------------
# Semantic default comparator (issue #1545): default values are compared as
# normalized literals, not raw source strings, so a literal and an equivalent
# module constant are the same contract.
# ---------------------------------------------------------------------------
@pytest.mark.parametrize(
    ("declared", "actual"),
    [
        ("25000", "25_000"),  # digit-group separator is the same int
        ("25000", "25000"),
        ("None", "None"),
        ("False", "False"),
        ("'literal'", '"literal"'),  # quote style is irrelevant
        ("('a', 'b')", "('a','b')"),  # whitespace is irrelevant
        ("-1", "-1"),  # unary minus folds
        ("{1, 2}", "{2, 1}"),  # set membership is order-insensitive
        ("{'a': 1, 'b': 2}", "{'b': 2, 'a': 1}"),  # dict key order irrelevant
        ("1e3", "1000.0"),  # equal floats written differently
        ("0.0", "0.0"),
        ("-0.0", "-0.0"),  # same signed zero
    ],
)
def test_equivalent_defaults_are_compatible(declared, actual):
    assert (
        compare_default_sources(declared, actual) is DefaultCompatibility.COMPATIBLE
    )


@pytest.mark.parametrize(
    ("declared", "actual"),
    [
        ("25000", "5000"),  # provably different ints
        ("1", "True"),  # bool is not the int 1
        ("25000", "25000.0"),  # int is not the float
        ("(1, 2)", "[1, 2]"),  # tuple is not the list
        ("'a'", "'b'"),
        ("-1", "1"),
        # Signed zero is behaviorally observable (copysign/division/format),
        # so -0.0 and 0.0 must NOT be treated as the same default.
        ("-0.0", "0.0"),
        ("0.0", "-0.0"),
    ],
)
def test_provably_different_defaults_are_incompatible(declared, actual):
    assert (
        compare_default_sources(declared, actual) is DefaultCompatibility.INCOMPATIBLE
    )


@pytest.mark.parametrize(
    ("declared", "actual"),
    [
        # A bare name has no module context here, so it cannot be resolved.
        ("25000", "_LIMIT"),
        ("_LIMIT", "25000"),
        # Calls / attribute access / dynamic expressions never resolve.
        ("get_limit()", "compute_limit()"),
        ("25000", "os.getenv('LIMIT')"),
        ("SOME_IMPORTED_VALUE", "25000"),
        ("f'{x}'", "f'{x}'"),  # f-strings are dynamic
    ],
)
def test_unresolvable_defaults_are_unknown(declared, actual):
    assert compare_default_sources(declared, actual) is DefaultCompatibility.UNKNOWN


def test_same_module_constant_resolves_to_its_literal():
    symbols = build_module_default_symbols("_COMMENT_MAX_CHARS = 25000\n")
    assert (
        compare_default_sources("25000", "_COMMENT_MAX_CHARS", symbols)
        is DefaultCompatibility.COMPATIBLE
    )
    assert (
        compare_default_sources("_COMMENT_MAX_CHARS", "25000", symbols)
        is DefaultCompatibility.COMPATIBLE
    )


def test_same_module_constant_with_different_value_is_incompatible():
    symbols = build_module_default_symbols("_COMMENT_MAX_CHARS = 5000\n")
    assert (
        compare_default_sources("25000", "_COMMENT_MAX_CHARS", symbols)
        is DefaultCompatibility.INCOMPATIBLE
    )


@pytest.mark.parametrize(
    "module_source",
    [
        # Reassigned to a different safe value -> not statically knowable.
        "X = 25000\nX = 5000\n",
        # Augmented assignment is a second binding.
        "X = 25000\nX += 1\n",
        # Conditionally overridden inside a block.
        "X = 25000\nif FLAG:\n    X = 5000\n",
        # Bound to an unsafe right-hand side.
        "X = get_limit()\n",
        # Tuple-unpacking rebind elsewhere.
        "X = 25000\nX, Y = load()\n",
        # A def/class/import that shadows the constant rebinds the name at
        # runtime even though it creates no ``ast.Name`` Store node — the
        # running module's ``X`` is the def/class/import object, not 25000.
        "X = 25000\ndef X():\n    return 1\n",
        "X = 25000\nclass X:\n    pass\n",
        "X = 25000\nimport os as X\n",
        "X = 25000\nfrom mod import X\n",
        # ...and the reverse textual order is equally untrustworthy.
        "import os as X\nX = 25000\n",
        # ``except ... as X`` also rebinds without a Store node.
        "X = 25000\ntry:\n    pass\nexcept Exception as X:\n    pass\n",
        # A star import binds an unknowable name set that could shadow X.
        "X = 25000\nfrom config import *\n",
    ],
)
def test_unsafe_or_ambiguous_module_constants_stay_unresolved(module_source):
    symbols = build_module_default_symbols(module_source)
    assert "X" not in symbols
    # And a default referencing it therefore fails closed (UNKNOWN), never
    # silently accepted as equivalent to a literal.
    assert (
        compare_default_sources("25000", "X", symbols)
        is DefaultCompatibility.UNKNOWN
    )


def test_module_constant_table_does_not_resolve_name_aliases_transitively():
    # ``B = A`` must NOT enter the table: the right-hand side is normalized
    # without name resolution, so an alias chain stays UNKNOWN (fail closed).
    symbols = build_module_default_symbols("A = 25000\nB = A\n")
    assert symbols == {"A": ("int", 25000)}
    assert "B" not in symbols


def test_star_import_empties_the_whole_constant_table():
    # ``from x import *`` binds an unknowable set of names that could shadow
    # ANY constant, so EVERY constant in the module becomes untrustworthy —
    # not just same-named ones. The whole table is empty (fail closed).
    clean = build_module_default_symbols("MAX = 25000\nMIN = 0\n")
    assert clean == {"MAX": ("int", 25000), "MIN": ("int", 0)}
    poisoned = build_module_default_symbols(
        "MAX = 25000\nMIN = 0\nfrom config import *\n"
    )
    assert poisoned == {}
    assert (
        compare_default_sources("25000", "MAX", poisoned)
        is DefaultCompatibility.UNKNOWN
    )


@pytest.mark.parametrize(
    "module_source",
    [
        "_ITEMS = []\n",
        "_M = {1: 2}\n",
        "_S = {1, 2}\n",
        # An immutable-looking tuple that holds a mutable element is itself
        # not safe — the inner list can still be mutated.
        "_T = (1, [2])\n",
    ],
)
def test_mutable_container_module_constants_are_not_trusted(module_source):
    # A constant bound to a mutable container can be mutated in place after
    # binding (e.g. ``_ITEMS.append(x)`` at import time), so its def-time value
    # is not the empty/initial container we see statically. Keep it out of the
    # table so a default ``=_ITEMS`` resolves UNKNOWN (fail closed) instead of
    # matching the literal it was initialized with.
    symbols = build_module_default_symbols(module_source)
    assert symbols == {}


def test_immutable_module_constants_are_still_trusted():
    # The fix for mutable containers must not stop trusting immutable values.
    symbols = build_module_default_symbols(
        "_LIMIT = 25000\n_NAME = 'x'\n_PAIR = (1, 2)\n_FLAG = False\n"
    )
    assert symbols["_LIMIT"] == ("int", 25000)
    assert symbols["_PAIR"] == ("tuple", (("int", 1), ("int", 2)))
    assert (
        compare_default_sources("(1, 2)", "_PAIR", symbols)
        is DefaultCompatibility.COMPATIBLE
    )


def test_signed_zero_default_change_is_a_regression_on_public_surface():
    # ``0.0`` -> ``-0.0`` on a public parameter default is behaviorally
    # observable, so the public-surface gate must flag it, not wave it through.
    assert (
        signature_entries_compatible(
            "[function] (x=0.0)", "[function] (x=-0.0)"
        )
        is False
    )


def test_public_surface_default_literal_normalization_is_not_a_regression():
    # The public-surface gate normalizes literals even without module context,
    # so a digit-separator reformat of a default is not a regression.
    assert (
        signature_entries_compatible(
            "[function] (x=25000)", "[function] (x=25_000)"
        )
        is True
    )


def test_public_surface_module_constant_default_is_conservatively_a_change():
    # Documented scope: the public-surface gate compares snapshot signature
    # strings with no module context, so a literal -> same-module-constant
    # refactor of a default stays UNKNOWN and is treated as a change there
    # (fail closed). Module-constant resolution is exercised only by the
    # prompt <pdd-interface> conformance gate, which has the generated AST.
    assert (
        signature_entries_compatible(
            "[function] (x=25000)", "[function] (x=_LIMIT)"
        )
        is False
    )
