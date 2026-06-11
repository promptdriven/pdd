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
# Semantic default comparator (issues #1545 / #1558): default values are
# compared as normalized literals, not raw source strings, so a literal and an
# equivalent module constant are the same contract.
# ---------------------------------------------------------------------------
@pytest.mark.parametrize(
    ("left", "right"),
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
def test_equivalent_defaults_are_compatible(left, right):
    assert compare_default_sources(left, right) is DefaultCompatibility.COMPATIBLE


@pytest.mark.parametrize(
    ("left", "right"),
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
def test_provably_different_defaults_are_incompatible(left, right):
    assert compare_default_sources(left, right) is DefaultCompatibility.INCOMPATIBLE


@pytest.mark.parametrize(
    ("left", "right"),
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
def test_unresolvable_defaults_are_unknown(left, right):
    assert compare_default_sources(left, right) is DefaultCompatibility.UNKNOWN


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


# ---------------------------------------------------------------------------
# Per-side symbol tables (issue #1558): each default resolves in its OWN
# module's namespace, so the same constant name can mean different values
# across an old and a generated module version.
# ---------------------------------------------------------------------------
def test_per_side_tables_resolve_each_default_in_its_own_module():
    old_symbols = build_module_default_symbols("_LIMIT = 25000\n")
    new_symbols = build_module_default_symbols("_LIMIT = 25_000\n")
    # Same name, equal resolved value across the two modules -> compatible.
    assert (
        compare_default_sources(
            "_LIMIT", "_LIMIT", left_symbols=old_symbols, right_symbols=new_symbols
        )
        is DefaultCompatibility.COMPATIBLE
    )


def test_per_side_tables_same_name_different_value_is_incompatible():
    old_symbols = build_module_default_symbols("_LIMIT = 25000\n")
    new_symbols = build_module_default_symbols("_LIMIT = 5000\n")
    # Identical source text "_LIMIT" on both sides, but the constant's VALUE
    # changed between module versions -> a real, provable contract break.
    assert (
        compare_default_sources(
            "_LIMIT", "_LIMIT", left_symbols=old_symbols, right_symbols=new_symbols
        )
        is DefaultCompatibility.INCOMPATIBLE
    )


def test_per_side_tables_old_literal_new_constant_is_compatible():
    new_symbols = build_module_default_symbols("_LIMIT = 25000\n")
    assert (
        compare_default_sources(
            "25000", "_LIMIT", left_symbols={}, right_symbols=new_symbols
        )
        is DefaultCompatibility.COMPATIBLE
    )


def test_per_side_argument_overrides_shared_symbols_for_that_side():
    shared = build_module_default_symbols("_LIMIT = 25000\n")
    override = build_module_default_symbols("_LIMIT = 5000\n")
    # ``symbols`` applies to both sides, but ``right_symbols`` overrides it for
    # the right side only, so the two ``_LIMIT`` resolve to 25000 vs 5000.
    assert (
        compare_default_sources(
            "_LIMIT", "_LIMIT", shared, right_symbols=override
        )
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
        # runtime even though it creates no ``ast.Name`` Store node.
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
    symbols = build_module_default_symbols(module_source)
    assert symbols == {}


def test_immutable_module_constants_are_still_trusted():
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
        signature_entries_compatible("[function] (x=0.0)", "[function] (x=-0.0)")
        is False
    )


def test_public_surface_default_literal_normalization_is_not_a_regression():
    # The public-surface gate normalizes literals even without module context,
    # so a digit-separator reformat of a default is not a regression.
    assert (
        signature_entries_compatible("[function] (x=25000)", "[function] (x=25_000)")
        is True
    )


def test_signature_entries_resolve_per_side_module_constant_defaults():
    # With per-side tables, an old-literal / new-same-module-constant default
    # refactor is recognized as the same contract (issue #1558).
    new_symbols = build_module_default_symbols("_LIMIT = 25000\n")
    assert (
        signature_entries_compatible(
            "[function] (x=25000)",
            "[function] (x=_LIMIT)",
            old_symbols={},
            new_symbols=new_symbols,
        )
        is True
    )


def test_signature_entries_same_named_constant_different_value_is_a_regression():
    # Identical signature text on both sides, but the constant's value changed
    # between the old and generated modules -> a provable contract break.
    old_symbols = build_module_default_symbols("_LIMIT = 25000\n")
    new_symbols = build_module_default_symbols("_LIMIT = 5000\n")
    assert (
        signature_entries_compatible(
            "[function] (x=_LIMIT)",
            "[function] (x=_LIMIT)",
            old_symbols=old_symbols,
            new_symbols=new_symbols,
        )
        is False
    )


def test_signature_entries_identical_unresolvable_default_is_not_a_regression():
    # Two identical unresolvable defaults changed nothing, so an UNKNOWN verdict
    # with equal source text must NOT be flagged (no false positive).
    assert (
        signature_entries_compatible(
            "[function] (x=helper())", "[function] (x=helper())"
        )
        is True
    )


def test_signature_entries_no_module_context_constant_is_conservatively_a_change():
    # Documented scope: with NO tables (e.g. a bare unit call), a literal ->
    # same-module-constant refactor of a default stays UNKNOWN and is treated as
    # a change (fail closed). The public-surface gate supplies the tables.
    assert (
        signature_entries_compatible("[function] (x=25000)", "[function] (x=_LIMIT)")
        is False
    )


def test_signature_entries_asymmetric_resolution_fails_closed():
    # Identical "_LIMIT" default text on both sides, but the constant resolves on
    # only ONE side: the other module leaves it unresolvable (a dynamic call, an
    # import, or a rebound name). Exactly one side being a known literal while the
    # other is opaque is positive evidence the effective default MAY have changed,
    # so textual equality must NOT wave it through -- fail closed. This is the
    # difference from two equally-unresolvable identical defaults, which DID
    # change nothing and stay compatible.
    resolves = build_module_default_symbols("_LIMIT = 5000\n")
    # Existing side opaque (empty table) -> generated side resolves to 5000.
    assert (
        signature_entries_compatible(
            "[function] (x=_LIMIT)",
            "[function] (x=_LIMIT)",
            old_symbols={},
            new_symbols=resolves,
        )
        is False
    )
    # Reverse direction: existing side resolves, generated side opaque.
    assert (
        signature_entries_compatible(
            "[function] (x=_LIMIT)",
            "[function] (x=_LIMIT)",
            old_symbols=resolves,
            new_symbols={},
        )
        is False
    )


def test_signature_entries_both_unresolvable_same_text_still_compatible():
    # The control for the asymmetric case above: when NEITHER side resolves and
    # the source text is identical, the default expression is unchanged, so it
    # must stay compatible even though one of them happens to be a bare name.
    assert (
        signature_entries_compatible(
            "[function] (x=_LIMIT)",
            "[function] (x=_LIMIT)",
            old_symbols={},
            new_symbols={},
        )
        is True
    )


# ---------------------------------------------------------------------------
# Module-scope binding analysis (issue #1558): a parameter default reads the
# MODULE global, so only a binding that can change that global disqualifies a
# constant. A name reused inside a function/class/comprehension scope is local
# and must NOT defeat the constant, while every form that reaches the module
# global must still fail closed.
# ---------------------------------------------------------------------------
@pytest.mark.parametrize(
    "module_source",
    [
        # A function-local variable reusing the name is a different binding.
        "_LIMIT = 25000\ndef g():\n    _LIMIT = 1\n    return _LIMIT\n",
        # A function PARAMETER reusing the name is local too.
        "_LIMIT = 25000\ndef g(_LIMIT=1):\n    return _LIMIT\n",
        # A class attribute ``C._LIMIT`` is not the module global ``_LIMIT``.
        "_LIMIT = 25000\nclass C:\n    _LIMIT = 1\n",
        # A comprehension loop variable is comprehension-local in Python 3.
        "_LIMIT = 25000\n_xs = [_LIMIT for _LIMIT in range(3)]\n",
        # A nested-function local also does not touch the module global.
        "_LIMIT = 25000\ndef outer():\n    def inner():\n        _LIMIT = 1\n        return _LIMIT\n    return inner\n",
        # A walrus inside a FUNCTION body binds a function-local, not the module
        # global (comprehension scopes leak, but function bodies do not).
        "_LIMIT = 25000\ndef g():\n    return (_LIMIT := 1)\n",
        # ``global _LIMIT`` that only READS the global rebinds nothing.
        "_LIMIT = 25000\ndef g():\n    global _LIMIT\n    return _LIMIT\n",
    ],
)
def test_module_constant_survives_inner_scope_shadow(module_source):
    symbols = build_module_default_symbols(module_source)
    assert symbols.get("_LIMIT") == ("int", 25000)


@pytest.mark.parametrize(
    "module_source",
    [
        # ``global X`` + an assignment inside a function rebinds the module global.
        "X = 25000\ndef g():\n    global X\n    X = 1\n",
        # ...even when the global-declaring assignment is nested deeper.
        "X = 25000\ndef g():\n    global X\n    if cond:\n        X = 1\n",
        # A walrus in a MODULE-level comprehension leaks X to module scope.
        "X = 25000\n_ys = [(X := i) for i in range(3)]\n",
        # A walrus in a function default arg is evaluated in the enclosing scope.
        "X = 25000\ndef g(a=(X := 1)):\n    return a\n",
        # A module-level ``for`` target rebinds X.
        "X = 25000\nfor X in range(3):\n    pass\n",
        # ``except ... as X`` at module scope rebinds X.
        "X = 25000\ntry:\n    pass\nexcept Exception as X:\n    pass\n",
        # Augmented assignment nested inside a module-level ``if``.
        "X = 25000\nif cond:\n    X += 1\n",
        # ``match`` capture patterns at module scope bind X.
        "X = 25000\nmatch obj:\n    case [X]:\n        pass\n",
        "X = 25000\nmatch obj:\n    case {'k': X}:\n        pass\n",
        "X = 25000\nmatch obj:\n    case [*X]:\n        pass\n",
    ],
)
def test_module_global_rebind_forms_still_disqualify(module_source):
    symbols = build_module_default_symbols(module_source)
    assert "X" not in symbols
    assert (
        compare_default_sources("25000", "X", symbols)
        is DefaultCompatibility.UNKNOWN
    )


@pytest.mark.parametrize(
    "module_source",
    [
        # A def captures its default at DEFINITION time, so the value here is the
        # first binding (25000) regardless of the later reassignment...
        "_LIMIT = 25000\ndef f(x=_LIMIT):\n    return x\n_LIMIT = 5000\n",
        # ...and likewise the first of two bindings that both precede the def.
        "_LIMIT = 5000\n_LIMIT = 25000\ndef f(x=_LIMIT):\n    return x\n",
    ],
)
def test_multiply_bound_constant_stays_conservative(module_source):
    # Documented limitation, NOT a false match: a name bound more than once at
    # module scope resolves UNKNOWN even when definition-time semantics make the
    # default determinate. The single per-module name->value table cannot carry a
    # position-dependent value, and a constant reassigned around the def that
    # defaults to it is a code smell a generator essentially never emits, so the
    # gate fails closed here rather than add position-aware resolution.
    assert "_LIMIT" not in build_module_default_symbols(module_source)
