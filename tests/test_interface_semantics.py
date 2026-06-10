import pytest

from pdd.interface_semantics import (
    annotations_compatible,
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
