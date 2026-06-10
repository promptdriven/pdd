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
    ],
)
def test_semantic_type_aliases_are_compatible(left, right):
    assert annotations_compatible(left, right)


@pytest.mark.parametrize(
    ("left", "right"),
    [
        ("List[str]", "Dict[str, str]"),
        ("Optional[str]", "str"),
        ("mytypes.Set", "Set[str]"),
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
