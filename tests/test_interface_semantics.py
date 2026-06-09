import pytest

from pdd.interface_semantics import annotations_compatible


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
