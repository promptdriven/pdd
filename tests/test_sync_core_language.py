"""Exhaustive conformance tests for every bundled language registry row."""

import csv
from pathlib import Path

import pytest

from pdd.sync_core import LanguageRegistry, LanguageRegistryError


CSV_PATH = Path(__file__).parents[1] / "pdd/data/language_format.csv"


def _rows():
    with CSV_PATH.open(newline="", encoding="utf-8") as handle:
        return tuple(csv.DictReader(handle))


@pytest.mark.parametrize("row", _rows(), ids=lambda row: row["language"] + row["extension"])
def test_every_bundled_row_resolves_by_explicit_language(row) -> None:
    registry = LanguageRegistry.bundled()
    spec = registry.resolve_alias(row["language"])
    extension = row["extension"].casefold()
    assert extension in spec.extensions
    if extension:
        assert registry.resolve_extension(
            extension, explicit_language=row["language"]
        ) == spec
    declared_roles = {role for role in row["outputs"].split("|") if role}
    assert declared_roles.issubset(spec.output_roles)


@pytest.mark.parametrize("extension", [".sh", ".pl", ".m", ".prompt"])
def test_ambiguous_extension_never_selects_first_row(extension) -> None:
    with pytest.raises(LanguageRegistryError, match="ambiguous or unknown"):
        LanguageRegistry.bundled().resolve_extension(extension)


def test_duplicate_language_rows_merge_all_extensions() -> None:
    yaml = LanguageRegistry.bundled().resolve_alias("YAML")
    assert yaml.extensions == (".yaml", ".yml")


def test_registry_digest_is_deterministic() -> None:
    assert LanguageRegistry.bundled().digest() == LanguageRegistry.bundled().digest()
