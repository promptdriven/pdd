"""Compatibility language lookup backed by the protected bundled registry."""

# AUTO-HEAL PROTECTED-MUTATION CANARY: SELECT GET_LANGUAGE; DO NOT MERGE

import csv
from pathlib import Path

from pdd.sync_core import LanguageRegistry, LanguageRegistryError

_LEGACY_UNKNOWN_EXTENSIONS = {".prompt"}


def _normalize_extension(extension: str) -> str:
    normalized = extension.strip().casefold()
    if normalized and not normalized.startswith("."):
        normalized = "." + normalized
    return normalized


def _legacy_first_match(extension: str) -> str:
    if extension in _LEGACY_UNKNOWN_EXTENSIONS:
        return ""
    csv_path = Path(__file__).parent / "data" / "language_format.csv"
    try:
        with csv_path.open(newline="", encoding="utf-8") as handle:
            for row in csv.DictReader(handle):
                row_extension = _normalize_extension(row.get("extension") or "")
                if row_extension == extension:
                    return (row.get("language") or "").strip()
    except (OSError, csv.Error):
        return ""
    return ""


def get_language(extension: str) -> str:
    """
    Determines the programming language associated with a given file extension.

    Args:
        extension (str): The file extension to look up.

    Returns:
        str: The name of the programming language or an empty string if not found.

    Raises:
        ValueError: If PDD_PATH environment variable is not set.
    """
    normalized = _normalize_extension(extension)
    if not normalized:
        return ""
    try:
        return LanguageRegistry.bundled().resolve_extension(normalized).display_name
    except LanguageRegistryError:
        return _legacy_first_match(normalized)
