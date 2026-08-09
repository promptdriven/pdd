"""Single source of truth for canonical file extensions.

Both the sync side (which decides the paths sync *expects*) and the
generation side (which decides the paths generation *writes*) resolve
extensions through this module, reading the package-bundled
``data/language_format.csv``.

Dependency-sliced from ``pdd/language_extensions.py`` (upstream pinned
commit in ``scenario.json``); comments and docstrings were normalized during
slicing — see ``seed.patch`` for the recorded transform.
"""

from __future__ import annotations

import csv
import logging
from functools import lru_cache
from pathlib import Path
from typing import Dict, Optional

logger = logging.getLogger(__name__)

_CSV_PATH = Path(__file__).parent / "data" / "language_format.csv"


@lru_cache(maxsize=1)
def _bundled_extension_map() -> Dict[str, str]:
    """Parse the bundled ``language_format.csv`` into ``{language: extension}``.

    Languages are lower-cased and the extension is normalised to drop a
    leading dot (``.yml`` -> ``yml``); a language with no extension (e.g.
    ``Makefile``) maps to ``""``.

    Parsed once and cached: the CSV is static package data.
    """
    mapping: Dict[str, str] = {}
    try:
        with open(_CSV_PATH, newline="", encoding="utf-8") as handle:
            for row in csv.DictReader(handle):
                language = (row.get("language") or "").strip().lower()
                if language:
                    mapping[language] = (row.get("extension") or "").strip().lstrip(".")
    except (OSError, csv.Error) as exc:
        # Observable, not silent: if the bundled CSV cannot be read, callers
        # fall back to their hard-coded maps.
        logger.debug("Could not read bundled language CSV at %s: %s", _CSV_PATH, exc)
    return dict(mapping)


def bundled_extension(language: str) -> Optional[str]:
    """Return the canonical extension (without a leading dot) for *language*.

    Returns ``""`` for a known extensionless language (e.g. ``Makefile``) and
    ``None`` when the language is absent from the bundled CSV, so callers can
    tell "known, no extension" apart from "unknown" and fall back accordingly.
    """
    if not language:
        return None
    return _bundled_extension_map().get(language.lower())
