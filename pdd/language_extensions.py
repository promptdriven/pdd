"""Single source of truth for canonical file extensions.

Both ``pdd.sync_determine_operation.get_extension`` (which decides the paths
sync *expects*) and ``pdd.construct_paths``' offline fallback (which decides
the paths generation *writes*) resolve extensions through this module, reading
the package-bundled ``data/language_format.csv`` without requiring ``PDD_PATH``.

Keeping a single reader prevents the two sides from diverging for a language —
e.g. sync expecting ``.yml`` while generation writes ``.yaml`` — which is the
PDD_PATH-unset relapse of issue #551.
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

    Languages are lower-cased and the extension is normalised to drop a leading
    dot (``.yml`` -> ``yml``); a language with no extension (e.g. ``Makefile``)
    maps to ``""``. The first matching row wins, so the duplicate YAML rows
    (``.yml`` before ``.yaml``) deterministically resolve to ``yml`` — do not
    reorder those rows without updating the issue #551 expectations.

    Parsed once and cached: the CSV is static package data.
    """
    mapping: Dict[str, str] = {}
    try:
        with open(_CSV_PATH, newline="", encoding="utf-8") as handle:
            for row in csv.DictReader(handle):
                language = (row.get("language") or "").strip().lower()
                if language and language not in mapping:  # first match wins (issue #551)
                    mapping[language] = (row.get("extension") or "").strip().lstrip(".")
    except (OSError, csv.Error) as exc:
        # Observable, not silent: if the bundled CSV cannot be read, callers
        # fall back to their hard-coded maps, which can reintroduce issue #551.
        logger.debug("Could not read bundled language CSV at %s: %s", _CSV_PATH, exc)
    return dict(mapping)


def bundled_extension(language: str) -> Optional[str]:
    """Return the canonical extension (without a leading dot) for *language*.

    Returns ``""`` for a known extensionless language (e.g. ``Makefile``) and
    ``None`` when the language is absent from the bundled CSV, so callers can
    tell "known, no extension" apart from "unknown" and fall back accordingly.
    ``PDD_PATH``-independent.
    """
    if not language:
        return None
    return _bundled_extension_map().get(language.lower())
