"""Tests for pdd.language_extensions — the single bundled-CSV extension source.

Guards the issue #551 invariants: the sync side and the generation side resolve
the same extension for a language, and the duplicate YAML rows resolve
deterministically (first match wins).
"""

import pdd.language_extensions as lx
from pdd.language_extensions import bundled_extension


def test_yaml_first_match_is_yml():
    """language_format.csv lists YAML twice (.yml before .yaml); first match wins."""
    assert bundled_extension("YAML") == "yml"
    assert bundled_extension("yaml") == "yml"


def test_makefile_is_known_but_empty():
    """Extensionless languages return '' (known, no extension), not None (unknown)."""
    assert bundled_extension("Makefile") == ""


def test_unknown_language_is_none():
    assert bundled_extension("NoSuchLanguageXyz") is None


def test_common_languages():
    assert bundled_extension("Markdown") == "md"
    assert bundled_extension("Python") == "py"
    assert bundled_extension("TypeScriptReact") == "tsx"


def test_csv_unreadable_keeps_sync_and_generation_aligned(monkeypatch, tmp_path):
    """If the bundled CSV can't be read, sync and generation must still agree.

    bundled_extension() then returns None for every language, and BOTH sync's
    get_extension and construct_paths' offline fallback defer to the same
    BUILTIN_EXT_MAP — so Markdown resolves to 'md' on the sync side instead of
    the raw '.markdown' that previously diverged from generation and reopened the
    #551 loop. The lru_cache is cleared around the patch so this stays isolated.
    """
    from pdd.sync_determine_operation import get_extension as sync_ext
    from pdd.construct_paths import BUILTIN_EXT_MAP

    monkeypatch.setattr(lx, "_CSV_PATH", tmp_path / "does-not-exist.csv")
    lx._bundled_extension_map.cache_clear()
    try:
        assert bundled_extension("Markdown") is None  # CSV is gone
        # sync now defers to BUILTIN_EXT_MAP, matching what generation writes.
        assert sync_ext("Markdown") == BUILTIN_EXT_MAP["markdown"].lstrip(".") == "md"
        assert sync_ext("YAML") == BUILTIN_EXT_MAP["yaml"].lstrip(".")
    finally:
        lx._bundled_extension_map.cache_clear()  # restore real CSV for other tests
