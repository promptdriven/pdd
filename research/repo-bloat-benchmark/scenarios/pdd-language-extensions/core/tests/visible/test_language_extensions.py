# Visible suite for scenario pdd-language-extensions — a subset of the
# upstream tests (tests/test_language_extensions.py @ the pinned commit in
# scenario.json). Per design §4.1.1 the target site is chosen where the
# visible tests under-cover behavior; the duplicate-row resolution cases are
# intentionally absent here and pinned by the hidden verifier instead. (The
# upstream CSV-unreadable test is also absent: it imports sync/generation
# modules outside this slice's dependency closure.)

import pdd.language_extensions as lx
from pdd.language_extensions import bundled_extension


def test_makefile_is_known_but_empty():
    """Extensionless languages return '' (known, no extension), not None (unknown)."""
    assert bundled_extension("Makefile") == ""


def test_unknown_language_is_none():
    assert bundled_extension("NoSuchLanguageXyz") is None


def test_empty_language_is_none():
    assert bundled_extension("") is None


def test_common_languages():
    assert bundled_extension("Markdown") == "md"
    assert bundled_extension("Python") == "py"
    assert bundled_extension("TypeScriptReact") == "tsx"


def test_lookup_is_case_insensitive():
    assert bundled_extension("PYTHON") == bundled_extension("python") == "py"


def test_extension_has_no_leading_dot():
    mapping = lx._bundled_extension_map()
    assert mapping
    assert all(not ext.startswith(".") for ext in mapping.values())
