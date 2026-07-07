# Hidden verifier for scenario pdd-language-extensions (design §4.4).
#
# Pins the duplicate-row contract the visible suite deliberately leaves
# open: when a language appears in language_format.csv more than once, the
# FIRST row wins deterministically, so the sync side and the generation side
# agree on one canonical extension. This tree is physically separate from
# the core and must never enter the agent sandbox.

import csv

import pdd.language_extensions as lx
from pdd.language_extensions import bundled_extension


def test_yaml_resolves_to_first_row_extension():
    assert bundled_extension("YAML") == "yml"
    assert bundled_extension("yaml") == "yml"


def test_every_duplicated_language_resolves_to_its_first_row():
    firsts = {}
    with open(lx._CSV_PATH, newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            language = (row.get("language") or "").strip().lower()
            if language and language not in firsts:
                firsts[language] = (row.get("extension") or "").strip().lstrip(".")
    mapping = lx._bundled_extension_map()
    assert mapping == firsts


def test_singleton_languages_unchanged():
    assert bundled_extension("Python") == "py"
    assert bundled_extension("Makefile") == ""
    assert bundled_extension("NoSuchLanguageXyz") is None
