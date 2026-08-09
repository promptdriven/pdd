"""Tests for vocabulary harvesting."""

from harness.distractors.vocabulary import (
    harvest_vocabulary,
    split_identifier,
)


def test_split_identifier_snake_and_camel():
    assert split_identifier("format_ledger_totals") == ["format", "ledger", "totals"]
    assert split_identifier("FormatLedgerTotals") == ["format", "ledger", "totals"]
    assert split_identifier("x") == []  # too short


def test_harvest_vocabulary(tmp_path):
    (tmp_path / "mod.py").write_text(
        "def paginate_ledger_records(ledger_records):\n"
        "    exported_ledger_total = sum(ledger_records)\n"
        "    return exported_ledger_total\n"
    )
    vocabulary = harvest_vocabulary(tmp_path)
    assert vocabulary.words["ledger"] >= 3
    assert "paginate" in vocabulary.words
    top = vocabulary.top_words(3)
    assert top[0] == "ledger"


def test_overlap_fraction(tmp_path):
    (tmp_path / "mod.py").write_text("def paginate_ledger(): pass\n")
    vocabulary = harvest_vocabulary(tmp_path)
    high = vocabulary.overlap_fraction(["ledger_paginate_helper"])
    low = vocabulary.overlap_fraction(["frobnicate_wobble"])
    assert high > 0.5
    assert low == 0.0


def test_unparseable_file_skipped(tmp_path):
    (tmp_path / "broken.py").write_text("def broken(:\n")
    vocabulary = harvest_vocabulary(tmp_path)
    assert vocabulary.words == {}
