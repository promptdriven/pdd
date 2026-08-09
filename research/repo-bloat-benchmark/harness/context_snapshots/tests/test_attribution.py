"""Tests for content attribution against a materialized tree."""

import pytest

from harness.context_snapshots.attribution import (
    Attribution,
    TreeIndex,
    reconcile_with_usage,
)

CORE_CONTENT = '''\
def slice_page(items, page, page_size):
    """Return one page of items using half-open slicing semantics."""
    start_index_for_requested_page = page * page_size
    return items[start_index_for_requested_page:start_index_for_requested_page + page_size]
'''

DISTRACTOR_CONTENT = '''\
def format_ledger_totals_for_export(ledger_rows, currency_code):
    """Format ledger totals for the quarterly export pipeline."""
    formatted_ledger_export_rows = [f"{row.total:.2f} {currency_code}" for row in ledger_rows]
    return formatted_ledger_export_rows
'''


@pytest.fixture()
def tree(tmp_path):
    (tmp_path / "src" / "pkg").mkdir(parents=True)
    (tmp_path / "src" / "pkg" / "pagination.py").write_text(CORE_CONTENT)
    (tmp_path / "src" / "pkg" / "ledger_formatter.py").write_text(DISTRACTOR_CONTENT)
    return tmp_path


@pytest.fixture()
def index(tree):
    return TreeIndex(tree, distractor_paths=["src/pkg/ledger_formatter.py"])


def test_distractor_lines_attributed(index):
    request_text = (
        "Here is a file I read:\n" + DISTRACTOR_CONTENT + "\nWhat should I do next?"
    )
    result = index.classify_text(request_text)
    assert result.distractor_lines > 0
    assert result.distractor_tokens > 0
    assert result.core_lines == 0
    assert "src/pkg/ledger_formatter.py" in result.distractor_files


def test_core_lines_attributed(index):
    result = index.classify_text(CORE_CONTENT)
    assert result.core_lines > 0
    assert result.distractor_lines == 0
    assert "src/pkg/pagination.py" in result.core_files


def test_unmatched_text_is_unknown(index):
    result = index.classify_text(
        "The assistant reasons at length about pagination strategies in prose."
    )
    assert result.distractor_lines == 0
    assert result.core_lines == 0
    assert result.unknown_tokens > 0


def test_short_lines_ignored(index):
    result = index.classify_text("return x\n\npass\n")
    assert result.total_tokens == 0


def test_ambiguous_lines_not_counted_as_distractor(tmp_path):
    shared = "shared_helper_line_that_is_long_enough_to_index = compute_shared_value()\n"
    (tmp_path / "core.py").write_text(shared)
    (tmp_path / "extra.py").write_text(shared)
    index = TreeIndex(tmp_path, distractor_paths=["extra.py"])
    result = index.classify_text(shared)
    assert result.distractor_tokens == 0
    assert result.ambiguous_lines == 1


def test_distractor_share(index):
    text = DISTRACTOR_CONTENT + CORE_CONTENT
    result = index.classify_text(text)
    assert 0.0 < result.distractor_share < 1.0


def test_reconcile_caps_at_provider_usage():
    attribution = Attribution(distractor_tokens=900.0, core_tokens=300.0)
    # Provider says the request was only 600 tokens; estimates must scale down.
    reconciled = reconcile_with_usage(attribution, provider_input_tokens=600)
    assert reconciled["reconciled_against_usage"]
    assert reconciled["distractor_context_tokens"] <= 600
    assert reconciled["distractor_context_share"] <= 1.0
    assert reconciled["raw_estimate_tokens"] == 900.0


def test_reconcile_without_usage_flags_itself():
    attribution = Attribution(distractor_tokens=100.0)
    reconciled = reconcile_with_usage(attribution, provider_input_tokens=None)
    assert not reconciled["reconciled_against_usage"]
    assert reconciled["distractor_context_tokens"] == 100.0
