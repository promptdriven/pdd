"""Tests for failure classification used by failure-aware fix retries."""

import pytest

from pdd.failure_classification import (
    FailureKind,
    classify_failure,
    extract_failure_signature,
    failure_classification_hint,
    format_signature_hint,
)


@pytest.mark.parametrize(
    "text,expected",
    [
        ("SyntaxError: invalid syntax", FailureKind.SYNTAX_IMPORT),
        ("IndentationError: unexpected indent", FailureKind.SYNTAX_IMPORT),
        ("ModuleNotFoundError: No module named 'foo'", FailureKind.SYNTAX_IMPORT),
        ("ImportError: cannot import name 'x'", FailureKind.SYNTAX_IMPORT),
        ("ERROR collecting tests/test_foo.py\nImportError while loading", FailureKind.SYNTAX_IMPORT),
        ("E   ImportError: bad", FailureKind.SYNTAX_IMPORT),
    ],
)
def test_classify_syntax_import(text: str, expected: FailureKind) -> None:
    assert classify_failure(text) == expected


@pytest.mark.parametrize(
    "text",
    [
        "FAILED test_x.py::test_a - AssertionError: assert 1 == 2",
        "E   assert False",
        "AssertionError: assert 3 == 4",
    ],
)
def test_classify_assertion_logic(text: str) -> None:
    assert classify_failure(text) == FailureKind.ASSERTION_LOGIC


@pytest.mark.parametrize(
    "text",
    [
        "+++ Timeout +++",
        "timed out after 30 seconds",
        "pytest-timeout",
        "FAILED test_x - Failed: Timeout (>10.0s)",
    ],
)
def test_classify_timeout_flaky(text: str) -> None:
    assert classify_failure(text) == FailureKind.TIMEOUT_FLAKY


def test_classify_timeout_before_syntax_keyword() -> None:
    """Timeout patterns should win over generic 'Error' substrings."""
    text = "Error: test timed out after 5s\nSyntaxError would not apply"
    assert classify_failure(text) == FailureKind.TIMEOUT_FLAKY


def test_extract_failure_signature_stable() -> None:
    out = '''File "src/foo.py", line 12, in bar
    x = 1 +
SyntaxError: invalid syntax'''
    sig = extract_failure_signature(out)
    assert "SyntaxError" in sig
    assert "foo.py" in sig
    assert "12" in sig


def test_extract_failure_signature_empty() -> None:
    assert extract_failure_signature("") == ""


def test_failure_classification_hint_nonempty() -> None:
    h = failure_classification_hint(FailureKind.SYNTAX_IMPORT)
    assert "syntax" in h.lower() or "import" in h.lower()


def test_failure_kind_has_multishot_values() -> None:
    """Prompt change: multi-shot controller sets budget/infra kinds programmatically."""
    assert FailureKind.BUDGET_TRUNCATED.value == "budget_truncated"
    assert FailureKind.INFRASTRUCTURE_ERROR.value == "infrastructure_error"


def test_failure_classification_hint_budget_truncated() -> None:
    assert failure_classification_hint(FailureKind.BUDGET_TRUNCATED) == (
        "shot stopped — per-shot or total budget exhausted; "
        "increase budget limits or reduce per-shot work scope"
    )


def test_failure_classification_hint_infrastructure_error() -> None:
    assert failure_classification_hint(FailureKind.INFRASTRUCTURE_ERROR) == (
        "shot stopped by infrastructure failure (crash, timeout, OOM); "
        "check infrastructure health and retry"
    )


def test_failure_classification_hint_covers_all_kinds() -> None:
    """Every FailureKind must yield a non-empty hint."""
    for kind in FailureKind:
        assert failure_classification_hint(kind).strip()


def test_budget_and_infra_not_derived_from_text() -> None:
    """classify_failure must never return the programmatic-only kinds from text."""
    assert classify_failure("budget exhausted") != FailureKind.BUDGET_TRUNCATED
    assert classify_failure("infrastructure OOM crash") != FailureKind.INFRASTRUCTURE_ERROR




import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

def test_extract_failure_signature_exception_only() -> None:
    sig = extract_failure_signature("ValueError: something bad happened")
    assert "ValueError" in sig


def test_extract_failure_signature_file_line_no_exception() -> None:
    sig = extract_failure_signature('  File "a/b.py", line 42, in func\n    do()')
    assert "b.py" in sig and "42" in sig


def test_extract_failure_signature_fallback_normalizes_whitespace() -> None:
    text = "weird   output\n\twith\n\nbreaks"
    sig = extract_failure_signature(text)
    assert "  " not in sig
    assert "\n" not in sig and "\t" not in sig
    assert sig  # non-empty fallback


def test_extract_failure_signature_stable_across_calls() -> None:
    text = 'File "x/y.py", line 7, in z\nAssertionError: nope'
    assert extract_failure_signature(text) == extract_failure_signature(text)


def test_extract_failure_signature_combines_exception_and_location() -> None:
    text = 'File "pkg/mod.py", line 99, in fn\nKeyError: \'k\''
    sig = extract_failure_signature(text)
    assert "KeyError" in sig and "pkg/mod.py" in sig and "99" in sig


def test_format_signature_hint_empty() -> None:
    out = format_signature_hint("")
    assert out and "could not" in out.lower()


def test_format_signature_hint_short_passthrough() -> None:
    assert format_signature_hint("Foo:bar.py:1") == "Foo:bar.py:1"


def test_format_signature_hint_truncates_long() -> None:
    long = "x" * 500
    out = format_signature_hint(long)
    assert len(out) <= 120
    assert out.endswith("...")


def test_format_signature_hint_boundary_120() -> None:
    s = "y" * 120
    assert format_signature_hint(s) == s  # exactly 120 not truncated


def test_classify_empty_and_whitespace() -> None:
    assert classify_failure("") == FailureKind.ASSERTION_LOGIC
    assert classify_failure("   \n\t  ") == FailureKind.ASSERTION_LOGIC


def test_classify_deadline_exceeded() -> None:
    assert classify_failure("Deadline exceeded while waiting") == FailureKind.TIMEOUT_FLAKY


def test_classify_tab_error_is_syntax_import() -> None:
    assert classify_failure("TabError: inconsistent use of tabs") == FailureKind.SYNTAX_IMPORT


def test_failure_kind_string_values() -> None:
    assert FailureKind.SYNTAX_IMPORT.value == "syntax_import"
    assert FailureKind.ASSERTION_LOGIC.value == "assertion_logic"
    assert FailureKind.TIMEOUT_FLAKY.value == "timeout_flaky"


def test_failure_classification_hint_timeout_mentions_stability() -> None:
    h = failure_classification_hint(FailureKind.TIMEOUT_FLAKY).lower()
    assert "timeout" in h or "flaky" in h or "stabiliz" in h


def test_failure_classification_hint_assertion_logic_nonempty() -> None:
    assert failure_classification_hint(FailureKind.ASSERTION_LOGIC).strip()