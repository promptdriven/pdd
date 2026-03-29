"""Tests for failure classification used by failure-aware fix retries."""

import pytest

from pdd.failure_classification import (
    FailureKind,
    classify_failure,
    extract_failure_signature,
    failure_classification_hint,
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

