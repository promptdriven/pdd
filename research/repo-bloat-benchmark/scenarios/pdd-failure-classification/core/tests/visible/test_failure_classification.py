# Visible suite for scenario pdd-failure-classification — a subset of the
# upstream tests (tests/test_failure_classification.py @ the pinned commit in
# scenario.json). Per design §4.1.1 the target site is chosen where the
# visible tests under-cover behavior; the mixed-marker precedence cases are
# intentionally absent here and pinned by the hidden verifier instead.

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


def test_classify_empty_is_assertion_logic() -> None:
    assert classify_failure("") == FailureKind.ASSERTION_LOGIC
    assert classify_failure("   \n ") == FailureKind.ASSERTION_LOGIC


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


def test_hints_cover_every_kind() -> None:
    for kind in FailureKind:
        assert failure_classification_hint(kind)


def test_format_signature_hint_truncates() -> None:
    assert format_signature_hint("") == "(could not locate a stable error position)"
    long_sig = "x" * 200
    assert len(format_signature_hint(long_sig)) == 120
