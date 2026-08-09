# Hidden verifier for scenario pdd-failure-classification (design §4.4).
#
# Pins the precedence contract the visible suite deliberately leaves open:
# a log that matches BOTH a timeout marker and a syntax/import marker is a
# timeout (timeouts abort runs mid-import all the time; retrying a "syntax
# fix" on them burns budget). This tree is physically separate from the
# core and must never enter the agent sandbox.

from pdd.failure_classification import FailureKind, classify_failure


def test_timeout_wins_over_import_marker():
    text = "ERROR collecting tests/test_slow.py\ntest run timed out after 30 seconds"
    assert classify_failure(text) == FailureKind.TIMEOUT_FLAKY


def test_timeout_wins_over_module_not_found():
    text = (
        "ModuleNotFoundError: No module named 'heavy_dep'\n"
        "FAILED test_x - Failed: Timeout (>10.0s)"
    )
    assert classify_failure(text) == FailureKind.TIMEOUT_FLAKY


def test_deadline_exceeded_wins_over_syntax_error():
    text = "Error: deadline exceeded while importing\nSyntaxError would not apply"
    assert classify_failure(text) == FailureKind.TIMEOUT_FLAKY


def test_pure_import_error_still_syntax_import():
    assert (
        classify_failure("ImportError: cannot import name 'x'")
        == FailureKind.SYNTAX_IMPORT
    )


def test_pure_timeout_still_timeout():
    assert classify_failure("timed out after 5 seconds") == FailureKind.TIMEOUT_FLAKY


def test_pure_assertion_still_assertion():
    assert classify_failure("E   assert False") == FailureKind.ASSERTION_LOGIC
