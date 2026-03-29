"""Failure-aware retry behavior in fix_error_loop."""

from unittest.mock import patch

import pytest

from pdd.fix_error_loop import fix_error_loop


@pytest.fixture
def setup_files(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    (tmp_path / ".pdd").mkdir()
    code_dir = tmp_path / "pdd"
    code_dir.mkdir()
    test_dir = tmp_path / "tests"
    test_dir.mkdir()

    code_file = code_dir / "mod.py"
    code_file.write_text("x = (\n")
    test_file = test_dir / "test_mod.py"
    test_file.write_text(
        "def test_x():\n"
        "    import mod\n"
        "    assert mod.x is not None\n"
    )
    verify_file = tmp_path / "verify.py"
    verify_file.write_text("print('ok')")

    return {
        "code_file": code_file,
        "test_file": test_file,
        "verify_file": verify_file,
        "error_log": tmp_path / "error_log.txt",
    }


SYNTAX_OUTPUT = """
File "pdd/mod.py", line 1
    x = (
        ^
SyntaxError: invalid syntax
"""

ASSERT_OUTPUT = """
FAILED tests/test_mod.py::test_x - AssertionError: assert 1 == 2
"""

TIMEOUT_OUTPUT = """
FAILED tests/test_mod.py::test_x - Failed: Timeout (>1.0s)
=== 1 failed in 2.0s ===
"""


@patch("pdd.fix_error_loop.fix_errors_from_unit_tests")
@patch("pdd.fix_error_loop.run_pytest_on_file")
def test_failure_aware_syntax_stops_after_one_attempt_when_signature_unchanged(
    mock_pytest, mock_fix, setup_files
):
    """Same syntax/import signature after a fix attempt → do not burn max_attempts."""
    files = setup_files
    mock_pytest.return_value = (1, 0, 0, SYNTAX_OUTPUT)
    mock_fix.return_value = (
        True,
        True,
        files["test_file"].read_text(),
        'x = (\n  # still broken',
        "analysis",
        0.01,
        "mock-model",
    )

    success, _, _, attempts, cost, model = fix_error_loop(
        unit_test_file=str(files["test_file"]),
        code_file=str(files["code_file"]),
        prompt_file="dummy_prompt.txt",
        prompt="prompt",
        verification_program=str(files["verify_file"]),
        strength=0.5,
        temperature=0.0,
        max_attempts=5,
        budget=10.0,
        error_log_file=str(files["error_log"]),
        agentic_fallback=False,
        failure_aware_retries=True,
    )

    assert success is False
    assert attempts == 1
    assert mock_fix.call_count == 1


@patch("pdd.fix_error_loop.fix_errors_from_unit_tests")
@patch("pdd.fix_error_loop.run_pytest_on_file")
def test_failure_aware_disabled_allows_multiple_syntax_attempts(
    mock_pytest, mock_fix, setup_files
):
    files = setup_files
    mock_pytest.return_value = (1, 0, 0, SYNTAX_OUTPUT)
    mock_fix.return_value = (
        True,
        True,
        files["test_file"].read_text(),
        "still bad",
        "analysis",
        0.01,
        "mock-model",
    )

    _, _, _, attempts, _, _ = fix_error_loop(
        unit_test_file=str(files["test_file"]),
        code_file=str(files["code_file"]),
        prompt_file="dummy_prompt.txt",
        prompt="prompt",
        verification_program=str(files["verify_file"]),
        strength=0.5,
        temperature=0.0,
        max_attempts=3,
        budget=10.0,
        error_log_file=str(files["error_log"]),
        agentic_fallback=False,
        failure_aware_retries=False,
    )

    assert attempts == 3
    assert mock_fix.call_count == 3


@patch("pdd.fix_error_loop.fix_errors_from_unit_tests")
@patch("pdd.fix_error_loop.run_pytest_on_file")
def test_failure_aware_assertion_uses_max_attempts(mock_pytest, mock_fix, setup_files):
    """Assertion/logic failures are not cut short by failure-aware logic."""
    files = setup_files
    mock_pytest.return_value = (1, 0, 0, ASSERT_OUTPUT)
    mock_fix.return_value = (
        True,
        True,
        files["test_file"].read_text(),
        files["code_file"].read_text(),
        "analysis",
        0.01,
        "mock-model",
    )

    _, _, _, attempts, _, _ = fix_error_loop(
        unit_test_file=str(files["test_file"]),
        code_file=str(files["code_file"]),
        prompt_file="dummy_prompt.txt",
        prompt="prompt",
        verification_program=str(files["verify_file"]),
        strength=0.5,
        temperature=0.0,
        max_attempts=4,
        budget=10.0,
        error_log_file=str(files["error_log"]),
        agentic_fallback=False,
        failure_aware_retries=True,
    )

    assert attempts == 4
    assert mock_fix.call_count == 4


@patch("pdd.fix_error_loop.fix_errors_from_unit_tests")
@patch("pdd.fix_error_loop.run_pytest_on_file")
def test_failure_aware_timeout_stops_after_two_without_improvement(
    mock_pytest, mock_fix, setup_files
):
    files = setup_files
    mock_pytest.return_value = (1, 0, 0, TIMEOUT_OUTPUT)
    mock_fix.return_value = (
        True,
        True,
        files["test_file"].read_text(),
        files["code_file"].read_text(),
        "analysis",
        0.01,
        "mock-model",
    )

    _, _, _, attempts, _, _ = fix_error_loop(
        unit_test_file=str(files["test_file"]),
        code_file=str(files["code_file"]),
        prompt_file="dummy_prompt.txt",
        prompt="prompt",
        verification_program=str(files["verify_file"]),
        strength=0.5,
        temperature=0.0,
        max_attempts=10,
        budget=10.0,
        error_log_file=str(files["error_log"]),
        agentic_fallback=False,
        failure_aware_retries=True,
    )

    assert attempts == 2
    assert mock_fix.call_count == 2


@patch("pdd.fix_error_loop.fix_errors_from_unit_tests")
@patch("pdd.fix_error_loop.run_pytest_on_file")
def test_fix_errors_receives_failure_classification_hint(mock_pytest, mock_fix, setup_files):
    files = setup_files
    mock_pytest.return_value = (1, 0, 0, SYNTAX_OUTPUT)
    mock_fix.return_value = (
        True,
        True,
        files["test_file"].read_text(),
        "fixed",
        "analysis",
        0.01,
        "mock-model",
    )

    fix_error_loop(
        unit_test_file=str(files["test_file"]),
        code_file=str(files["code_file"]),
        prompt_file="dummy_prompt.txt",
        prompt="prompt",
        verification_program=str(files["verify_file"]),
        strength=0.5,
        temperature=0.0,
        max_attempts=1,
        budget=10.0,
        error_log_file=str(files["error_log"]),
        agentic_fallback=False,
        failure_aware_retries=True,
    )

    kwargs = mock_fix.call_args.kwargs
    assert "failure_classification" in kwargs
    assert "syntax" in kwargs["failure_classification"].lower() or "import" in kwargs[
        "failure_classification"
    ].lower()

