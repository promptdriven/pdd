import json
import os
from pathlib import Path
from unittest.mock import MagicMock

import pytest

from pdd.fix_error_loop import fix_error_loop

# --- Test Data ---

PROMPT_CONTENT = "Test prompt"
BUGGY_CODE_CONTENT = "def buggy_function():\n    return 1/0"
FIXED_CODE_CONTENT = "def buggy_function():\n    return 1"
MAIN_CONTENT = "from src.utils import buggy_function; print(buggy_function())"
TEST_CONTENT_FAILING = "import unittest\nfrom src import utils\n\nclass TestBug(unittest.TestCase):\n    def test_bug(self):\n        utils.buggy_function()"


@pytest.fixture
def tmp_project(tmp_path):
    """Sets up a temporary project directory for each test."""
    project_root = tmp_path
    (project_root / "prompts").mkdir()
    (project_root / "src").mkdir()
    (project_root / "tests").mkdir()

    (project_root / "prompts" / "utils_python.prompt").write_text(PROMPT_CONTENT)
    (project_root / "src" / "utils.py").write_text(BUGGY_CODE_CONTENT)
    (project_root / "main.py").write_text(MAIN_CONTENT)
    (project_root / "tests" / "test_utils.py").write_text(TEST_CONTENT_FAILING)
    (project_root / "error.log").touch()

    return project_root

# --- Test Cases ---

def test_fallback_is_triggered_on_failure(tmp_project, monkeypatch):
    """
    Case 1: Verifies that the agentic fallback is correctly triggered when the
    standard LLM fix loop fails.
    """
    # Arrange
    monkeypatch.syspath_prepend(str(tmp_project))
    mock_pytest = MagicMock(return_value=(1, 0, 0, "mocked pytest failure"))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", mock_pytest)
    mock_llm_fix = MagicMock(return_value=(False, False, "", "", "Simulated LLM failure", 0.0, "mock_model"))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", mock_llm_fix)
    mock_agentic_fix = MagicMock(return_value=(True, "Agentic fix successful"))
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    # Act
    success, _, _, _, _, _ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    # Assert
    mock_pytest.assert_called()
    mock_llm_fix.assert_called_once()
    mock_agentic_fix.assert_called_once()
    assert success is True

def test_fallback_not_triggered_if_disabled(tmp_project, monkeypatch):
    """
    Case 2: Verifies that the agentic fallback is NOT called when the
    `--agentic-fallback` flag is False, even if the fix loop fails.
    """
    # Arrange
    monkeypatch.syspath_prepend(str(tmp_project))
    mock_pytest = MagicMock(return_value=(1, 0, 0, "mocked pytest failure"))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", mock_pytest)
    mock_llm_fix = MagicMock(return_value=(False, False, "", "", "Simulated LLM failure", 0.0, "mock_model"))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", mock_llm_fix)
    mock_agentic_fix = MagicMock()
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    # Act
    success, _, _, _, _, _ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=False
    )

    # Assert
    mock_agentic_fix.assert_not_called()
    assert success is False

def test_fallback_not_triggered_on_success(tmp_project, monkeypatch):
    """
    Case 3: Verifies that the agentic fallback is NOT called if the standard
    fix loop succeeds.
    """
    # Arrange
    monkeypatch.syspath_prepend(str(tmp_project))
    mock_pytest = MagicMock(side_effect=[(1, 0, 0, "fail"), (0, 0, 0, "pass")])
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", mock_pytest)
    mock_llm_fix = MagicMock(return_value=(True, True, "", FIXED_CODE_CONTENT, "Fixed", 0.1, "gpt-4"))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", mock_llm_fix)
    mock_agentic_fix = MagicMock()
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    # Act
    success, _, _, _, _, _ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    # Assert
    mock_agentic_fix.assert_not_called()
    assert success is True

def test_budget_exceeded_before_fallback(tmp_project, monkeypatch):
    """
    Case 4: Verifies that if the cost budget is exceeded by the standard LLM
    fixer, the agentic fallback is not triggered.
    """
    # Arrange
    monkeypatch.syspath_prepend(str(tmp_project))
    mock_pytest = MagicMock(return_value=(1, 0, 0, "mocked pytest failure"))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", mock_pytest)
    mock_llm_fix = MagicMock(return_value=(False, False, "", "", "Expensive failure", 2.0, "gpt-4-turbo"))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", mock_llm_fix)
    mock_agentic_fix = MagicMock()
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    # Act
    success, _, _, _, _, _ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=3, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    # Assert
    mock_agentic_fix.assert_not_called()
    assert success is False

def test_max_attempts_reached_triggers_fallback(tmp_project, monkeypatch):
    """
    Case 5: Verifies that the fallback is correctly triggered after the loop
    reaches its max_attempts.
    """
    # Arrange
    monkeypatch.syspath_prepend(str(tmp_project))
    mock_pytest = MagicMock(return_value=(1, 0, 0, "mocked pytest failure"))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", mock_pytest)
    mock_llm_fix = MagicMock(return_value=(False, False, "", "", "Simulated LLM failure", 0.1, "mock_model"))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", mock_llm_fix)
    mock_agentic_fix = MagicMock(return_value=(True, "Agentic fix successful"))
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    # Act
    fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=3, budget=5.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    # Assert
    assert mock_llm_fix.call_count == 3
    mock_agentic_fix.assert_called_once()

def test_agent_failure_returns_overall_failure(tmp_project, monkeypatch):
    """
    Case 6: Verifies that if the agentic fallback itself fails, the entire
    `fix_error_loop` function correctly reports `success=False`.
    """
    # Arrange
    monkeypatch.syspath_prepend(str(tmp_project))
    mock_pytest = MagicMock(return_value=(1, 0, 0, "mocked pytest failure"))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", mock_pytest)
    mock_llm_fix = MagicMock(return_value=(False, False, "", "", "Simulated LLM failure", 0.0, "mock_model"))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", mock_llm_fix)
    mock_agentic_fix = MagicMock(return_value=(False, "Agentic fix failed"))
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    # Act
    success, _, _, _, _, _ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    # Assert
    mock_agentic_fix.assert_called_once()
    assert success is False

def test_no_unit_test_file_returns_failure(tmp_project):
    """
    Case 7: Verifies that the function exits gracefully and returns False
    if the initial unit test file does not exist.
    """
    # Arrange
    non_existent_test_file = tmp_project / "tests" / "non_existent_test.py"

    # Act
    success, _, _, _, _, _ = fix_error_loop(
        unit_test_file=str(non_existent_test_file),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    # Assert
    assert success is False

def test_no_code_file_returns_failure(tmp_project):
    """
    Case 8: Verifies that the function exits gracefully and returns False
    if the code file does not exist.
    """
    # Arrange
    non_existent_code_file = tmp_project / "src" / "non_existent_code.py"

    # Act
    success, _, _, _, _, _ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(non_existent_code_file),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    # Assert
    assert success is False

def test_initial_pytest_pass_skips_everything(tmp_project, monkeypatch):
    """
    Case 9: Verifies that if the initial pytest run passes, no fix attempts
    (neither LLM nor agentic) are made.
    """
    # Arrange
    monkeypatch.syspath_prepend(str(tmp_project))
    mock_pytest = MagicMock(return_value=(0, 0, 0, "All tests pass"))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", mock_pytest)
    mock_llm_fix = MagicMock()
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", mock_llm_fix)
    mock_agentic_fix = MagicMock()
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    # Act
    success, _, _, _, _, _ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=3, budget=5.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    # Assert
    mock_pytest.assert_called_once()
    mock_llm_fix.assert_not_called()
    mock_agentic_fix.assert_not_called()
    assert success is True

def test_agent_receives_correct_file_paths(tmp_project, monkeypatch):
    """
    Case 10: Verifies that the correct file paths are passed to the agentic fix function.
    """
    # Arrange
    monkeypatch.syspath_prepend(str(tmp_project))
    mock_pytest = MagicMock(return_value=(1, 0, 0, "mocked pytest failure"))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", mock_pytest)
    mock_llm_fix = MagicMock(return_value=(False, False, "", "", "Simulated LLM failure", 0.0, "mock_model"))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", mock_llm_fix)
    mock_agentic_fix = MagicMock(return_value=(True, "Agentic fix successful"))
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)
    
    error_log_path = tmp_project / "custom_error.log"

    # Act
    fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(error_log_path),
        verbose=False, agentic_fallback=True
    )

    # Assert
    mock_agentic_fix.assert_called_once()
    agent_call_args = mock_agentic_fix.call_args[1]
    assert agent_call_args['prompt_file'] == str(tmp_project / "prompts" / "utils_python.prompt")
    assert agent_call_args['code_file'] == str(tmp_project / "src" / "utils.py")
    assert agent_call_args['unit_test_file'] == str(tmp_project / "tests" / "test_utils.py")
    assert agent_call_args['error_log_file'] == str(error_log_path)
