# tests/test_fix_code_loop.py

import pytest
import os
import shutil
import subprocess
from unittest import mock
from unittest.mock import patch, mock_open, MagicMock
from pathlib import Path

# Assuming the package is structured with 'pdd.fix_code_loop'
# and 'pdd.fix_code_module_errors'

from pdd.fix_code_loop import fix_code_loop


@pytest.fixture
def setup_files(tmp_path):
    """
    Fixture to create temporary code_file and verification_program.
    """
    code_file = tmp_path / "code.py"
    verification_program = tmp_path / "verify.py"
    code_file.write_text(
        """
def calculate_sum(numbers):
    return sum(numbers)

result = calculate_sum("123")  # Error: trying to sum a string
print(result)
"""
    )
    verification_program.write_text(
        """
import code

def test_calculate_sum():
    try:
        code.calculate_sum("123")
    except TypeError as e:
        print(e)
        exit(1)

if __name__ == "__main__":
        test_calculate_sum()
"""
    )
    return str(code_file), str(verification_program)


@pytest.fixture
def mock_fix_code_module_errors():
    """
    Fixture to mock fix_code_module_errors function.
    """
    with patch("pdd.fix_code_loop.fix_code_module_errors") as mock_func:
        yield mock_func


@pytest.fixture
def mock_subprocess_run_success():
    """
    Fixture to mock subprocess.run to simulate successful execution.
    """
    with patch("subprocess.run") as mock_run:
        mock_process = MagicMock()
        mock_process.returncode = 0
        mock_process.stdout = "Success"
        mock_process.stderr = ""
        mock_run.return_value = mock_process
        yield mock_run


@pytest.fixture
def mock_subprocess_run_failure():
    """
    Fixture to mock subprocess.run to simulate failed execution.
    """
    with patch("subprocess.run") as mock_run:
        mock_process = MagicMock()
        mock_process.returncode = 1
        mock_process.stdout = ""
        mock_process.stderr = "TypeError: unsupported operand type(s) for +: 'int' and 'str'"
        mock_run.return_value = mock_process
        yield mock_run


def test_successful_fix_first_attempt(setup_files, mock_subprocess_run_success, mock_fix_code_module_errors):
    """
    Test that fix_code_loop succeeds without needing any fixes.
    """
    code_file, verification_program = setup_files

    result = fix_code_loop(
        code_file=code_file,
        prompt="Write a function that calculates the sum of numbers",
        verification_program=verification_program,
        strength=0.7,
        temperature=0.5,
        max_attempts=3,
        budget=10.0
    )

    assert result[0] is True  # success
    assert result[3] == 1  # total_attempts
    assert result[4] == 0.0  # total_cost
    assert result[5] == ""  # model_name


def test_fix_requires_one_attempt(setup_files, mock_subprocess_run_failure, mock_fix_code_module_errors):
    """
    Test that fix_code_loop makes one fix attempt and succeeds.
    """
    code_file, verification_program = setup_files

    # Mock fix_code_module_errors to return updates
    mock_fix_code_module_errors.return_value = (True, True, "fixed_verify.py", "fixed_code.py", 2.5, "GPT-4")

    # After first failure, simulate success
    def subprocess_run_side_effect(*args, **kwargs):
        if mock_subprocess_run_failure.call_count == 1:
            # First attempt fails
            mock_process = MagicMock()
            mock_process.returncode = 1
            mock_process.stdout = ""
            mock_process.stderr = "TypeError: unsupported operand type(s) for +: 'int' and 'str'"
            return mock_process
        else:
            # Second attempt succeeds
            mock_process = MagicMock()
            mock_process.returncode = 0
            mock_process.stdout = "Success"
            mock_process.stderr = ""
            return mock_process

    mock_subprocess_run_failure.side_effect = subprocess_run_side_effect

    result = fix_code_loop(
        code_file=code_file,
        prompt="Write a function that calculates the sum of numbers",
        verification_program=verification_program,
        strength=0.7,
        temperature=0.5,
        max_attempts=3,
        budget=10.0
    )

    assert result[0] is True  # success
    assert result[3] == 2  # total_attempts
    assert result[4] == 2.5  # total_cost
    assert result[5] == "GPT-4"  # model_name
    mock_fix_code_module_errors.assert_called_once()


def test_budget_exceeded(setup_files, mock_subprocess_run_failure, mock_fix_code_module_errors):
    """
    Test that fix_code_loop stops when the budget is exceeded.
    """
    code_file, verification_program = setup_files

    # Mock fix_code_module_errors to always add cost
    mock_fix_code_module_errors.return_value = (True, True, "fixed_verify.py", "fixed_code.py", 5.0, "GPT-4")

    # Keep failing to exhaust the budget
    def subprocess_run_side_effect(*args, **kwargs):
        mock_process = MagicMock()
        mock_process.returncode = 1
        mock_process.stdout = ""
        mock_process.stderr = "TypeError: unsupported operand type(s) for +: 'int' and 'str'"
        return mock_process

    mock_subprocess_run_failure.side_effect = subprocess_run_side_effect

    result = fix_code_loop(
        code_file=code_file,
        prompt="Write a function that calculates the sum of numbers",
        verification_program=verification_program,
        strength=0.7,
        temperature=0.5,
        max_attempts=5,
        budget=10.0  # Only two attempts possible
    )

    assert result[0] is False  # not successful
    assert result[3] == 2  # total_attempts before budget exceeded
    assert result[4] == 10.0  # total_cost
    assert result[5] == "GPT-4"  # model_name
    assert mock_fix_code_module_errors.call_count == 2


def test_max_attempts_exceeded(setup_files, mock_subprocess_run_failure, mock_fix_code_module_errors):
    """
    Test that fix_code_loop stops after reaching max_attempts.
    """
    code_file, verification_program = setup_files

    # Mock fix_code_module_errors to add a small cost each time
    mock_fix_code_module_errors.return_value = (True, True, "fixed_verify.py", "fixed_code.py", 1.0, "GPT-4")

    # Always fail
    def subprocess_run_side_effect(*args, **kwargs):
        mock_process = MagicMock()
        mock_process.returncode = 1
        mock_process.stdout = ""
        mock_process.stderr = "TypeError: unsupported operand type(s) for +: 'int' and 'str'"
        return mock_process

    mock_subprocess_run_failure.side_effect = subprocess_run_side_effect

    result = fix_code_loop(
        code_file=code_file,
        prompt="Write a function that calculates the sum of numbers",
        verification_program=verification_program,
        strength=0.7,
        temperature=0.5,
        max_attempts=3,
        budget=10.0
    )

    assert result[0] is False  # not successful
    assert result[3] == 3  # total_attempts reached
    assert result[4] == 3.0  # total_cost
    assert result[5] == "GPT-4"  # model_name
    assert mock_fix_code_module_errors.call_count == 3


def test_invalid_strength_temperature(setup_files):
    """
    Test that fix_code_loop raises ValueError for invalid strength or temperature.
    """
    code_file, verification_program = setup_files

    with pytest.raises(ValueError):
        fix_code_loop(
            code_file=code_file,
            prompt="Write a function that calculates the sum of numbers",
            verification_program=verification_program,
            strength=1.5,  # Invalid
            temperature=0.5,
            max_attempts=3,
            budget=10.0
        )

    with pytest.raises(ValueError):
        fix_code_loop(
            code_file=code_file,
            prompt="Write a function that calculates the sum of numbers",
            verification_program=verification_program,
            strength=0.7,
            temperature=-0.1,  # Invalid
            max_attempts=3,
            budget=10.0
        )


def test_invalid_max_attempts_budget(setup_files):
    """
    Test that fix_code_loop raises ValueError for invalid max_attempts or budget.
    """
    code_file, verification_program = setup_files

    with pytest.raises(ValueError):
        fix_code_loop(
            code_file=code_file,
            prompt="Write a function that calculates the sum of numbers",
            verification_program=verification_program,
            strength=0.7,
            temperature=0.5,
            max_attempts=0,  # Invalid
            budget=10.0
        )

    with pytest.raises(ValueError):
        fix_code_loop(
            code_file=code_file,
            prompt="Write a function that calculates the sum of numbers",
            verification_program=verification_program,
            strength=0.7,
            temperature=0.5,
            max_attempts=3,
            budget=-5.0  # Invalid
        )


def test_missing_files():
    """
    Test that fix_code_loop raises FileNotFoundError when code_file or verification_program is missing.
    """
    with pytest.raises(FileNotFoundError):
        fix_code_loop(
            code_file="non_existent_code.py",
            prompt="Write a function that calculates the sum of numbers",
            verification_program="non_existent_verify.py",
            strength=0.7,
            temperature=0.5,
            max_attempts=3,
            budget=10.0
        )


def test_no_changes_needed(setup_files, mock_subprocess_run_failure, mock_fix_code_module_errors):
    """
    Test that fix_code_loop stops when no changes are needed.
    """
    code_file, verification_program = setup_files

    # Mock fix_code_module_errors to indicate no updates needed
    mock_fix_code_module_errors.return_value = (False, False, "", "", 0.0, "")

    # Simulate one failure
    mock_process = MagicMock()
    mock_process.returncode = 1
    mock_process.stdout = ""
    mock_process.stderr = "TypeError: unsupported operand type(s) for +: 'int' and 'str'"
    mock_subprocess_run_failure.return_value = mock_process

    result = fix_code_loop(
        code_file=code_file,
        prompt="Write a function that calculates the sum of numbers",
        verification_program=verification_program,
        strength=0.7,
        temperature=0.5,
        max_attempts=5,
        budget=10.0
    )

    assert result[0] is False  # not successful
    assert result[3] == 1  # only one attempt
    assert result[4] == 0.0  # no cost
    assert mock_fix_code_module_errors.assert_called_once()


def test_restores_original_files_on_failure(setup_files, mock_subprocess_run_failure, mock_fix_code_module_errors):
    """
    Test that fix_code_loop restores original files if unable to fix errors.
    """
    code_file, verification_program = setup_files

    # Mock fix_code_module_errors to always attempt fixes but never succeed
    mock_fix_code_module_errors.return_value = (True, True, "fixed_verify.py", "fixed_code.py", 1.0, "GPT-4")

    # Always fail
    mock_process = MagicMock()
    mock_process.returncode = 1
    mock_process.stdout = ""
    mock_process.stderr = "TypeError: unsupported operand type(s) for +: 'int' and 'str'"
    mock_subprocess_run_failure.return_value = mock_process

    original_code = Path(code_file).read_text()
    original_verify = Path(verification_program).read_text()

    result = fix_code_loop(
        code_file=code_file,
        prompt="Write a function that calculates the sum of numbers",
        verification_program=verification_program,
        strength=0.7,
        temperature=0.5,
        max_attempts=2,
        budget=5.0
    )

    # After failure, files should be restored
    assert Path(code_file).read_text() == original_code
    assert Path(verification_program).read_text() == original_verify
    assert result[0] is False  # not successful


def test_error_log_file_handling(setup_files, mock_subprocess_run_failure, mock_fix_code_module_errors, tmp_path):
    """
    Test that fix_code_loop handles the error_log_file correctly.
    """
    code_file, verification_program = setup_files
    error_log = tmp_path / "custom_error.log"

    # Mock fix_code_module_errors to attempt a fix
    mock_fix_code_module_errors.return_value = (True, False, "", "fixed_code.py", 1.0, "GPT-4")

    # Simulate one failure and one success
    def subprocess_run_side_effect(*args, **kwargs):
        if mock_subprocess_run_failure.call_count == 0:
            # First attempt fails
            mock_process = MagicMock()
            mock_process.returncode = 1
            mock_process.stdout = ""
            mock_process.stderr = "Error on first attempt"
            return mock_process
        else:
            # Second attempt succeeds
            mock_process = MagicMock()
            mock_process.returncode = 0
            mock_process.stdout = "Success on second attempt"
            mock_process.stderr = ""
            return mock_process

    mock_subprocess_run_failure.side_effect = subprocess_run_side_effect

    result = fix_code_loop(
        code_file=code_file,
        prompt="Write a function that calculates the sum of numbers",
        verification_program=verification_program,
        strength=0.7,
        temperature=0.5,
        max_attempts=3,
        budget=10.0,
        error_log_file=str(error_log)
    )

    # Check that the custom error log file was created and contains the error
    assert error_log.exists()
    log_content = error_log.read_text()
    assert "Error on first attempt" in log_content
    assert "Success on second attempt" in log_content

    assert result[0] is True  # success
    assert result[3] == 2  # two attempts
    assert result[4] == 1.0  # total cost
    assert result[5] == "GPT-4"  # model name
    mock_fix_code_module_errors.assert_called_once()


def test_relative_imports(mock_subprocess_run_success, mock_fix_code_module_errors, setup_files):
    """
    Test that fix_code_loop uses relative imports correctly.
    """
    code_file, verification_program = setup_files

    # Since imports are relative, ensure that the function can be called correctly
    result = fix_code_loop(
        code_file=code_file,
        prompt="Write a function that calculates the sum of numbers",
        verification_program=verification_program,
        strength=0.7,
        temperature=0.5,
        max_attempts=1,
        budget=10.0
    )

    assert result[0] is True  # success
    assert mock_fix_code_module_errors.call_count == 0  # No fixes needed


def test_zero_max_attempts(setup_files):
    """
    Test that fix_code_loop raises ValueError when max_attempts is less than 1.
    """
    code_file, verification_program = setup_files

    with pytest.raises(ValueError):
        fix_code_loop(
            code_file=code_file,
            prompt="Write a function that calculates the sum of numbers",
            verification_program=verification_program,
            strength=0.7,
            temperature=0.5,
            max_attempts=0,  # Invalid
            budget=10.0
        )
