import pytest
import os
import tempfile
from unittest.mock import patch, MagicMock
from pdd.fix_error_loop import fix_error_loop
import subprocess

@pytest.fixture
def temp_files():
    """Create temporary files for unit tests, code, and verification."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as unit_test_file:
        unit_test_file.write("def test_dummy(): assert False")
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as code_file:
        code_file.write("def dummy_function(): return True")
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as verification_file:
        verification_file.write("print('Verification successful')")
    yield unit_test_file.name, code_file.name, verification_file.name
    os.unlink(unit_test_file.name)
    os.unlink(code_file.name)
    os.unlink(verification_file.name)

@pytest.fixture
def mock_subprocess_run():
    """Mock the subprocess.run function."""
    with patch('subprocess.run') as mock_run:
        yield mock_run

@pytest.fixture
def mock_fix_errors_from_unit_tests():
    """Mock the fix_errors_from_unit_tests function."""
    with patch('pdd.fix_error_loop.fix_errors_from_unit_tests') as mock_fix:
        yield mock_fix

def test_fix_error_loop_success(temp_files, mock_subprocess_run, mock_fix_errors_from_unit_tests):
    """Test successful error fixing scenario."""
    unit_test_file, code_file, verification_file = temp_files
    # Use subprocess.CompletedProcess instead of MagicMock for accurate simulation
    mock_subprocess_run.side_effect = [
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED"),
        subprocess.CompletedProcess(args=["python", verification_file], returncode=0, stdout="Verification successful"),
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=0, stdout="All tests passed")
    ]
    mock_fix_errors_from_unit_tests.return_value = (True, True, "fixed_unit_test", "fixed_code", 0.5, "gpt-3.5-turbo")

    success, final_unit_test, final_code, attempts, total_cost, model_name = fix_error_loop(
        unit_test_file, code_file, "test prompt", verification_file, 0.7, 0.5, 3, 10.0
    )

    assert success is True
    assert final_unit_test == "fixed_unit_test"
    assert final_code == "fixed_code"
    assert attempts == 1
    assert total_cost == 0.5
    assert model_name == "gpt-3.5-turbo"

def test_fix_error_loop_max_attempts(temp_files, mock_subprocess_run, mock_fix_errors_from_unit_tests):
    """Test scenario where maximum attempts are reached without success."""
    unit_test_file, code_file, verification_file = temp_files
    # All pytest runs fail, no verification runs succeed
    mock_subprocess_run.side_effect = [
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED"),
        subprocess.CompletedProcess(args=["python", verification_file], returncode=1, stdout="Verification failed"),
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED"),
        subprocess.CompletedProcess(args=["python", verification_file], returncode=1, stdout="Verification failed"),
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED"),
        subprocess.CompletedProcess(args=["python", verification_file], returncode=1, stdout="Verification failed")
    ]
    mock_fix_errors_from_unit_tests.return_value = (True, True, "fixed_unit_test", "fixed_code", 0.5, "gpt-3.5-turbo")

    success, _, _, attempts, total_cost, _ = fix_error_loop(
        unit_test_file, code_file, "test prompt", verification_file, 0.7, 0.5, 3, 10.0
    )

    assert success is False
    assert attempts == 3
    assert total_cost == 1.5

def test_fix_error_loop_budget_exceeded(temp_files, mock_subprocess_run, mock_fix_errors_from_unit_tests):
    """Test scenario where the budget is exceeded."""
    unit_test_file, code_file, verification_file = temp_files
    # Each fix attempt costs 2.0, budget is 5.0, max_attempts=10
    mock_subprocess_run.side_effect = [
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED"),
        subprocess.CompletedProcess(args=["python", verification_file], returncode=1, stdout="Verification failed"),
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED"),
        subprocess.CompletedProcess(args=["python", verification_file], returncode=1, stdout="Verification failed"),
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED")
    ]
    mock_fix_errors_from_unit_tests.return_value = (True, True, "fixed_unit_test", "fixed_code", 2.0, "gpt-3.5-turbo")

    success, _, _, attempts, total_cost, _ = fix_error_loop(
        unit_test_file, code_file, "test prompt", verification_file, 0.7, 0.5, 10, 5.0
    )

    assert success is False
    assert attempts == 3  # 3 attempts before exceeding budget (2.0 * 3 = 6.0 > 5.0)
    assert total_cost == 6.0

def test_fix_error_loop_no_changes_needed(temp_files, mock_subprocess_run, mock_fix_errors_from_unit_tests):
    """Test scenario where no changes are needed in the fix attempt."""
    unit_test_file, code_file, verification_file = temp_files
    # Initial test run fails, fix_errors_from_unit_tests indicates no updates needed
    mock_subprocess_run.side_effect = [
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED"),
        subprocess.CompletedProcess(args=["python", verification_file], returncode=1, stdout="Verification failed")
    ]
    mock_fix_errors_from_unit_tests.return_value = (False, False, "", "", 0.5, "gpt-3.5-turbo")

    success, _, _, attempts, total_cost, _ = fix_error_loop(
        unit_test_file, code_file, "test prompt", verification_file, 0.7, 0.5, 3, 10.0
    )

    assert success is False
    assert attempts == 1
    assert total_cost == 0.5

def test_fix_error_loop_verification_failure(temp_files, mock_subprocess_run, mock_fix_errors_from_unit_tests):
    """Test scenario where verification fails after fixing, but the function continues to attempt fixes."""
    unit_test_file, code_file, verification_file = temp_files
    # First fix attempt: test fails, fix applied
    # Verification fails
    # Second fix attempt: test fails, fix applied
    # Verification fails
    # Third fix attempt: test runs but let's say verification succeeds
    mock_subprocess_run.side_effect = [
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED"),
        subprocess.CompletedProcess(args=["python", verification_file], returncode=1, stdout="Verification failed"),
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED"),
        subprocess.CompletedProcess(args=["python", verification_file], returncode=1, stdout="Verification failed"),
        subprocess.CompletedProcess(args=["python", "-m", "pytest", "-vv", unit_test_file], returncode=1, stdout="FAILED FAILED"),
        subprocess.CompletedProcess(args=["python", verification_file], returncode=1, stdout="Verification failed")
    ]
    mock_fix_errors_from_unit_tests.return_value = (True, True, "fixed_unit_test", "fixed_code", 0.5, "gpt-3.5-turbo")

    success, final_unit_test, final_code, attempts, total_cost, _ = fix_error_loop(
        unit_test_file,
        code_file,
        "test prompt",
        verification_file,
        0.7,
        0.5,
        3,
        10.0
    )

    assert success is False
    assert final_unit_test != "fixed_unit_test"
    assert final_code != "fixed_code"
    assert attempts == 3
    assert total_cost == 1.5

def test_fix_error_loop_file_io_error(temp_files):
    """Test scenario where a file I/O error occurs."""
    non_existent_file = "/path/to/non/existent/file.py"
    unit_test_file, code_file, verification_file = temp_files

    success, final_unit_test, final_code, attempts, total_cost, model_name = fix_error_loop(
        non_existent_file, code_file, "test prompt", verification_file, 0.7, 0.5, 3, 10.0
    )

    assert success is False
    assert final_unit_test == ""
    assert final_code == ""
    assert attempts == 0
    assert total_cost == 0.0
    assert model_name == ""
