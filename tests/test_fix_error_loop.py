import os
import sys
import subprocess
from unittest.mock import patch
import pytest
import shutil
from pathlib import Path

from pdd.fix_error_loop import fix_error_loop

@pytest.fixture
def setup_files(tmp_path):
    """
    Create temporary directories and files for testing,
    including a code file, test file, and a verification program.
    """
    # Create directories
    code_dir = tmp_path / "pdd"
    code_dir.mkdir()
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    
    # Create initial code file with an intentional error
    code_file = code_dir / "code.py"
    code_content = "def add(a, b): return a + b + 1  # Intentional error"
    code_file.write_text(code_content)
    
    # Create unit test file
    test_file = test_dir / "test_code.py"
    test_content = """
def test_add():
    assert add(2, 3) == 5
    assert add(-1, 1) == 0
"""
    test_file.write_text(test_content)
    
    # Create verification program
    verify_file = tmp_path / "verify.py"
    verify_file.write_text("print('Verification passed')")
    
    return {
        "code_file": code_file,
        "test_file": test_file,
        "verify_file": verify_file,
        "error_log": tmp_path / "error_log.txt",
    }

def test_successful_fix(setup_files):
    """
    Test a scenario where the code is successfully fixed on the first attempt.
    We mock run_pytest_on_file so that the initial test fails, the second test passes,
    and the final run also passes. We also mock the verification script to pass.
    """
    files = setup_files

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_run_pytest:
        # 1) initial test run => fails=1 => triggers fix
        # 2) test run in the same iteration => success => 0 fails
        # 3) final run => success => 0 fails
        mock_run_pytest.side_effect = [
            (1, 0, 0, "initial test output"),  
            (0, 0, 0, "second test output"),   
            (0, 0, 0, "final test output"),    
        ]
        with patch("subprocess.run") as mock_subproc:
            # verification success
            mock_subproc.return_value = subprocess.CompletedProcess(args=[], returncode=0)
            
            # Mock fix_errors_from_unit_tests to return corrected code
            with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
                mock_fix.return_value = (
                    True, True,  # updated_unit_test, updated_code
                    files["test_file"].read_text(), 
                    "def add(a, b): return a + b",  # corrected code
                    0.1,         # cost
                    "mock-model" # model_name
                )
                
                success, final_test, final_code, attempts, cost, model = fix_error_loop(
                    unit_test_file=str(files["test_file"]),  # pass strings
                    code_file=str(files["code_file"]),
                    prompt="Test prompt",
                    verification_program=str(files["verify_file"]),
                    strength=0.5,
                    temperature=0.0,
                    max_attempts=3,
                    budget=10.0,
                    error_log_file=str(files["error_log"]),
                    verbose=False
                )
    
    assert success is True
    assert "return a + b" in final_code
    assert attempts == 1         # There was only one fix attempt
    assert cost == 0.1
    assert model == "mock-model"

def test_max_attempts_exceeded(setup_files):
    """
    Test that if every test run fails, eventually the loop hits max_attempts and exits.
    """
    files = setup_files
    
    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_run_pytest:
        # 2 attempts per iteration (initial + second in same iteration), plus 1 final
        # For max_attempts=3, let's provide enough calls returning fails=1 each time:
        mock_run_pytest.side_effect = [
            # Iteration 1
            (1, 0, 0, "test run output"),  
            (1, 0, 0, "test run output"),  
            # Iteration 2
            (1, 0, 0, "test run output"),  
            (1, 0, 0, "test run output"),  
            # Iteration 3
            (1, 0, 0, "test run output"),  
            (1, 0, 0, "test run output"),  
            # Final run
            (1, 0, 0, "test run output"),  
        ]
        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            # Return "no change" each time => triggers repeated fixes
            mock_fix.return_value = (False, False, "", "", 0.0, "mock-model")
            
            success, final_test, final_code, attempts, cost, model = fix_error_loop(
                str(files["test_file"]),
                str(files["code_file"]),
                "Test prompt",
                str(files["verify_file"]),
                0.5,
                0.0,
                3,           # max_attempts
                10.0,
                str(files["error_log"])
            )
    
    assert success is False
    # We used all 3 attempts
    assert attempts == 3
    # Code was never successfully changed (still has the +1)
    assert "return a + b + 1" in final_code

def test_verification_failure(setup_files):
    """
    Test a scenario where the code gets "fixed" but then fails verification, 
    so it is restored, and the tests keep failing.
    """
    files = setup_files

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_run_pytest:
        # Provide enough side effects for 3 iterations => 
        # each iteration calls run_pytest_on_file twice (initial + second) plus 1 final run:
        # total = 2*3 + 1 = 7 calls
        mock_run_pytest.side_effect = [
            # Iteration 1
            (1, 0, 0, "test run output"),   # 1) initial fails
            (1, 0, 0, "test run output"),   # 2) second fails
            # Iteration 2
            (1, 0, 0, "test run output"),   # 3) initial fails
            (1, 0, 0, "test run output"),   # 4) second fails
            # Iteration 3
            (1, 0, 0, "test run output"),   # 5) initial fails
            (1, 0, 0, "test run output"),   # 6) second fails
            # Final run
            (1, 0, 0, "test run output"),   # 7) final fails
        ]

        with patch("subprocess.run") as mock_subproc:
            # verification fails => returncode=1
            mock_subproc.return_value = subprocess.CompletedProcess(args=[], returncode=1)
            
            with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
                # Return a "fixed" code that is still incorrect
                mock_fix.return_value = (
                    True, True,
                    files["test_file"].read_text(),
                    "def add(a, b): return 0",  # intentionally bad fix
                    0.1,
                    "mock-model"
                )
                
                success, final_test, final_code, attempts, cost, model = fix_error_loop(
                    str(files["test_file"]),
                    str(files["code_file"]),
                    "Test prompt",
                    str(files["verify_file"]),
                    0.5,
                    0.0,
                    3,
                    10.0,
                    str(files["error_log"])
                )
    
    # Expect failure after 3 attempts
    assert success is False
    # After verification fails, we restore the original code each time => +1 is still there
    assert "return a + b + 1" in final_code

def test_backup_creation(setup_files):
    """
    Test that we create backup files correctly when tests fail.
    """
    files = setup_files
    
    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_run_pytest:
        # Return fails=1 => triggers fix, then second run => fails=1, then final => fails=1
        mock_run_pytest.side_effect = [
            (1, 0, 0, "test run output"),
            (1, 0, 0, "test run output"),
            (1, 0, 0, "test run output"),
        ]
        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            # Return that we changed both test and code, cost=0.1
            mock_fix.return_value = (True, True, "", "", 0.1, "mock-model")
            
            fix_error_loop(
                str(files["test_file"]),
                str(files["code_file"]),
                "Test prompt",
                str(files["verify_file"]),
                0.5, 0.0, 1, 10.0,
                str(files["error_log"])
            )
    
    backup_files = list(files["code_file"].parent.glob("code_*.py"))
    assert len(backup_files) == 1
    # The pattern: code_<iteration>_<errors>_<fails>_<warnings>_<timestamp>.py
    # Since we had fails=1, errors=0, warnings=0 in iteration #1
    # => code_1_0_1_0_<timestamp>.py
    assert "code_1_0_1_0" in backup_files[0].name

def test_missing_files():
    """
    Ensure that fix_error_loop returns False immediately if the test/code files do not exist.
    """
    success, *rest = fix_error_loop(
        "nonexistent_test.py",
        "nonexistent_code.py",
        "prompt",
        "verify.py",
        0.5, 0.0, 3, 10.0
    )
    assert success is False