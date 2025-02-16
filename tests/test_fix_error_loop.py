import os
import sys
import subprocess
from unittest.mock import patch, Mock
import pytest
import shutil

from pdd.fix_error_loop import fix_error_loop

@pytest.fixture
def setup_files(tmp_path):
    # Create directories
    code_dir = tmp_path / "pdd"
    code_dir.mkdir()
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    
    # Create initial code file with error
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
        "code_file": str(code_file),
        "test_file": str(test_file),
        "verify_file": str(verify_file),
        "error_log": str(tmp_path / "error_log.txt"),
    }

def mock_pytest_failure(*args, **kwargs):
    return subprocess.CompletedProcess(
        args=args,
        returncode=1,
        stdout="1 failed, 0 passed, 0 warnings",
        stderr=""
    )

def mock_pytest_success(*args, **kwargs):
    return subprocess.CompletedProcess(
        args=args,
        returncode=0,
        stdout="0 failed, 1 passed, 0 warnings",
        stderr=""
    )

def test_successful_fix(setup_files):
    files = setup_files
    
    # Mock subprocess.run to handle pytest and verification calls
    with patch("subprocess.run") as mock_run:
        mock_run.side_effect = [
            mock_pytest_failure(),  # Initial test run
            mock_pytest_success(),  # Post-fix test run
            mock_pytest_success(),  # Final verification
        ]
        
        # Mock fix_errors_from_unit_tests to return corrected code
        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            mock_fix.return_value = (
                True, True, 
                files["test_file"], 
                "def add(a, b): return a + b",
                0.1, "mock-model"
            )
            
            success, final_test, final_code, attempts, cost, model = fix_error_loop(
                unit_test_file=files["test_file"],
                code_file=files["code_file"],
                prompt="Test prompt",
                verification_program=files["verify_file"],
                strength=0.5,
                temperature=0.0,
                max_attempts=3,
                budget=10.0,
                error_log_file=files["error_log"],
                verbose=False
            )
    
    assert success is True
    assert "return a + b" in final_code
    assert attempts == 1
    assert cost == 0.1

def test_max_attempts_exceeded(setup_files):
    files = setup_files
    
    with patch("subprocess.run") as mock_run:
        mock_run.return_value = mock_pytest_failure()
        
        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            mock_fix.return_value = (False, False, "", "", 0.0, "mock-model")
            
            success, final_test, final_code, attempts, cost, model = fix_error_loop(
                files["test_file"],
                files["code_file"],
                "Test prompt",
                files["verify_file"],
                0.5, 0.0, 3, 10.0,
                files["error_log"]
            )
    
    assert success is False
    assert attempts == 3
    assert "return a + b + 1" in final_code

def test_verification_failure(setup_files):
    files = setup_files
    
    with patch("subprocess.run") as mock_run:
        mock_run.side_effect = [
            mock_pytest_failure(),
            subprocess.CompletedProcess(args=[], returncode=1),  # Verification failure
            mock_pytest_failure(),
        ]
        
        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            mock_fix.return_value = (
                True, True,
                files["test_file"],
                "def add(a, b): return 0",  # Bad fix
                0.1, "mock-model"
            )
            
            success, final_test, final_code, attempts, cost, model = fix_error_loop(
                files["test_file"],
                files["code_file"],
                "Test prompt",
                files["verify_file"],
                0.5, 0.0, 3, 10.0,
                files["error_log"]
            )
    
    assert success is False
    assert "return a + b + 1" in final_code  # Original code restored

def test_backup_creation(setup_files):
    files = setup_files
    
    with patch("subprocess.run") as mock_run:
        mock_run.return_value = mock_pytest_failure()
        
        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            mock_fix.return_value = (True, True, "", "", 0.1, "mock-model")
            
            fix_error_loop(
                files["test_file"],
                files["code_file"],
                "Test prompt",
                files["verify_file"],
                0.5, 0.0, 1, 10.0,
                files["error_log"]
            )
    
    backup_files = list(files["code_file"].parent.glob("code_*.py"))
    assert len(backup_files) == 1
    assert "1_0_0" in backup_files[0].name  # Format: attempt_errors_fails_warnings

def test_missing_files():
    success, *rest = fix_error_loop(
        "nonexistent_test.py",
        "nonexistent_code.py",
        "prompt",
        "verify.py",
        0.5, 0.0, 3, 10.0
    )
    assert success is False