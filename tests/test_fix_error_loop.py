import os
import pytest
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock
from pdd.fix_error_loop import fix_error_loop, extract_test_results, create_backup_files, IterationResult

# Fixture for temporary files
@pytest.fixture
def temp_files(tmp_path):
    unit_test = tmp_path / "test_example.py"
    code_file = tmp_path / "example.py"
    verification = tmp_path / "verify.py"
    error_log = tmp_path / "error_log.txt"
    
    # Create dummy files
    unit_test.write_text("def test_dummy(): assert True")
    code_file.write_text("def dummy(): return True")
    verification.write_text("print('verification successful')")
    
    return str(unit_test), str(code_file), str(verification), str(error_log)

def test_successful_fix(temp_files):
    unit_test, code_file, verification, error_log = temp_files
    
    # Mock subprocess.run to simulate passing tests after one attempt
    with patch('subprocess.run') as mock_run:
        mock_run.side_effect = [
            MagicMock(stdout="1 failed", stderr="", returncode=1),  # First pytest run
            MagicMock(stdout="success", stderr="", returncode=0),   # Verification
            MagicMock(stdout="All tests passed", stderr="", returncode=0),  # Final pytest
            MagicMock(stdout="All tests passed", stderr="", returncode=0)   # Extra for safety
        ]
        
        # Mock fix_errors_from_unit_tests
        with patch('pdd.fix_error_loop.fix_errors_from_unit_tests') as mock_fix:
            mock_fix.return_value = (True, True, "fixed test", "fixed code", 0.1, "gpt-4")
            
            # Mock file existence
            with patch('os.path.exists', return_value=True):
                success, final_test, final_code, attempts, cost, model = fix_error_loop(
                    unit_test, code_file, "test prompt", verification,
                    0.7, 0.5, 3, 1.0, error_log
                )
                
                assert success == True
                assert attempts == 2
                assert cost == 0.1
                assert model == "gpt-4"

def test_budget_exceeded(temp_files):
    unit_test, code_file, verification, error_log = temp_files
    
    with patch('subprocess.run') as mock_run:
        mock_run.return_value = MagicMock(stdout="1 failed", stderr="", returncode=1)
        
        with patch('pdd.fix_error_loop.fix_errors_from_unit_tests') as mock_fix:
            mock_fix.return_value = (True, True, "fixed test", "fixed code", 2.0, "gpt-4")
            
            success, _, _, attempts, cost, _ = fix_error_loop(
                unit_test, code_file, "test prompt", verification,
                0.7, 0.5, 3, 1.0, error_log
            )
            
            assert success == False
            assert cost == 2.0
            assert attempts == 1

def test_invalid_inputs():
    with patch('os.path.exists', return_value=False):
        with pytest.raises(FileNotFoundError):
            fix_error_loop(
                "nonexistent.py", "nonexistent.py", "prompt",
                "nonexistent.py", 0.7, 0.5, 3, 1.0
            )
    
    with patch('os.path.exists', return_value=True):
        with pytest.raises(ValueError):
            fix_error_loop(
                "test.py", "code.py", "prompt",
                "verify.py", 1.5, 0.5, 3, 1.0
            )

def test_extract_test_results():
    # Test various pytest output formats
    assert extract_test_results("4 failed, 2 passed") == (4, 0)
    assert extract_test_results("1 error, 1 failed") == (1, 1)
    assert extract_test_results("1 error") == (0, 1)
    assert extract_test_results("All tests passed") == (0, 0)

def test_create_backup_files(temp_files):
    unit_test, code_file, _, _ = temp_files
    
    backup_unit, backup_code = create_backup_files(unit_test, code_file, 1, 0, 3)
    
    assert os.path.exists(backup_unit)
    assert os.path.exists(backup_code)
    assert backup_unit.endswith("_1_0_3.py")
    assert backup_code.endswith("_1_0_3.py")

def test_iteration_result_comparison():
    result1 = IterationResult(fails=1, errors=0, iteration=1, total_fails_and_errors=1)
    result2 = IterationResult(fails=2, errors=0, iteration=2, total_fails_and_errors=2)
    result3 = IterationResult(fails=1, errors=1, iteration=3, total_fails_and_errors=2)
    
    assert result1.is_better_than(result2)
    assert result1.is_better_than(result3)
    assert result2.is_better_than(result3)  # Same total but fewer errors
    assert result1.is_better_than(None)

def test_verification_failure(temp_files):
    unit_test, code_file, verification, error_log = temp_files
    
    with patch('subprocess.run') as mock_run:
        mock_run.side_effect = [
            MagicMock(stdout="1 failed", stderr="", returncode=1),  # First pytest
            MagicMock(stdout="verification failed", stderr="error", returncode=1),  # Failed verification
            MagicMock(stdout="1 failed", stderr="", returncode=1),   # Pytest after verification failure
            MagicMock(stdout="verification failed again", stderr="error again", returncode=1), # Second verification
            MagicMock(stdout="1 failed", stderr="", returncode=1), # Second pytest
            MagicMock(stdout="1 failed", stderr="", returncode=1),  # Third pytest
            MagicMock(stdout="1 failed", stderr="", returncode=1),  # Final pytest
            MagicMock(stdout="1 failed", stderr="", returncode=1)   # Extra for safety
        ]
        
        with patch('pdd.fix_error_loop.fix_errors_from_unit_tests') as mock_fix:
            mock_fix.return_value = (True, True, "fixed test", "fixed code", 0.1, "gpt-4")
            
            # Mock file existence
            with patch('os.path.exists', return_value=True):
                success, _, _, attempts, cost, _ = fix_error_loop(
                    unit_test, code_file, "test prompt", verification,
                    0.7, 0.5, 3, 1.0, error_log
                )
                
                assert success == False
                assert attempts == 3
                assert os.path.exists(error_log)
                with open(error_log, 'r') as f:
                    content = f.read()
                    assert "verification failed" in content
                    assert "verification failed again" in content
                    assert "Restoring previous working code" in content