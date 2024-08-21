import pytest
import os
import tempfile
from fix_error_loop import fix_error_loop

@pytest.fixture
def temp_files():
    """Fixture to create temporary files for unit tests, code, and verification."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as unit_test_file, \
         tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as code_file, \
         tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as verification_file:
        
        unit_test_file.write("def test_example():\n    assert 1 == 2")
        code_file.write("def example_function():\n    return 1")
        verification_file.write("print('Verification passed')")
        
        yield unit_test_file.name, code_file.name, verification_file.name
    
    os.unlink(unit_test_file.name)
    os.unlink(code_file.name)
    os.unlink(verification_file.name)

def test_fix_error_loop_success(temp_files, monkeypatch):
    """Test case for successful error fixing."""
    unit_test_file, code_file, verification_file = temp_files
    
    def mock_fix_errors(*args, **kwargs):
        return True, True, "def test_example():\n    assert 1 == 1", "def example_function():\n    return 1", 0.1
    
    monkeypatch.setattr("fix_error_loop.fix_errors_from_unit_tests", mock_fix_errors)
    
    result = fix_error_loop(unit_test_file, code_file, verification_file, 0.5, 0.7, 3, 1.0)
    
    assert result[0] == True  # success
    assert "assert 1 == 1" in result[1]  # final_unit_test
    assert "return 1" in result[2]  # final_code
    assert result[3] == 2  # total_attempts
    assert result[4] == 0.1  # total_cost

def test_fix_error_loop_budget_exceeded(temp_files, monkeypatch):
    """Test case for budget exceeded scenario."""
    unit_test_file, code_file, verification_file = temp_files
    
    def mock_fix_errors(*args, **kwargs):
        return True, True, "def test_example():\n    assert 1 == 2", "def example_function():\n    return 1", 2.0
    
    monkeypatch.setattr("fix_error_loop.fix_errors_from_unit_tests", mock_fix_errors)
    
    result = fix_error_loop(unit_test_file, code_file, verification_file, 0.5, 0.7, 3, 1.0)
    
    assert result[0] == False  # success
    assert result[3] == 1  # total_attempts
    assert result[4] == 2.0  # total_cost

def test_fix_error_loop_max_attempts_reached(temp_files, monkeypatch):
    """Test case for maximum attempts reached scenario."""
    unit_test_file, code_file, verification_file = temp_files
    
    def mock_fix_errors(*args, **kwargs):
        return True, True, "def test_example():\n    assert 1 == 2", "def example_function():\n    return 1", 0.1
    
    monkeypatch.setattr("fix_error_loop.fix_errors_from_unit_tests", mock_fix_errors)
    
    result = fix_error_loop(unit_test_file, code_file, verification_file, 0.5, 0.7, 2, 10.0)
    
    assert result[0] == False  # success
    assert result[3] == 2  # total_attempts
    assert result[4] == 0.2  # total_cost
