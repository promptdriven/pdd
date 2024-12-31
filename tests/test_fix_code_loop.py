import os
import shutil
import subprocess
import tempfile
import pytest
from unittest.mock import patch, MagicMock

# Import the function under test
# Adjust the import below if your actual package or file structure is different.
from pdd.fix_code_loop import fix_code_loop

@pytest.fixture
def temp_workspace():
    """
    Creates a temporary directory for test files and cleans up afterward.
    """
    with tempfile.TemporaryDirectory() as tmpdir:
        current_dir = os.getcwd()
        try:
            os.chdir(tmpdir)
            yield tmpdir
        finally:
            os.chdir(current_dir)

def write_file(filename: str, content: str):
    """
    Helper to write content to a file.
    """
    with open(filename, "w", encoding="utf-8") as f:
        f.write(content)

def read_file(filename: str) -> str:
    """
    Helper to read and return content from a file.
    """
    with open(filename, "r", encoding="utf-8") as f:
        return f.read()

@pytest.mark.parametrize("verbose_flag", [True, False])
def test_fix_code_loop_runs_successfully_first_try(temp_workspace, verbose_flag):
    """
    Test that fix_code_loop immediately succeeds when the verification program
    runs without errors. No attempts to "fix" the code should be necessary.
    """
    # Create a dummy verification program that always succeeds
    verification_program_path = "verify_success.py"
    verification_program_text = """
print("Verification passed successfully.")
"""
    write_file(verification_program_path, verification_program_text)

    # Create a dummy code file (though it won't really be run in this scenario)
    code_file_path = "dummy_code.py"
    code_file_text = """
def dummy_function():
    return "OK"
"""
    write_file(code_file_path, code_file_text)

    # Call fix_code_loop
    success, final_program, final_code, total_attempts, total_cost, model_name = fix_code_loop(
        code_file=code_file_path,
        prompt="A dummy prompt",
        verification_program=verification_program_path,
        strength=0.5,
        temperature=0.5,
        max_attempts=3,
        budget=10.0,
        error_log_file="error_code.log",
        verbose=verbose_flag,
    )

    # Validate results
    assert success is True, "The code should have succeeded on the first try."
    assert total_attempts == 0, "No fix attempts should have been made."
    assert total_cost == 0.0, "No cost should be incurred."
    assert "Verification passed successfully." in final_program
    assert "def dummy_function()" in final_code

def test_fix_code_loop_missing_verification_program(temp_workspace):
    """
    Test that fix_code_loop returns an immediate False if the verification
    program does not exist.
    """
    # Create a code file
    code_file_path = "dummy_code.py"
    write_file(code_file_path, "print('Hello from code!')")

    # Provide a verification path that doesn't exist
    verification_program_path = "missing_verify.py"

    success, final_program, final_code, total_attempts, total_cost, model_name = fix_code_loop(
        code_file=code_file_path,
        prompt="Prompt that generated code",
        verification_program=verification_program_path,
        strength=0.5,
        temperature=0.5,
        max_attempts=3,
        budget=10.0,
        error_log_file="error_code.log",
        verbose=False,
    )

    # Validate results
    assert success is False, "Should fail immediately if verification program is missing."
    assert total_attempts == 0, "No attempts should have been made."
    assert total_cost == 0.0, "No cost should be incurred because fix was never called."
    assert final_program == "", "No final program should be returned on failure."
    assert final_code == "", "No final code should be returned on failure."

@patch("pdd.fix_code_loop.fix_code_module_errors")
def test_fix_code_loop_needs_fixing(mock_fix_code_module_errors, temp_workspace):
    """
    Test that fix_code_loop attempts to fix the code when the verification program
    fails. The mock of fix_code_module_errors simulates a single successful fix.
    """
    # Create an initial verification program that fails
    verification_program_path = "verification_fail.py"
    verification_program_text = """
import sys

# We simulate an error
raise ValueError("Simulated verification failure!")
"""
    write_file(verification_program_path, verification_program_text)

    # Create a code file that presumably has an error
    code_file_path = "erroneous_code.py"
    code_file_text = """
def troublesome_function():
    raise Exception("Something is wrong")
"""
    write_file(code_file_path, code_file_text)

    # Mock fix_code_module_errors to simulate a single fix
    def mock_fix(*args, **kwargs):
        return (True, True,  # update_program, update_code
                "print('Fixed verification!')",  # fixed_program
                "def troublesome_function(): return 'All good now!'",  # fixed_code
                0.5,  # cost
                "mock-model-v1"  # model_name
               )

    mock_fix_code_module_errors.side_effect = mock_fix

    success, final_program, final_code, total_attempts, total_cost, model_name = fix_code_loop(
        code_file=code_file_path,
        prompt="Prompt for code that doesn't work",
        verification_program=verification_program_path,
        strength=0.5,
        temperature=0.5,
        max_attempts=5,
        budget=10.0,
        error_log_file="error_code.log",
        verbose=True,
    )

    # Validate results
    assert success is True, "Should succeed after the mock fix is applied."
    # The function attempts once, sees the error, then calls mock fix, so total_attempts should be 1
    assert total_attempts == 1, "Expected exactly one fix attempt."
    assert total_cost == 0.5, "Cost should sum up to the value returned by the mock fix."
    assert "Fixed verification!" in final_program, "Expected the updated verification program."
    assert "All good now!" in final_code, "Expected the updated code content."
    assert model_name == "mock-model-v1", "Should return the mocked model name."

@patch("pdd.fix_code_loop.fix_code_module_errors")
def test_fix_code_loop_exceed_budget(mock_fix_code_module_errors, temp_workspace):
    """
    Test that fix_code_loop stops if the total cost exceeds the budget.
    We simulate multiple failed fixes that each add cost.
    """
    # Create a verification program that fails
    verification_program_path = "verification_fail_budget.py"
    verification_program_text = """
raise RuntimeError("Always fails")
"""
    write_file(verification_program_path, verification_program_text)

    # Create a code file that presumably needs fixes
    code_file_path = "expensive_code.py"
    code_file_text = """
def expensive_problem():
    raise Exception("Needs fixing")
"""
    write_file(code_file_path, code_file_text)

    # The first two attempts each add cost, the third attempt should exceed the budget
    # and cause fix_code_loop to stop.
    def mock_fix(*args, **kwargs):
        return (True, True,
                "print('Still broken verification')",
                "def expensive_problem(): raise Exception('Still not fixed')",
                6.0,  # cost each time
                "expensive-model"
               )

    mock_fix_code_module_errors.side_effect = mock_fix

    success, final_program, final_code, total_attempts, total_cost, model_name = fix_code_loop(
        code_file=code_file_path,
        prompt="Prompt for an expensive fix",
        verification_program=verification_program_path,
        strength=0.5,
        temperature=0.5,
        max_attempts=5,
        budget=10.0,  # Will be exceeded on first fix
        error_log_file="error_code.log",
        verbose=True,
    )

    # Validate results
    assert success is False, "Should fail because the budget was exceeded."
    assert total_attempts == 1, "Only one attempt should be made before exceeding the budget."
    assert total_cost > 10.0, "Total cost should exceed the original budget."
    assert model_name == "expensive-model", "Should report the model name from the mock."

    # Check that the code was restored to the original (since fix eventually failed)
    with open(verification_program_path, "r") as vf:
        restored_verification = vf.read()
    with open(code_file_path, "r") as cf:
        restored_code = cf.read()

    assert "Always fails" in restored_verification, "Original verification program should be restored."
    assert "Needs fixing" in restored_code, "Original code should be restored."
    
def test_fix_code_loop_exceed_max_attempts(temp_workspace):
    """
    Test that fix_code_loop stops if the maximum attempts are reached, even if
    the budget is not exceeded.
    We substitute a failing verification program and no real fix attempts.
    """

    verification_program_path = "verify_to_fail.py"
    write_file(
        verification_program_path,
        "print('Attempting verification...'); raise RuntimeError('It fails every time')"
    )

    code_file_path = "broken_code.py"
    write_file(
        code_file_path,
        "raise Exception('Code is broken')"
    )

    # We patch fix_code_module_errors to do nothing or return no changes repeatedly
    with patch("pdd.fix_code_loop.fix_code_module_errors") as mock_fix:
        # Always return no changes needed - to simulate repeated attempts with no improvement
        mock_fix.return_value = (False, False, "", "", 1.0, "mocked_model")

        success, final_program, final_code, total_attempts, total_cost, model_name = fix_code_loop(
            code_file=code_file_path,
            prompt="Prompt for broken code",
            verification_program=verification_program_path,
            strength=0.5,
            temperature=0.5,
            max_attempts=2,  # Limit attempts
            budget=100.0,    # Substantial budget, so we can check attempts
            error_log_file="error_code.log",
            verbose=False,
        )

        # After each failure, we see no changes needed => fix_code_loop should break immediately,
        # or continue until max_attempts if it tries to bypass "no changes" logic.
        # The code checks for "if not update_program and not update_code" => break immediately.
        # So we may see total_attempts = 1 with success=False if it tries once and sees no changes.
        # This test ensures it doesn't loop infinitely.
        assert success is False, "Should not succeed because errors were never fixed."
        assert total_attempts <= 2, "Should not exceed max_attempts."
        assert total_cost == pytest.approx(1.0, abs=1e-9), (
            "Expected cost is the sum from the single call to fix_code_module_errors."
        )
        assert model_name == "mocked_model", "Should capture the mocked model name."
        assert final_program == "", "Verification program was never updated."
        assert final_code == "", "Code was never updated."