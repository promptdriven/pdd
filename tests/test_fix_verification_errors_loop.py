import os
import shutil
import pytest
import datetime
from pathlib import Path
from unittest.mock import MagicMock, call, ANY
from xml.etree import ElementTree as ET
from xml.sax.saxutils import escape

# Ensure the test can find the module in the 'pdd' directory
# This assumes the tests are run from the root directory containing 'pdd' and 'tests'
from pdd.fix_verification_errors_loop import fix_verification_errors_loop, _run_program

# Define paths relative to a temporary directory provided by pytest
OUTPUT_DIR = "output"

# --- Test Fixture ---

@pytest.fixture
def setup_test_environment(tmp_path, mocker):
    """Sets up a temporary environment for testing fix_verification_errors_loop."""
    # Create directories
    pdd_dir = tmp_path / "pdd"
    pdd_dir.mkdir()
    output_path = tmp_path / OUTPUT_DIR
    output_path.mkdir()

    # Create dummy files
    program_content = """
import code_module
import sys
arg = sys.argv[1] if len(sys.argv) > 1 else 'default'
print(f"Running with {arg}")
result = code_module.run()
if result == 'EXPECTED_OK':
    print('VERIFICATION_SUCCESS')
else:
    print(f'VERIFICATION_FAILURE: Got {result}')
"""
    code_content_initial = """
# code_module.py
def run():
    return 'INITIAL_BUG' # Initial buggy state
"""
    code_content_fixed = """
# code_module.py
def run():
    return 'EXPECTED_OK' # Fixed state
"""
    verification_content = """
import sys
# Simple syntax check simulation
print("Verification program running...")
# Simulate success (exit 0) by default
sys.exit(0)
"""

    program_file = output_path / "program.py"
    code_file = output_path / "code_module.py"
    verification_file = output_path / "verify.py"
    log_file = output_path / "test_verification.log"

    program_file.write_text(program_content, encoding="utf-8")
    code_file.write_text(code_content_initial, encoding="utf-8")
    verification_file.write_text(verification_content, encoding="utf-8")

    # Mock dependencies
    mock_fixer = mocker.patch('pdd.fix_verification_errors_loop.fix_verification_errors', autospec=True)
    mock_runner = mocker.patch('pdd.fix_verification_errors_loop._run_program', autospec=True)
    # Mock console print for verbose checks if needed
    mock_console_print = mocker.spy(fix_verification_errors_loop.console, 'print')


    # Default args for the function under test
    default_args = {
        "program_file": str(program_file),
        "code_file": str(code_file),
        "prompt": "Make the code return 'EXPECTED_OK'",
        "verification_program": str(verification_file),
        "strength": 0.5,
        "temperature": 0.1,
        "max_attempts": 3,
        "budget": 0.1,
        "verification_log_file": str(log_file),
        "verbose": False,
        "program_args": ["test_arg"],
    }

    return {
        "tmp_path": tmp_path,
        "output_path": output_path,
        "program_file": program_file,
        "code_file": code_file,
        "verification_file": verification_file,
        "log_file": log_file,
        "program_content": program_content,
        "code_content_initial": code_content_initial,
        "code_content_fixed": code_content_fixed,
        "mock_fixer": mock_fixer,
        "mock_runner": mock_runner,
        "mock_console_print": mock_console_print,
        "default_args": default_args,
    }

# --- Helper Function ---
def read_log_xml(log_path: Path) -> ET.Element:
    """Reads and parses the XML log file."""
    if not log_path.exists():
        pytest.fail(f"Log file not found: {log_path}")
    try:
        # Wrap content in a root element for valid parsing if needed
        content = f"<root>{log_path.read_text(encoding='utf-8')}</root>"
        return ET.fromstring(content)
    except ET.ParseError as e:
        pytest.fail(f"Failed to parse XML log file {log_path}: {e}\nContent:\n{log_path.read_text(encoding='utf-8')}")
    except Exception as e:
         pytest.fail(f"Failed to read log file {log_path}: {e}")


# --- Test Cases ---

def test_initial_success(setup_test_environment):
    """Test the case where the code is already correct initially."""
    env = setup_test_environment
    # Simulate initial program run showing success
    env["mock_runner"].return_value = (0, "Running with test_arg\nVERIFICATION_SUCCESS")
    # Simulate initial fixer call finding 0 issues
    env["mock_fixer"].return_value = {
        'explanation': ["Initial check OK"],
        'fixed_program': env["program_content"],
        'fixed_code': env["code_content_initial"], # Assume initial code was already correct for this test
        'total_cost': 0.001,
        'model_name': 'model-init',
        'verification_issues_count': 0,
    }

    # Make initial code correct for this scenario
    env["code_file"].write_text(env["code_content_fixed"], encoding="utf-8")

    result = fix_verification_errors_loop(**env["default_args"])

    assert result["success"] is True
    assert result["total_attempts"] == 0
    assert result["total_cost"] == 0.001
    assert result["model_name"] == 'model-init'
    assert result["final_code"] == env["code_content_fixed"] # Should remain fixed
    assert result["statistics"]["initial_issues"] == 0
    assert result["statistics"]["final_issues"] == 0
    assert result["statistics"]["status_message"] == 'Success on initial check'

    # Check mocks
    env["mock_runner"].assert_called_once_with(env["program_file"], args=["test_arg"])
    env["mock_fixer"].assert_called_once()

    # Check log file
    log_root = read_log_xml(env["log_file"])
    assert log_root.find("InitialState") is not None
    assert log_root.find("Iteration") is None # No loop iterations
    assert log_root.find("FinalActions/Action").text == "Process finished successfully."


def test_success_first_attempt(setup_test_environment):
    """Test successful fix on the first loop attempt."""
    env = setup_test_environment

    # Initial run: Failure
    env["mock_runner"].side_effect = [
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Initial run
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Loop attempt 1 run
        (0, "Verification program running..."), # Secondary verification
    ]
    # Fixer calls: Initial assessment (>0 issues), First attempt (0 issues, fix suggested)
    env["mock_fixer"].side_effect = [
        { # Initial assessment
            'explanation': ["Initial bug found"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
            'model_name': 'model-init', 'verification_issues_count': 1,
        },
        { # First attempt fix
            'explanation': ["Fixed the bug"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_fixed"], 'total_cost': 0.002,
            'model_name': 'model-fixer', 'verification_issues_count': 0,
        }
    ]

    result = fix_verification_errors_loop(**env["default_args"])

    assert result["success"] is True
    assert result["total_attempts"] == 1
    assert result["total_cost"] == 0.001 + 0.002
    assert result["model_name"] == 'model-fixer'
    assert result["final_code"] == env["code_content_fixed"] # Code should be fixed
    assert result["statistics"]["initial_issues"] == 1
    assert result["statistics"]["final_issues"] == 0
    assert result["statistics"]["best_iteration_num"] == 1
    assert result["statistics"]["status_message"] == 'Success on attempt 1'

    # Check mocks called correctly
    assert env["mock_runner"].call_count == 3
    env["mock_runner"].assert_has_calls([
        call(env["program_file"], args=["test_arg"]), # Initial
        call(env["program_file"], args=["test_arg"]), # Attempt 1
        call(env["verification_file"]),              # Secondary verification
    ])
    assert env["mock_fixer"].call_count == 2

    # Check log file
    log_root = read_log_xml(env["log_file"])
    assert log_root.find("InitialState") is not None
    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    assert iter1.find("Status").text == "Success - 0 Issues Found"
    assert iter1.find("SecondaryVerification[@passed='true']") is not None # Should have run as code changed
    assert iter1.find("Action").text == "Applied code changes." # Check action log
    assert log_root.find("FinalActions/Action").text == "Process finished successfully."

    # Check backup file was created for iteration 1
    backup_code_file = env["output_path"] / "code_module_iteration_1.py"
    assert backup_code_file.exists()
    assert backup_code_file.read_text(encoding="utf-8") == env["code_content_initial"] # Backup holds state *before* fix


def test_max_attempts_reached_with_improvement(setup_test_environment):
    """Test reaching max attempts with some improvement, restoring best."""
    env = setup_test_environment
    env["default_args"]["max_attempts"] = 2

    code_content_attempt1_fix = """
# code_module.py
def run():
    return 'SLIGHTLY_BETTER_BUG' # Attempt 1 fix (still wrong)
"""
    # Runner sequence: Initial fail, Att 1 fail, Att 2 fail, Verify 1 pass, Verify 2 pass
    env["mock_runner"].side_effect = [
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Initial
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Att 1 run
        (0, "Verification program running..."),                             # Att 1 verify
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got SLIGHTLY_BETTER_BUG"), # Att 2 run
        (0, "Verification program running..."),                             # Att 2 verify
    ]
    # Fixer sequence: Initial (2 issues), Att 1 (1 issue, suggests change), Att 2 (1 issue, no change)
    env["mock_fixer"].side_effect = [
        { # Initial assessment
            'explanation': ["Initial bug"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
            'model_name': 'model-init', 'verification_issues_count': 2, # Start with 2 issues
        },
        { # Attempt 1 fix (improves to 1 issue)
            'explanation': ["Partial fix"], 'fixed_program': env["program_content"],
            'fixed_code': code_content_attempt1_fix, 'total_cost': 0.002,
            'model_name': 'model-fixer1', 'verification_issues_count': 1,
        },
         { # Attempt 2 fix (no change suggested, still 1 issue)
            'explanation': ["No further ideas"], 'fixed_program': env["program_content"],
            'fixed_code': code_content_attempt1_fix, 'total_cost': 0.003, # Still attempt 1's code
            'model_name': 'model-fixer2', 'verification_issues_count': 1,
        }
    ]

    result = fix_verification_errors_loop(**env["default_args"])

    assert result["success"] is False
    assert result["total_attempts"] == 2 # Reached max attempts
    assert result["total_cost"] == 0.001 + 0.002 + 0.003
    assert result["model_name"] == 'model-fixer2' # Last model used
    # IMPORTANT: Check that the code was restored to the BEST state (Attempt 1's backup)
    # The state *before* attempt 1 was initial. Attempt 1 produced the best result (1 issue).
    # Since the loop failed, it should restore the state *before* the best attempt, which is the initial code.
    # Let's re-evaluate the logic: The backup is made *before* the fix. The best iteration is attempt 1 (1 issue).
    # The backup associated with attempt 1 is the *initial* code. So it should restore the initial code.
    assert env["code_file"].read_text(encoding="utf-8") == env["code_content_initial"]
    assert result["final_code"] == env["code_content_initial"]

    assert result["statistics"]["initial_issues"] == 2
    assert result["statistics"]["final_issues"] == 1 # Best achieved issues
    assert result["statistics"]["best_iteration_num"] == 1
    assert result["statistics"]["best_iteration_issues"] == 1
    assert "Max attempts (2) reached" in result["statistics"]["status_message"]
    assert "Restored best iteration 1" in result["statistics"]["status_message"]

    # Check mocks
    assert env["mock_runner"].call_count == 5
    assert env["mock_fixer"].call_count == 3

    # Check log file for restoration action
    log_root = read_log_xml(env["log_file"])
    assert log_root.find("Iteration[@attempt='1']") is not None
    assert log_root.find("Iteration[@attempt='2']") is not None
    # Check the status of the last iteration (no changes suggested)
    assert log_root.find("Iteration[@attempt='2']/Status").text == "No Changes Suggested"
    final_actions = log_root.find("FinalActions")
    assert final_actions is not None
    assert final_actions.find("Action[contains(text(), 'Max attempts')]") is not None
    assert final_actions.find("Action[contains(text(), 'Restored Best Iteration 1')]") is not None

    # Check backups exist
    assert (env["output_path"] / "code_module_iteration_1.py").exists()
    assert (env["output_path"] / "code_module_iteration_2.py").exists()


def test_budget_exceeded_in_loop(setup_test_environment):
    """Test exceeding the budget during a loop iteration."""
    env = setup_test_environment
    env["default_args"]["budget"] = 0.0025 # Low budget
    env["default_args"]["max_attempts"] = 3

    # Runner sequence: Initial fail, Att 1 fail, Verify 1 pass
    env["mock_runner"].side_effect = [
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Initial
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Att 1 run
        (0, "Verification program running..."),                             # Att 1 verify
    ]
    # Fixer sequence: Initial (cost 0.001), Att 1 (cost 0.002 - exceeds budget)
    env["mock_fixer"].side_effect = [
        { # Initial assessment
            'explanation': ["Initial bug"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
            'model_name': 'model-init', 'verification_issues_count': 2,
        },
        { # Attempt 1 fix (costly)
            'explanation': ["Trying fix"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_fixed"], 'total_cost': 0.002, # Total cost becomes 0.003
            'model_name': 'model-fixer1', 'verification_issues_count': 1, # Improvement, but budget exceeded
        },
    ]

    result = fix_verification_errors_loop(**env["default_args"])

    assert result["success"] is False
    assert result["total_attempts"] == 1 # Stops after attempt 1 due to budget
    assert result["total_cost"] == 0.001 + 0.002
    assert result["model_name"] == 'model-fixer1'
    # Should restore initial state as attempt 1 exceeded budget before completion?
    # The check happens *after* the fixer call. The attempt completes, logs budget exceeded.
    # Best iteration is attempt 1 (1 issue). Should restore initial code (backup from before attempt 1).
    assert env["code_file"].read_text(encoding="utf-8") == env["code_content_initial"]
    assert result["final_code"] == env["code_content_initial"]

    assert result["statistics"]["initial_issues"] == 2
    assert result["statistics"]["final_issues"] == 1 # Best recorded issue count
    assert result["statistics"]["best_iteration_num"] == 1
    assert result["statistics"]["best_iteration_issues"] == 1
    assert result["statistics"]["status_message"] == 'Budget Exceeded - Restored best iteration 1'

    # Check log
    log_root = read_log_xml(env["log_file"])
    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    assert iter1.find("Status").text == "Budget Exceeded"
    final_actions = log_root.find("FinalActions")
    assert final_actions.find("Action[contains(text(), 'Restored Best Iteration 1')]") is not None


def test_secondary_verification_fails_discard(setup_test_environment):
    """Test that changes are discarded if secondary verification fails."""
    env = setup_test_environment

    # Runner sequence: Initial fail, Att 1 fail, Verify 1 FAIL
    env["mock_runner"].side_effect = [
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Initial
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Att 1 run
        (1, "Verification program running...\nSyntax Error!"),              # Att 1 verify FAILS (exit 1)
        # Assume loop continues for another attempt if max_attempts > 1
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Att 2 run (code was restored)
    ]
    # Fixer sequence: Initial (1 issue), Att 1 (1 issue, suggests change), Att 2 (no change)
    env["mock_fixer"].side_effect = [
        { # Initial assessment
            'explanation': ["Initial bug"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
            'model_name': 'model-init', 'verification_issues_count': 1,
        },
        { # Attempt 1 fix (suggests change)
            'explanation': ["Trying fix"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_fixed"], 'total_cost': 0.002,
            'model_name': 'model-fixer1', 'verification_issues_count': 1, # No improvement in issues here
        },
         { # Attempt 2 (no change suggested, code is back to initial)
            'explanation': ["No ideas"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.003,
            'model_name': 'model-fixer2', 'verification_issues_count': 1,
        },
    ]
    env["default_args"]["max_attempts"] = 2
    result = fix_verification_errors_loop(**env["default_args"])

    assert result["success"] is False
    assert result["total_attempts"] == 2 # Completed 2 attempts
    # Check that the code file contains the *initial* content, as the fix was discarded
    assert env["code_file"].read_text(encoding="utf-8") == env["code_content_initial"]
    assert result["final_code"] == env["code_content_initial"]

    assert result["statistics"]["initial_issues"] == 1
    assert result["statistics"]["final_issues"] == 1 # No improvement recorded
    assert result["statistics"]["best_iteration_num"] == 0 # Best remains initial state
    assert result["statistics"]["best_iteration_issues"] == 1
    assert "Max attempts (2) reached" in result["statistics"]["status_message"] # Reached max attempts
    assert "keeping original state" in result["statistics"]["status_message"] # No improvement found

    # Check log for discard action
    log_root = read_log_xml(env["log_file"])
    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    assert iter1.find("SecondaryVerification[@passed='false']") is not None
    assert iter1.find("Action").text == "Changes Discarded Due To Secondary Verification Failure"
    assert iter1.find("Status").text == "Changes Discarded"

    iter2 = log_root.find("Iteration[@attempt='2']")
    assert iter2.find("Status").text == "No Changes Suggested" # Attempt 2 found no changes

    final_actions = log_root.find("FinalActions")
    assert final_actions.find("Action[contains(text(), 'keeping original state')]") is not None


def test_input_file_not_found(setup_test_environment):
    """Test error handling when an input file is missing."""
    env = setup_test_environment
    env["default_args"]["program_file"] = str(env["tmp_path"] / "non_existent_program.py")

    result = fix_verification_errors_loop(**env["default_args"])

    assert result["success"] is False
    assert result["total_attempts"] == 0
    assert result["total_cost"] == 0.0
    assert not env["log_file"].exists() # Log file shouldn't be created if input validation fails early


def test_invalid_parameters(setup_test_environment):
    """Test error handling for invalid numerical parameters."""
    env = setup_test_environment
    env["default_args"]["strength"] = 1.5 # Invalid strength

    result = fix_verification_errors_loop(**env["default_args"])

    assert result["success"] is False
    assert result["total_attempts"] == 0
    assert result["total_cost"] == 0.0


def test_log_xml_escaping(setup_test_environment):
    """Test that XML special characters in output are escaped in the log."""
    env = setup_test_environment
    malicious_output = "Running...\n<tag>&'\"</tag>\nVERIFICATION_FAILURE"

    env["mock_runner"].return_value = (0, malicious_output) # Initial run fails with special chars
    env["mock_fixer"].return_value = { # Initial assessment
            'explanation': ["Bug found < > &"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
            'model_name': 'model-init', 'verification_issues_count': 1,
    }
    env["default_args"]["max_attempts"] = 0 # Stop after initial assessment

    result = fix_verification_errors_loop(**env["default_args"])

    assert result["success"] is False # Stopped early
    assert env["log_file"].exists()

    log_content = env["log_file"].read_text(encoding='utf-8')
    # Check escaped output in InitialState
    assert escape(malicious_output) in log_content
    # Check escaped explanation in FixerResult (if logged - depends on exact logging format)
    # Let's assume explanation is logged within Iteration 0 / Initial assessment details if available
    # The current code logs initial assessment output but not fixer details unless in a loop.
    # Let's modify the test slightly to run one loop iteration to check fixer result logging.

    # --- Redo test to run one iteration ---
    env["log_file"].unlink() # Remove previous log
    env["default_args"]["max_attempts"] = 1
    env["mock_runner"].side_effect = [
         (0, malicious_output), # Initial run
         (0, malicious_output), # Loop attempt 1 run
         (0, "Verification OK") # Secondary verify
    ]
    env["mock_fixer"].side_effect = [
        { # Initial assessment
            'explanation': ["Initial bug < > &"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
            'model_name': 'model-init', 'verification_issues_count': 1,
        },
        { # Attempt 1 (no fix, just testing logging)
            'explanation': ["Still buggy < > & ' \" `"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.002,
            'model_name': 'model-fixer1', 'verification_issues_count': 1,
        }
    ]

    result = fix_verification_errors_loop(**env["default_args"])
    assert result["success"] is False
    assert result["total_attempts"] == 1

    log_root = read_log_xml(env["log_file"])
    initial_state = log_root.find("InitialState")
    assert initial_state is not None
    assert initial_state.find("Output").text == escape(malicious_output)

    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    assert iter1.find("ProgramExecution/OutputBeforeFix").text == escape(malicious_output)
    fixer_result = iter1.find("FixerResult")
    assert fixer_result is not None
    # Check escaped content within fixer result tags
    assert fixer_result.find("Explanation").text == escape("['Still buggy < > & \' \" `']") # Note: list __str__ adds quotes
    assert fixer_result.find("FixedProgram").text == escape(env["program_content"])
    assert fixer_result.find("FixedCode").text == escape(env["code_content_initial"])


def test_program_args_passed(setup_test_environment):
    """Verify program_args are passed correctly to _run_program."""
    env = setup_test_environment
    custom_args = ["--input", "file.txt", "--mode=fast"]
    env["default_args"]["program_args"] = custom_args
    env["default_args"]["max_attempts"] = 0 # Stop after initial

    # Mock runner and fixer for initial state only
    env["mock_runner"].return_value = (0, "VERIFICATION_SUCCESS")
    env["mock_fixer"].return_value = {
        'explanation': [], 'fixed_program': "", 'fixed_code': "",
        'total_cost': 0.001, 'model_name': 'm', 'verification_issues_count': 0,
    }

    fix_verification_errors_loop(**env["default_args"])

    # Check that the first call to runner (initial state) used the args
    env["mock_runner"].assert_called_once_with(env["program_file"], args=custom_args)
