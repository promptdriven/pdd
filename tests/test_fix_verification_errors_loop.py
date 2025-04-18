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
# Import the module itself to access its members correctly for mocking
import pdd.fix_verification_errors_loop
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
    # Corrected: Pass the actual console object to spy, not a string path.
    mock_console_print = mocker.spy(pdd.fix_verification_errors_loop.console, 'print')


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
        # Handle potentially empty log file
        content_text = log_path.read_text(encoding='utf-8')
        if not content_text.strip():
             # Return an empty root element if the file is empty or whitespace only
             return ET.fromstring("<root></root>")
        content = f"<root>{content_text}</root>"
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
        # Secondary verification is NOT run when success is achieved in step 4i
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
    assert result["total_attempts"] == 1 # Should be 1 attempt made in the loop
    assert result["total_cost"] == 0.001 + 0.002
    assert result["model_name"] == 'model-fixer'
    assert result["final_code"] == env["code_content_fixed"] # Code should be fixed
    assert result["statistics"]["initial_issues"] == 1
    assert result["statistics"]["final_issues"] == 0
    assert result["statistics"]["best_iteration_num"] == 1
    assert result["statistics"]["status_message"] == 'Success on attempt 1'

    # Check mocks called correctly
    assert env["mock_runner"].call_count == 2 # Initial run + Attempt 1 run
    env["mock_runner"].assert_has_calls([
        call(env["program_file"], args=["test_arg"]), # Initial
        call(env["program_file"], args=["test_arg"]), # Attempt 1
        # call(env["verification_file"]),              # Secondary verification - NOT CALLED
    ])
    assert env["mock_fixer"].call_count == 2

    # Check log file
    log_root = read_log_xml(env["log_file"])
    assert log_root.find("InitialState") is not None
    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    assert iter1.find("Status").text == "Success - 0 Issues Found"
    assert iter1.find("SecondaryVerification") is None # Should NOT have run
    # Check action log - should indicate changes applied
    actions = iter1.findall("Action")
    assert any("Applied code changes." in a.text for a in actions)
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
    # Runner sequence: Initial fail, Att 1 fail, Verify 1 pass, Att 2 fail (code updated), Verify 2 pass
    env["mock_runner"].side_effect = [
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Initial
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Att 1 run
        (0, "Verification program running..."),                             # Att 1 verify
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got SLIGHTLY_BETTER_BUG"), # Att 2 run (code was updated after Att 1)
        (0, "Verification program running..."),                             # Att 2 verify (needed because code changed in Att 2 fixer result, even if content is same)
    ]
    # Fixer sequence: Initial (2 issues), Att 1 (1 issue, suggests change), Att 2 (1 issue, suggests same change again)
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
         { # Attempt 2 fix (suggests the same code as attempt 1, still 1 issue)
            'explanation': ["No further ideas"], 'fixed_program': env["program_content"],
            'fixed_code': code_content_attempt1_fix, 'total_cost': 0.003, # Still attempt 1's code suggested
            'model_name': 'model-fixer2', 'verification_issues_count': 1,
        }
    ]

    result = fix_verification_errors_loop(**env["default_args"])

    assert result["success"] is False
    assert result["total_attempts"] == 2 # Reached max attempts
    assert result["total_cost"] == 0.001 + 0.002 + 0.003
    assert result["model_name"] == 'model-fixer2' # Last model used
    # IMPORTANT: Check that the code was restored to the BEST iteration's backup.
    # The best iteration is attempt 1 (1 issue). The backup for attempt 1 was made *before* the fix,
    # so it contains the *initial* code. The function should restore from this backup.
    # The backup path is stored in best_iteration['code_backup']
    best_backup_path = env["output_path"] / "code_module_iteration_1.py"
    assert best_backup_path.exists()
    assert best_backup_path.read_text(encoding="utf-8") == env["code_content_initial"]
    # Check the final state of the main code file
    assert env["code_file"].read_text(encoding="utf-8") == env["code_content_initial"]
    assert result["final_code"] == env["code_content_initial"]

    assert result["statistics"]["initial_issues"] == 2
    assert result["statistics"]["final_issues"] == 1 # Best achieved issues
    assert result["statistics"]["best_iteration_num"] == 1
    assert result["statistics"]["best_iteration_issues"] == 1
    assert "Max attempts (2) reached" in result["statistics"]["status_message"]
    assert "Restored best iteration 1" in result["statistics"]["status_message"]

    # Check mocks
    assert env["mock_runner"].call_count == 5 # Initial, Att1-Run, Att1-Verify, Att2-Run, Att2-Verify
    env["mock_runner"].assert_has_calls([
        call(env["program_file"], args=["test_arg"]), # Initial
        call(env["program_file"], args=["test_arg"]), # Att 1 run
        call(env["verification_file"]),              # Att 1 verify
        call(env["program_file"], args=["test_arg"]), # Att 2 run
        call(env["verification_file"]),              # Att 2 verify (needed because code *was* updated in Att 2 based on fixer result)
    ])
    assert env["mock_fixer"].call_count == 3

    # Check log file for restoration action
    log_root = read_log_xml(env["log_file"])
    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    assert iter1.find("SecondaryVerification[@passed='true']") is not None
    assert iter1.find("Status").text == "Changes Applied (Secondary Verification Passed or Not Needed)"

    iter2 = log_root.find("Iteration[@attempt='2']")
    assert iter2 is not None
    # Check the status of the last iteration (changes were suggested and applied)
    assert iter2.find("SecondaryVerification[@passed='true']") is not None
    assert iter2.find("Status").text == "Changes Applied (Secondary Verification Passed or Not Needed)"

    final_actions = log_root.find("FinalActions")
    assert final_actions is not None
    assert final_actions.find("Action[contains(text(), 'Max attempts')]") is not None
    assert final_actions.find("Action[contains(text(), 'Restored Best Iteration 1')]") is not None

    # Check backups exist
    assert (env["output_path"] / "code_module_iteration_1.py").exists()
    assert (env["output_path"] / "code_module_iteration_2.py").exists()
    # Check content of backups
    assert (env["output_path"] / "code_module_iteration_1.py").read_text(encoding="utf-8") == env["code_content_initial"]
    assert (env["output_path"] / "code_module_iteration_2.py").read_text(encoding="utf-8") == code_content_attempt1_fix


def test_budget_exceeded_in_loop(setup_test_environment):
    """Test exceeding the budget during a loop iteration."""
    env = setup_test_environment
    env["default_args"]["budget"] = 0.0025 # Low budget
    env["default_args"]["max_attempts"] = 3

    # Runner sequence: Initial fail, Att 1 fail, Verify 1 pass (not reached)
    env["mock_runner"].side_effect = [
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Initial
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Att 1 run
        # No secondary verification run as budget exceeded before that step
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
    assert result["total_attempts"] == 1 # Stops after attempt 1 due to budget check *after* fixer call
    assert result["total_cost"] == 0.001 + 0.002
    assert result["model_name"] == 'model-fixer1'
    # Budget exceeded *after* fixer call in attempt 1.
    # Best iteration is attempt 1 (1 issue). Loop breaks.
    # Final step restores best iteration's backup, which is the initial code.
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
    assert iter1.find("SecondaryVerification") is None # Not reached
    final_actions = log_root.find("FinalActions")
    assert final_actions.find("Action[contains(text(), 'Restored Best Iteration 1')]") is not None


def test_secondary_verification_fails_discard(setup_test_environment):
    """Test that changes are discarded if secondary verification fails."""
    env = setup_test_environment

    # Runner sequence: Initial fail, Att 1 fail, Verify 1 FAIL, Att 2 fail (code restored), Verify 2 not run
    env["mock_runner"].side_effect = [
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Initial
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Att 1 run
        (1, "Verification program running...\nSyntax Error!"),              # Att 1 verify FAILS (exit 1)
        # Assume loop continues for another attempt if max_attempts > 1
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Att 2 run (code was restored after Att 1 fail)
        # No secondary verification for Att 2 as no changes suggested by fixer
    ]
    # Fixer sequence: Initial (1 issue), Att 1 (1 issue, suggests change), Att 2 (no change)
    env["mock_fixer"].side_effect = [
        { # Initial assessment
            'explanation': ["Initial bug"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
            'model_name': 'model-init', 'verification_issues_count': 1,
        },
        { # Attempt 1 fix (suggests change, but verification will fail)
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
    # Check that the code file contains the *initial* content, as the fix was discarded in Att 1,
    # and no changes were made in Att 2. Final restoration logic should keep initial state (best_iteration is 0).
    assert env["code_file"].read_text(encoding="utf-8") == env["code_content_initial"]
    assert result["final_code"] == env["code_content_initial"]

    assert result["statistics"]["initial_issues"] == 1
    assert result["statistics"]["final_issues"] == 1 # No improvement recorded
    assert result["statistics"]["best_iteration_num"] == 0 # Best remains initial state
    assert result["statistics"]["best_iteration_issues"] == 1
    # Status message depends on why loop ended. Here, Att 2 suggested no changes.
    assert result["statistics"]["status_message"] == 'No changes suggested on attempt 2 - keeping original state'

    # Check log for discard action
    log_root = read_log_xml(env["log_file"])
    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    assert iter1.find("SecondaryVerification[@passed='false']") is not None
    assert iter1.find("Action").text == "Changes Discarded Due To Secondary Verification Failure"
    assert iter1.find("Status").text == "Changes Discarded"

    iter2 = log_root.find("Iteration[@attempt='2']")
    assert iter2 is not None
    assert iter2.find("Status").text == "No Changes Suggested" # Attempt 2 found no changes
    assert iter2.find("SecondaryVerification") is None # Not run

    final_actions = log_root.find("FinalActions")
    assert final_actions.find("Action[contains(text(), 'No changes suggested')]") is not None
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
    # Check the statistics dictionary is empty as per validation failure return
    assert result["statistics"] == {}


def test_invalid_parameters(setup_test_environment):
    """Test error handling for invalid numerical parameters."""
    env = setup_test_environment
    env["default_args"]["strength"] = 1.5 # Invalid strength

    result = fix_verification_errors_loop(**env["default_args"])

    assert result["success"] is False
    assert result["total_attempts"] == 0
    assert result["total_cost"] == 0.0
    # Check the statistics dictionary is empty as per validation failure return
    assert result["statistics"] == {}
    # Log file should not exist for early validation errors
    assert not env["log_file"].exists()


def test_log_xml_escaping(setup_test_environment):
    """Test that XML special characters in output are escaped in the log."""
    env = setup_test_environment
    malicious_output = "Running...\n<tag>&'\"</tag>\nVERIFICATION_FAILURE"
    malicious_explanation = "Still buggy < > & ' \" `"
    malicious_explanation_list_str = str([malicious_explanation]) # How it gets logged

    # --- Redo test to run one iteration, ending with no changes suggested ---
    env["default_args"]["max_attempts"] = 1
    env["mock_runner"].side_effect = [
         (0, malicious_output), # Initial run
         (0, malicious_output), # Loop attempt 1 run
         # No secondary verify needed as no code change suggested in attempt 1
    ]
    env["mock_fixer"].side_effect = [
        { # Initial assessment
            'explanation': ["Initial bug < > &"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
            'model_name': 'model-init', 'verification_issues_count': 1,
        },
        { # Attempt 1 (suggests no code change, just testing logging)
            'explanation': [malicious_explanation], 'fixed_program': env["program_content"], # No change
            'fixed_code': env["code_content_initial"], 'total_cost': 0.002, # No change
            'model_name': 'model-fixer1', 'verification_issues_count': 1,
        }
    ]

    result = fix_verification_errors_loop(**env["default_args"])
    assert result["success"] is False # No changes suggested in loop
    assert result["total_attempts"] == 1 # Ran one attempt, then stopped due to no changes

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
    assert fixer_result.find("Explanation").text == escape(malicious_explanation_list_str)
    assert fixer_result.find("FixedProgram").text == escape(env["program_content"])
    assert fixer_result.find("FixedCode").text == escape(env["code_content_initial"])
    # Check status reflects no changes suggested
    assert iter1.find("Status").text == "No Changes Suggested"


def test_program_args_passed(setup_test_environment):
    """Verify program_args are passed correctly to _run_program."""
    env = setup_test_environment
    custom_args = ["--input", "file.txt", "--mode=fast"]
    env["default_args"]["program_args"] = custom_args
    # Stop after initial check (which involves one run)
    # Make initial check fail to prevent early exit before loop starts
    env["mock_runner"].return_value = (1, "VERIFICATION_FAILURE")
    env["mock_fixer"].return_value = {
        'explanation': ["Initial fail"], 'fixed_program': "", 'fixed_code': "",
        'total_cost': 0.001, 'model_name': 'm', 'verification_issues_count': 1, # Fail initial check
    }
    # Set max_attempts to 0 to prevent loop execution after initial check
    env["default_args"]["max_attempts"] = 0


    fix_verification_errors_loop(**env["default_args"])

    # Check that the first call to runner (initial state check in Step 3a) used the args
    env["mock_runner"].assert_called_once_with(env["program_file"], args=custom_args)
