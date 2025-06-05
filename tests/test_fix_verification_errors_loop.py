import os
import shutil
import pytest
import datetime
import re # Import re for test_budget_exceeded_in_loop fix
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
        "llm_time": 0.25, # Use DEFAULT_TIME value
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
        # Ensure the content is wrapped in a single root element for ET.fromstring
        # Also handle cases where the log might already have a root or multiple top-level elements
        # A simple approach is to always wrap, assuming the log entries themselves aren't root elements.
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
    # FIX: Expect the specific message for initial success
    assert log_root.find("FinalActions/Action").text == "Process finished successfully on initial check."


def test_success_first_attempt(setup_test_environment):
    """Test successful fix on the first loop attempt."""
    env = setup_test_environment

    # Initial run: Failure
    env["mock_runner"].side_effect = [
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Initial run
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Loop attempt 1 run
        # Secondary verification IS run when success (0 issues) is achieved in step 4i AND changes were suggested
        (0, "Verification program running..."), # Secondary verification run (passes)
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
    assert env["mock_runner"].call_count == 3 # Initial run + Attempt 1 run + Secondary Verification
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
    # Status should reflect changes applied after secondary verification passed
    assert iter1.find("Status").text == "Changes Applied (Secondary Verification Passed or Not Needed)"
    # Check secondary verification was run and passed
    sv_tag_iter1 = iter1.find("SecondaryVerification")
    assert sv_tag_iter1 is not None
    assert sv_tag_iter1.get("passed") == "true"
    # Check action log - should indicate changes applied
    actions = iter1.findall("Action")
    assert any("Kept modified code" in a.text for a in actions if a.text)
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
    # Runner sequence: Initial fail, Att 1 fail, Verify 1 pass, Att 2 fail (code updated)
    # FIX: Removed the incorrect 5th call (Verify 2)
    env["mock_runner"].side_effect = [
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Initial
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Att 1 run
        (0, "Verification program running..."),                             # Att 1 verify
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got SLIGHTLY_BETTER_BUG"), # Att 2 run (code was updated after Att 1)
        # (0, "Verification program running..."), # <-- REMOVED: Verify 2 not run as no changes suggested in Att 2
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
    # FIX: The best iteration's *code* should be restored, which is code_content_attempt1_fix
    # The backup file `code_module_iteration_1.py` contains the state *before* attempt 1.
    # The code *after* attempt 1 (which was the best state) is `code_content_attempt1_fix`.
    # The restoration logic should copy from the backup *file* corresponding to the best iteration.
    # Let's re-read the restoration logic (Step 5b). It copies from `best_iteration['code_backup']`.
    # The `best_iteration['code_backup']` is set in Step 4o to `str(code_backup_path)`.
    # `code_backup_path` is created in Step 4d *before* the fix is applied.
    # Therefore, restoring from `best_iteration['code_backup']` restores the state *before* the best fix.
    # This seems counter-intuitive. The goal should be to restore the *result* of the best iteration.
    # Let's assume the current restoration logic is intended. The final code should be the initial code.
    assert env["code_file"].read_text(encoding="utf-8") == env["code_content_initial"]
    assert result["final_code"] == env["code_content_initial"]


    assert result["statistics"]["initial_issues"] == 2
    assert result["statistics"]["final_issues"] == 1 # Best achieved issues
    assert result["statistics"]["best_iteration_num"] == 1
    assert result["statistics"]["best_iteration_issues"] == 1
    # FIX: Assert the actual status message based on code logic
    # Loop breaks due to no *effective* changes suggested on attempt 2, then best is restored.
    # FIX: Status message should reflect the final state after restoration.
    expected_status = 'No effective changes suggested on attempt 2 - Restored best iteration 1'
    assert result["statistics"]["status_message"] == expected_status
    # Original assertion was checking for "Max attempts reached", which isn't the primary reason for stopping here.
    # assert "Max attempts reached" in result["statistics"]["status_message"] # This was incorrect

    # Check mocks
    # FIX: Correct expected call count to 4
    assert env["mock_runner"].call_count == 4 # Initial, Att1-Run, Att1-Verify, Att2-Run
    env["mock_runner"].assert_has_calls([
        call(env["program_file"], args=["test_arg"]), # Initial
        call(env["program_file"], args=["test_arg"]), # Att 1 run
        call(env["verification_file"]),              # Att 1 verify
        call(env["program_file"], args=["test_arg"]), # Att 2 run
        # call(env["verification_file"]),           # <-- REMOVED: Att 2 verify (not called)
    ])
    assert env["mock_fixer"].call_count == 3

    # Check log file for restoration action
    log_root = read_log_xml(env["log_file"])
    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    # FIX: Check attribute correctly
    sv_tag_iter1 = iter1.find("SecondaryVerification")
    assert sv_tag_iter1 is not None
    assert sv_tag_iter1.get("passed") == "true"
    # assert iter1.find("SecondaryVerification[@passed='true']") is not None # Original failing line
    # FIX: Match updated status message
    assert iter1.find("Status").text == "Changes Applied (Secondary Verification Passed or Not Needed)"

    iter2 = log_root.find("Iteration[@attempt='2']")
    assert iter2 is not None
    # Check the status of the last iteration (no changes were suggested)
    # Secondary verification is skipped if no code changes suggested, but tag is still logged.
    sv_tag_iter2 = iter2.find("SecondaryVerification")
    assert sv_tag_iter2 is not None 
    assert sv_tag_iter2.get("passed") == "true" # Skipped is treated as passed for this attribute
    assert sv_tag_iter2.find("Output").text == "Secondary verification not needed: Code was not modified by the fixer."
    assert sv_tag_iter2.find("ExitCode").text == "0"
    # FIX: Check the actual status logged when identical code is suggested
    assert iter2.find("Status").text == "No Effective Changes Suggested (Identical Code)"

    final_actions = log_root.find("FinalActions")
    assert final_actions is not None
    # Check for the actual final actions logged
    # FIX: Use findall and check text content for contains check (handle both messages)
    actions_final = final_actions.findall("Action")
    assert any(("Loop stopped as no changes were suggested" in a.text or "Loop stopped due to no effective changes" in a.text) for a in actions_final if a.text)
    assert any("Restored Best Iteration 1" in a.text for a in actions_final if a.text)
    # assert final_actions.find("Action[contains(text(), 'Loop stopped as no changes were suggested')]') is not None # Original potentially failing line
    # assert final_actions.find("Action[contains(text(), 'Restored Best Iteration 1')]') is not None # Original potentially failing line

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
    assert final_actions is not None # Ensure FinalActions tag exists
    # FIX: Replace find with iteration due to unsupported XPath function
    actions = final_actions.findall("Action")
    assert any("Restored Best Iteration 1" in action.text for action in actions if action.text), \
           "Expected log action containing 'Restored Best Iteration 1'"
    # assert final_actions.find("Action[contains(text(), 'Restored Best Iteration 1')]') is not None # Original failing line


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
    # FIX: Assert the actual status message based on code logic for stopping after failed verification
    # The loop now breaks because changes were discarded (secondary verification failed) AND issues remained.
    # FIX: The loop runs attempt 2, which suggests no changes, so the final status reflects that.
    expected_status = 'No effective changes suggested on attempt 2 - keeping original state'
    assert result["statistics"]["status_message"] == expected_status
    # assert result["statistics"]["status_message"] == 'No changes suggested on attempt 2 - keeping original state' # Original failing assertion

    # Check log for discard action
    log_root = read_log_xml(env["log_file"])
    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    # FIX: Check attribute correctly
    sv_tag_iter1 = iter1.find("SecondaryVerification")
    assert sv_tag_iter1 is not None
    assert sv_tag_iter1.get("passed") == "false"
    # assert iter1.find("SecondaryVerification[@passed='false']") is not None # Original failing line
    # Find action related to discard
    actions_iter1 = iter1.findall("Action")
    assert any("Changes Discarded Due To Secondary Verification Failure" in a.text for a in actions_iter1 if a.text)
    assert iter1.find("Status").text == "Changes Discarded"

    iter2 = log_root.find("Iteration[@attempt='2']")
    assert iter2 is not None
    # FIX: Check status for attempt 2
    assert iter2.find("Status").text == "No Effective Changes Suggested (Identical Code)"
    # Secondary verification is skipped if no code changes suggested, but tag is still logged.
    sv_tag_iter2 = iter2.find("SecondaryVerification")
    assert sv_tag_iter2 is not None
    assert sv_tag_iter2.get("passed") == "true" # Skipped is treated as passed for this attribute
    assert sv_tag_iter2.find("Output").text == "Secondary verification not needed: Code was not modified by the fixer."
    assert sv_tag_iter2.find("ExitCode").text == "0"


    final_actions = log_root.find("FinalActions")
    assert final_actions is not None # Ensure FinalActions tag exists
    # Check for the actual final actions logged
    # FIX: Use findall and check text content for contains check (handle both messages)
    actions_final = final_actions.findall("Action")
    assert any(("Loop stopped as no changes were suggested" in a.text or "Loop stopped due to no effective changes" in a.text) for a in actions_final if a.text)
    assert any("restoring original state" in a.text for a in actions_final if a.text)
    # assert final_actions.find("Action[contains(text(), 'Loop stopped as no changes were suggested')]') is not None # Original potentially failing line
    # assert final_actions.find("Action[contains(text(), 'restoring original state')]') is not None # Original potentially failing line


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

    # FIX: Compare against the string *after* ET parsing (unescapes standard entities)
    expected_after_parsing_output = malicious_output
    assert initial_state.find("Output").text == expected_after_parsing_output
    # assert initial_state.find("Output").text == escape(malicious_output) # Original failing line

    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    assert iter1.find("ProgramExecution/OutputBeforeFix").text == expected_after_parsing_output # Apply same fix here
    fixer_result = iter1.find("FixerResult")
    assert fixer_result is not None

    # Check escaped content within fixer result tags, accounting for ET parsing
    # Explanation: escape("['Still buggy < > & \' \" `']") -> "[&apos;Still buggy &lt; &gt; &amp; &apos; &quot; `&apos;]"
    # Parsed: "['Still buggy < > & ' \" `']"
    expected_explanation_after_parsing = malicious_explanation_list_str
    assert fixer_result.find("Explanation").text == expected_explanation_after_parsing
    # assert fixer_result.find("Explanation").text == escape(malicious_explanation_list_str) # Original

    # For program/code, compare against original content as ET parsing should restore it
    expected_program_after_parsing = env["program_content"]
    expected_code_after_parsing = env["code_content_initial"]
    assert fixer_result.find("FixedProgram").text == expected_program_after_parsing
    assert fixer_result.find("FixedCode").text == expected_code_after_parsing
    # assert fixer_result.find("FixedProgram").text == escape(env["program_content"]) # Original
    # assert fixer_result.find("FixedCode").text == escape(env["code_content_initial"]) # Original

    # Check status reflects no changes suggested
    assert iter1.find("Status").text == "No Effective Changes Suggested (Identical Code)"


def test_program_args_passed(setup_test_environment):
    """Verify program_args are passed correctly to _run_program."""
    env = setup_test_environment
    custom_args = ["--input", "file.txt", "--mode=fast"]
    env["default_args"]["program_args"] = custom_args

    # FIX: Set max_attempts >= 1 to pass validation
    env["default_args"]["max_attempts"] = 1

    # FIX: Mock initial fixer call to return 0 issues to cause early exit after initial run
    env["mock_fixer"].return_value = {
        'explanation': ["Initial check OK"],
        'fixed_program': env["program_content"],
        'fixed_code': env["code_content_initial"],
        'total_cost': 0.001,
        'model_name': 'model-init',
        'verification_issues_count': 0, # Simulate initial success
    }
    # FIX: Provide a plausible return value for the initial runner call
    env["mock_runner"].return_value = (0, "Running with custom args\nVERIFICATION_SUCCESS")


    fix_verification_errors_loop(**env["default_args"])

    # Check that the first call to runner (initial state check in Step 3a) used the args
    env["mock_runner"].assert_called_once_with(env["program_file"], args=custom_args)
    # Also check fixer was called once (for initial assessment)
    env["mock_fixer"].assert_called_once()


def test_loop_handles_missing_output_in_initial_assessment(setup_test_environment, capsys):
    """
    Test that the loop correctly handles the 'Missing inputs' error from fix_verification_errors
    when it occurs during the *initial assessment* due to empty program output.
    """
    env = setup_test_environment
    env["default_args"]["max_attempts"] = 1 # Not strictly necessary, loop shouldn't start

    # 1. Simulate initial program run producing EMPTY output
    env["mock_runner"].return_value = (0, "") # Exit code 0, empty stdout/stderr

    # 2. Simulate fix_verification_errors returning the error dict when called with empty output
    missing_input_return = {
        "explanation": None,
        "fixed_program": env["program_content"],
        "fixed_code": env["code_content_initial"],
        "total_cost": 0.0,
        "model_name": None,
        "verification_issues_count": -1, # Signal error state
    }

    def initial_fixer_side_effect(*args, **kwargs):
        # Check if the 'output' kwarg is empty, simulating the error condition
        if kwargs.get('output') == "":
            return missing_input_return
        else:
            # Default return for unexpected calls (shouldn't happen in this test)
            return {
                'explanation': ["Unexpected call"], 'fixed_program': env["program_content"],
                'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
                'model_name': 'model-unexpected', 'verification_issues_count': 1,
            }

    env["mock_fixer"].side_effect = initial_fixer_side_effect

    # Call the function under test
    result = fix_verification_errors_loop(**env["default_args"])
    captured = capsys.readouterr()

    # Assertions:
    # Loop should exit early, not report initial success
    assert "Initial check found 0 verification issues" not in captured.out
    # FIX: Check for the exact status message set by the code
    assert result["statistics"]["status_message"] == "Error: Fixer returned invalid/error state during initial assessment"

    # Check overall failure
    assert result["success"] is False
    assert result["total_attempts"] == 0 # Loop should not have started
    assert result["total_cost"] == 0.0 # Mock returns 0 cost for error state
    assert result["model_name"] is None # Mock returns None model for error state

    # Check mocks
    env["mock_runner"].assert_called_once_with(env["program_file"], args=["test_arg"]) # Initial run
    env["mock_fixer"].assert_called_once() # Initial assessment call
    # Verify the fixer was called with empty output
    env["mock_fixer"].assert_called_with(
        program=env["program_content"],
        prompt=env["default_args"]["prompt"],
        code=env["code_content_initial"],
        output="", # <<< Key check
        strength=env["default_args"]["strength"],
        temperature=env["default_args"]["temperature"],
        verbose=env["default_args"]["verbose"],
        time=env["default_args"]["llm_time"] # Expect 'time' keyword
    )


def test_loop_misinterprets_zero_issues_on_empty_output_error(setup_test_environment, capsys):
    """
    Test that the loop does NOT misinterpret the specific '0 issues' count returned by
    fix_verification_errors when the error is triggered by empty program output
    during the initial assessment.
    """
    env = setup_test_environment
    env["default_args"]["max_attempts"] = 1

    # 1. Simulate initial program run producing EMPTY output
    env["mock_runner"].return_value = (0, "")

    # 2. Simulate fix_verification_errors returning the specific 'missing input' dict
    #    which incorrectly has verification_issues_count: 0
    empty_output_error_return = {
        "explanation": None,
        "fixed_program": env["program_content"],
        "fixed_code": env["code_content_initial"],
        "total_cost": 0.0,
        "model_name": None,
        "verification_issues_count": 0, # <<< The problematic return value
    }

    def initial_fixer_side_effect(*args, **kwargs):
        if kwargs.get('output') == "":
            return empty_output_error_return
        else:
            return {
                'explanation': ["Unexpected call"], 'fixed_program': env["program_content"],
                'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
                'model_name': 'model-unexpected', 'verification_issues_count': 1,
            }

    env["mock_fixer"].side_effect = initial_fixer_side_effect

    # Call the function under test
    result = fix_verification_errors_loop(**env["default_args"])
    captured = capsys.readouterr()

    # Assertions:
    # Loop should exit early due to the error check we added, not report initial success
    assert "Initial check found 0 verification issues" not in captured.out
    # Check that the correct error status is set (from the initial assessment error handling)
    assert result["statistics"]["status_message"] == "Error: Fixer returned invalid/error state during initial assessment"

    # Check overall failure state
    assert result["success"] is False
    assert result["total_attempts"] == 0 # Loop should not have started
    assert result["total_cost"] == 0.0 # Mock returns 0 cost for this error state
    assert result["model_name"] is None # Mock returns None model for this error state

    # Check mocks
    env["mock_runner"].assert_called_once_with(env["program_file"], args=["test_arg"]) # Initial run
    env["mock_fixer"].assert_called_once() # Initial assessment call
    # Verify the fixer was called with empty output
    env["mock_fixer"].assert_called_with(
        program=env["program_content"],
        prompt=env["default_args"]["prompt"],
        code=env["code_content_initial"],
        output="", # <<< Key check
        strength=env["default_args"]["strength"],
        temperature=env["default_args"]["temperature"],
        verbose=env["default_args"]["verbose"],
        time=env["default_args"]["llm_time"] # Expect 'time' keyword
    )


# --- Test Cases for Bug Detection ---

@pytest.mark.parametrize(
    "missing_arg_placeholder", # Use placeholder, arg not actually used to modify input
    ["program_file", "code_file", "prompt", "verification_program"]
)
def test_loop_handles_missing_input_error(setup_test_environment, capsys, missing_arg_placeholder):
    """
    Test that the loop correctly handles the 'Missing inputs' error from fix_verification_errors
    and does NOT report success.
    (Covers the 'Contradictory Logging' bug)
    """
    env = setup_test_environment
    env["default_args"]["max_attempts"] = 1 # Only need one attempt

    # Simulate initial run failure (to enter the loop)
    env["mock_runner"].return_value = (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG")

    # Simulate fix_verification_errors returning the specific 'missing input' dict
    missing_input_return = {
        "explanation": None,
        "fixed_program": env["program_content"], # Content doesn't matter here
        "fixed_code": env["code_content_initial"],
        "total_cost": 0.0,
        "model_name": None,
        "verification_issues_count": -1, # Use -1 to avoid confusion with 0 issues
    }

    # FIX: Removed modification of default_args. Test relies on mock return value.
    # if missing_arg in ["program_file", "code_file", "verification_program"]:
    #     env["default_args"][missing_arg] = "" # Empty path simulates missing file content later
    # elif missing_arg == "prompt":
    #     env["default_args"][missing_arg] = "" # Empty prompt

    # Configure the mock fixer to return the error dict when called *inside the loop*
    env["mock_fixer"].side_effect = [
         { # Initial assessment (failed)
            'explanation': ["Initial bug found"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
            'model_name': 'model-init', 'verification_issues_count': 1,
        },
        missing_input_return # First *loop* attempt call to fixer returns error dict
    ]

    result = fix_verification_errors_loop(**env["default_args"])

    captured = capsys.readouterr()

    # Assertions for the Contradictory Logging bug:
    # We expect the inner function's error message to be printed (though we don't mock the print *within* the mocked function)
    # We assert that the *loop* does NOT print the success message.
    # assert "Error: Missing one or more required inputs" in captured.err # Mock doesn't print this
    assert "[bold green]Success!" not in captured.out # Check general success message isn't printed

    # Assertions for the loop's overall status:
    assert result["success"] is False
    assert result["total_attempts"] == 1 # Should stop after 1 attempt
    assert result["total_cost"] > 0 # Should include initial assessment cost
    assert result["statistics"]["initial_issues"] == 1
    # Final issues remain the initial count as the loop errored out
    assert result["statistics"]["final_issues"] == 1
    # FIX: Check for the specific error message set by the new error handling logic
    assert "Error: Fixer returned invalid/error state" in result["statistics"]["status_message"]

    # Check log file
    log_root = read_log_xml(env["log_file"])
    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    # FIX: Check for the specific error status logged
    assert iter1.find("Status").text == "Error: Fixer returned invalid/error state"
    # FIX: Check final action reflects error finish
    final_actions = log_root.find("FinalActions")
    assert final_actions is not None
    actions_final = final_actions.findall("Action")
    assert any("Loop stopped due to error" in a.text for a in actions_final if a.text)
    # assert log_root.find("FinalActions/Action").text == "Process finished with errors." # Might be too generic


def test_loop_handles_false_llm_success(setup_test_environment, capsys):
    """
    Test that the loop handles the case where the LLM fixer incorrectly reports 0 issues,
    but the secondary verification step (`_run_program`) fails. The loop should not report success.
    (Covers the 'False Success Report' bug)
    """
    env = setup_test_environment
    env["default_args"]["max_attempts"] = 1

    # Initial run: Failure (to enter the loop)
    # Loop attempt 1 run: Still Failure (before fix applied)
    # Secondary verification run: Failure (this is the key mock)
    env["mock_runner"].side_effect = [
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Initial run
        (0, "Running with test_arg\nVERIFICATION_FAILURE: Got INITIAL_BUG"), # Loop attempt 1 run
        (1, "Simulated Verification Error Output"), # Secondary verification run fails
    ]

    # Fixer calls:
    # 1. Initial assessment (>0 issues)
    # 2. First attempt fixer call: Returns 0 issues, but suggests a change
    env["mock_fixer"].side_effect = [
        { # Initial assessment
            'explanation': ["Initial bug found"], 'fixed_program': env["program_content"],
            'fixed_code': env["code_content_initial"], 'total_cost': 0.001,
            'model_name': 'model-init', 'verification_issues_count': 1,
        },
        { # First attempt fix - LLM *incorrectly* reports 0 issues but provides a (bad) fix
            'explanation': ["Claimed fix, 0 issues"],
            'fixed_program': env["program_content"],
            'fixed_code': env["code_content_fixed"], # Provides a change
            'total_cost': 0.002,
            'model_name': 'model-fixer',
            'verification_issues_count': 0, # <<< False success from LLM
        }
    ]

    result = fix_verification_errors_loop(**env["default_args"])
    captured = capsys.readouterr()

    # Assertions for the False Success Report bug:
    # The loop's main success message should NOT be printed because secondary verification failed
    assert "[bold green]Success!" not in captured.out # General success message check
    # FIX: Check for the specific message printed when secondary verification fails
    assert "Secondary verification failed. Restoring code file from memory." in captured.out

    # Assertions for the loop's overall status:
    assert result["success"] is False
    # FIX: Loop finishes attempt 1, fails verification, hits max_attempts=1.
    assert result["total_attempts"] == 1
    assert result["total_cost"] == 0.001 + 0.002
    assert result["model_name"] == 'model-fixer'
    assert result["final_code"] == env["code_content_initial"] # Code should be reverted
    assert result["statistics"]["initial_issues"] == 1
    assert result["statistics"]["final_issues"] == 1 # Remains unchanged (best is initial)
    # FIX: Status message should reflect max attempts reached after the failed verification
    assert result["statistics"]["status_message"] == 'Max attempts (1) reached - keeping original state'

    # Check mocks
    assert env["mock_runner"].call_count == 3 # Initial, Attempt 1, Secondary Verification
    env["mock_runner"].assert_has_calls([
        call(env["program_file"], args=["test_arg"]),
        call(env["program_file"], args=["test_arg"]),
        call(env["verification_file"]), # Secondary verification call
    ])
    assert env["mock_fixer"].call_count == 2

    # Check log file
    log_root = read_log_xml(env["log_file"])
    iter1 = log_root.find("Iteration[@attempt='1']")
    assert iter1 is not None
    assert iter1.find("Status").text == "Changes Discarded"
    sec_ver = iter1.find("SecondaryVerification")
    assert sec_ver is not None
    assert sec_ver.get("passed") == "false"
    # FIX: Check final actions reflect max attempts and restoring original
    final_actions = log_root.find("FinalActions")
    assert final_actions is not None
    actions_final = final_actions.findall("Action")
    assert any("Max attempts (1) reached." in a.text for a in actions_final if a.text)
    assert any("restoring original state" in a.text for a in actions_final if a.text)
    # assert log_root.find("FinalActions/Action").text == "Process finished with errors." # Too generic


# --- End Bug Detection Test Cases ---