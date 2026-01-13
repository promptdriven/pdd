"""
Test Plan for pdd.agentic_bug_orchestrator

1. **Happy Path Execution**:
   - Verify that the orchestrator runs through all 10 steps when no hard stops are triggered.
   - Verify that costs are accumulated correctly.
   - Verify that changed files are aggregated correctly.
   - Verify that the final success message is returned.

2. **Hard Stop Conditions**:
   - **Step 1 (Duplicate)**: Verify early exit if output contains "Duplicate of #".
   - **Step 2 (Not a Bug)**: Verify early exit for "Feature Request" or "User Error".
   - **Step 3 (Needs Info)**: Verify early exit for "Needs More Info".
   - **Step 7 (No Test File)**: Verify early exit if no files are generated in step 7.
   - **Step 8 (Verification Failed)**: Verify early exit if output contains "FAIL: Test does not work as expected".

3. **Soft Failures**:
   - Verify that if a step returns `success=False` (from the agent) but does NOT match a hard stop condition, the workflow continues to the next step.

4. **Error Handling**:
   - **Template Loading Failure**: Verify graceful exit if a prompt template cannot be loaded.
   - **Template Formatting Error**: Verify graceful exit if context is missing required keys for the template.

5. **Context Accumulation**:
   - Verify that outputs from previous steps are correctly passed into the context for subsequent steps (e.g., step 2 receives step 1's output).

Note: Z3 formal verification is not applied here as the logic is primarily procedural orchestration of external side effects (LLM calls) and string matching, rather than complex constraint solving or state machine invariants. Unit tests with mocking provide sufficient coverage.
"""

import pytest
from unittest.mock import MagicMock, patch, call
from pathlib import Path
from typing import List, Tuple

# Import the module under test
from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

# --- Fixtures ---


@pytest.fixture
def mock_dependencies(tmp_path):
    """
    Mocks external dependencies:
    - run_agentic_task
    - load_prompt_template
    - console (to suppress output during tests)
    - _setup_worktree (for git worktree isolation)
    """
    # Create a mock worktree path
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree:

        # Default behavior: successful run, generic output
        # Note: run_agentic_task returns 4 values: (success, output, cost, provider)
        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        # Default behavior: return a simple format string
        mock_load.return_value = "Prompt for {issue_number}"
        # Default behavior: successful worktree creation
        mock_worktree.return_value = (mock_worktree_path, None)

        yield mock_run, mock_load, mock_console


@pytest.fixture
def default_args(tmp_path):
    """Provides default arguments for the orchestrator function."""
    return {
        "issue_url": "http://github.com/owner/repo/issues/1",
        "issue_content": "Bug description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Bug Title",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True
    }


# --- Tests ---


def test_happy_path_execution(mock_dependencies, default_args):
    """
    Test that all 10 steps execute successfully when no stop conditions are met.
    """
    mock_run, mock_load, _ = mock_dependencies

    # Setup mock to return FILES_CREATED in step 7 output to avoid hard stop
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            # Step 7 outputs FILES_CREATED line which is parsed by orchestrator
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "Investigation complete" in msg
    assert mock_run.call_count == 10
    # Use approx for floating point comparison
    assert cost == pytest.approx(1.0)  # 10 steps × 0.1 each
    assert files == ["test_file.py"]
    assert model == "gpt-4"


def test_hard_stop_step_1_duplicate(mock_dependencies, default_args):
    """
    Test early exit at Step 1 if issue is a duplicate.
    """
    mock_run, _, _ = mock_dependencies

    # Mock step 1 output to trigger hard stop
    mock_run.return_value = (True, "This looks like a Duplicate of #42", 0.05, "claude")

    success, msg, cost, _, _ = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at Step 1" in msg
    assert "duplicate" in msg.lower()
    assert mock_run.call_count == 1
    assert cost == 0.05


def test_hard_stop_step_2_not_a_bug(mock_dependencies, default_args):
    """
    Test early exit at Step 2 if issue is a feature request or user error.
    """
    mock_run, _, _ = mock_dependencies
    
    # Step 1 passes, Step 2 fails
    mock_run.side_effect = [
        (True, "Step 1 ok", 0.1, "model"),
        (True, "Analysis: Feature Request (Not a Bug)", 0.1, "model")
    ]
    
    success, msg, cost, _, _ = run_agentic_bug_orchestrator(**default_args)
    
    assert success is False
    assert "Stopped at Step 2" in msg
    assert "Feature Request" in msg
    assert mock_run.call_count == 2


def test_hard_stop_step_3_needs_info(mock_dependencies, default_args):
    """
    Test early exit at Step 3 if more info is needed.
    """
    mock_run, _, _ = mock_dependencies
    
    # Steps 1-2 pass, Step 3 fails
    mock_run.side_effect = [
        (True, "Step 1 ok", 0.1, "model"),
        (True, "Step 2 ok", 0.1, "model"),
        (True, "Cannot proceed. Needs More Info from user.", 0.1, "model")
    ]
    
    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)
    
    assert success is False
    assert "Stopped at Step 3" in msg
    assert "information" in msg.lower() or "info" in msg.lower()
    assert mock_run.call_count == 3


def test_hard_stop_step_7_no_file_generated(mock_dependencies, default_args):
    """
    Test early exit at Step 7 if no test file is generated.
    """
    mock_run, _, _ = mock_dependencies
    
    # Steps 1-6 pass generic
    # Step 7 returns no FILES_CREATED line
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "I could not generate a test.", 0.1, "model")  # No FILES_CREATED line
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect
    
    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)
    
    assert success is False
    assert "Stopped at Step 7" in msg
    assert "No test file" in msg or "no test" in msg.lower()
    # Should stop at step 7, so 7 calls total
    assert mock_run.call_count == 7


def test_hard_stop_step_8_verification_failed(mock_dependencies, default_args):
    """
    Test early exit at Step 8 if test verification fails.
    """
    mock_run, _, _ = mock_dependencies
    
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test.py", 0.1, "model")
        if label == 'step8':
            return (True, "FAIL: Test does not work as expected", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect
    
    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)
    
    assert success is False
    assert "Stopped at Step 8" in msg
    assert "verification" in msg.lower() or "fail" in msg.lower()
    assert mock_run.call_count == 8


def test_soft_failure_continuation(mock_dependencies, default_args):
    """
    Test that the workflow continues if a step returns success=False 
    but does NOT trigger a hard stop condition string.
    """
    mock_run, _, _ = mock_dependencies
    
    # Step 1 fails (agent error) but no hard stop text
    # Step 7 needs to return a file to avoid hard stop there
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step1':
            return (False, "Agent had a hiccup but produced output", 0.1, "model")
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect
    
    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)
    
    # The overall workflow should succeed because soft failures are allowed
    assert success is True
    assert "Investigation complete" in msg
    assert mock_run.call_count == 10


def test_template_loading_failure(mock_dependencies, default_args):
    """
    Test graceful exit if a prompt template cannot be loaded.
    """
    mock_run, mock_load, _ = mock_dependencies
    
    # Mock template loader to return None for step 1
    mock_load.return_value = None
    
    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)
    
    assert success is False
    assert "prompt template" in msg.lower() or "Missing" in msg
    assert mock_run.call_count == 0


def test_template_formatting_error(mock_dependencies, default_args):
    """
    Test graceful exit if template formatting fails (e.g. missing keys).
    """
    mock_run, mock_load, _ = mock_dependencies
    
    # Return a template that requires a key not present in context
    mock_load.return_value = "This template needs {non_existent_key}"
    
    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)
    
    assert success is False
    assert "formatting error" in msg.lower() or "missing" in msg.lower()
    assert mock_run.call_count == 0


def test_context_accumulation(mock_dependencies, default_args):
    """
    Verify that output from previous steps is passed to subsequent steps via template formatting.
    """
    mock_run, mock_load, _ = mock_dependencies
    
    # We want to verify that step 2 receives step 1's output
    # We need to ensure step 1 template doesn't fail formatting
    def side_effect_load(name):
        if "step1" in name:
            return "Step 1 prompt"
        if "step2" in name:
            return "Context: {step1_output}"
        return "Generic prompt"
    
    mock_load.side_effect = side_effect_load
    
    # Step 1 output
    step1_out = "Output from step 1"
    
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step1':
            return (True, step1_out, 0.1, "model")
        if label == 'step7':
            return (True, "gen\nFILES_CREATED: f.py", 0.1, "model")
        return (True, "ok", 0.1, "model")
        
    mock_run.side_effect = side_effect_run
    
    run_agentic_bug_orchestrator(**default_args)
    
    # Check the call args for step 2
    step2_call = None
    for call_obj in mock_run.call_args_list:
        if call_obj.kwargs.get('label') == 'step2':
            step2_call = call_obj
            break
            
    assert step2_call is not None
    instruction_arg = step2_call.kwargs['instruction']
    # The instruction should have been formatted with step1_output
    assert f"Context: {step1_out}" == instruction_arg


def test_file_accumulation(mock_dependencies, default_args):
    """
    Verify that changed files from multiple steps are accumulated and deduplicated.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            # Only Step 7 reports files via FILES_CREATED
            return (True, "gen\nFILES_CREATED: test.py, repro.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    _, _, _, _, changed_files = run_agentic_bug_orchestrator(**default_args)

    # Should contain both, no duplicates
    assert len(changed_files) == 2
    assert "repro.py" in changed_files
    assert "test.py" in changed_files


def test_step7_files_modified_for_append(mock_dependencies, default_args):
    """
    Test that FILES_MODIFIED marker is parsed correctly when appending to existing test files.

    This supports the PDD methodology where tests should accumulate in existing files
    rather than always creating new ones. Step 6 may recommend appending to an existing
    test file, and Step 7 should use FILES_MODIFIED to indicate the file was modified.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            # Step 7 appends to existing file, uses FILES_MODIFIED instead of FILES_CREATED
            return (True, "Appended test to existing file\nFILES_MODIFIED: tests/test_existing_module.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, _, _, changed_files = run_agentic_bug_orchestrator(**default_args)

    # Should succeed - FILES_MODIFIED is a valid marker for step 7
    assert success is True
    assert "Investigation complete" in msg
    # The modified file should be tracked
    assert "tests/test_existing_module.py" in changed_files
    assert mock_run.call_count == 10


def test_step_timeouts_passed_to_run_agentic_task(mock_dependencies, default_args):
    """
    Test that step-specific timeouts from STEP_TIMEOUTS are passed to run_agentic_task.

    This verifies the fix for Issue #261: Missing timeout parameters caused all steps
    to use the default 240-second timeout instead of step-specific values.
    """
    from pdd.agentic_common import STEP_TIMEOUTS

    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "gen\nFILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    run_agentic_bug_orchestrator(**default_args)

    # Verify timeout is passed for each step
    assert mock_run.call_count == 10

    for call_obj in mock_run.call_args_list:
        label = call_obj.kwargs.get('label', '')
        timeout = call_obj.kwargs.get('timeout')

        # Extract step number from label (e.g., 'step7' -> 7)
        step_num = int(label.replace('step', ''))
        expected_timeout = STEP_TIMEOUTS.get(step_num)

        assert timeout == expected_timeout, (
            f"Step {step_num}: expected timeout={expected_timeout}, got timeout={timeout}"
        )


def test_files_to_stage_passed_to_step10(mock_dependencies, default_args):
    """
    Test that files_to_stage context variable is passed to Step 10 (PR).

    This verifies the fix for Issue #268: The pdd bug command was including
    unrelated files in PRs because the Step 10 prompt didn't have explicit
    file paths to stage. Now the orchestrator passes files_to_stage to Step 10.
    """
    mock_run, mock_load, _ = mock_dependencies

    # Setup templates that use the files_to_stage variable
    def side_effect_load(name):
        if "step10" in name:
            # Step 10 (PR) template uses files_to_stage
            return "Files to stage: {files_to_stage}"
        return "Generic prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "gen\nFILES_CREATED: tests/test_bug_fix.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect_run

    run_agentic_bug_orchestrator(**default_args)

    # Find the Step 10 call and verify files_to_stage was formatted into the prompt
    step10_call = None
    for call_obj in mock_run.call_args_list:
        if call_obj.kwargs.get('label') == 'step10':
            step10_call = call_obj
            break

    assert step10_call is not None, "Step 10 should have been called"
    instruction = step10_call.kwargs['instruction']
    assert instruction == "Files to stage: tests/test_bug_fix.py"


def test_files_to_stage_with_multiple_files(mock_dependencies, default_args):
    """
    Test that multiple files are correctly joined in files_to_stage.

    When Step 7 creates multiple files, all should be listed in files_to_stage
    so the agent knows exactly which files to git add.
    """
    mock_run, mock_load, _ = mock_dependencies

    def side_effect_load(name):
        if "step10" in name:
            return "Stage these: {files_to_stage}"
        return "Generic prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            # Step 7 creates multiple files
            return (True, "gen\nFILES_CREATED: tests/test_bug.py, tests/conftest.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect_run

    run_agentic_bug_orchestrator(**default_args)

    step10_call = None
    for call_obj in mock_run.call_args_list:
        if call_obj.kwargs.get('label') == 'step10':
            step10_call = call_obj
            break

    assert step10_call is not None
    instruction = step10_call.kwargs['instruction']
    # Both files should be in the instruction, comma-separated
    assert "tests/test_bug.py" in instruction
    assert "tests/conftest.py" in instruction


def test_files_to_stage_with_modified_files(mock_dependencies, default_args):
    """
    Test that FILES_MODIFIED files are also included in files_to_stage.

    When appending to existing test files (FILES_MODIFIED), those files
    should also be passed to Step 10 (PR) for staging.
    """
    mock_run, mock_load, _ = mock_dependencies

    def side_effect_load(name):
        if "step10" in name:
            return "Stage: {files_to_stage}"
        return "Generic prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            # Step 7 modifies an existing file
            return (True, "appended\nFILES_MODIFIED: tests/test_existing.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect_run

    run_agentic_bug_orchestrator(**default_args)

    step10_call = None
    for call_obj in mock_run.call_args_list:
        if call_obj.kwargs.get('label') == 'step10':
            step10_call = call_obj
            break

    assert step10_call is not None
    instruction = step10_call.kwargs['instruction']
    assert "tests/test_existing.py" in instruction


def test_hard_stop_step_9_e2e_fail(mock_dependencies, default_args):
    """
    Test early exit at Step 9 if E2E test fails to catch the bug.

    This verifies the hard stop condition for Step 9 (E2E Test):
    If the E2E test doesn't correctly detect the bug, the workflow stops.
    """
    mock_run, mock_load, _ = mock_dependencies

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        if label == 'step9':
            # Step 9 E2E test fails to catch the bug
            return (True, "E2E test ran but...\nE2E_FAIL: Test does not catch bug correctly", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at Step 9" in msg
    assert "E2E test does not catch bug" in msg
    # Should stop at step 9, not reach step 10
    assert mock_run.call_count == 9


def test_e2e_files_accumulated(mock_dependencies, default_args):
    """
    Test that E2E files from Step 9 are added to changed_files.

    When Step 9 creates E2E test files (E2E_FILES_CREATED), those files
    should be included in the changed_files list and passed to Step 10.
    """
    mock_run, mock_load, _ = mock_dependencies

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated unit test\nFILES_CREATED: tests/test_unit.py", 0.1, "gpt-4")
        if label == 'step9':
            return (True, "Generated E2E test\nE2E_FILES_CREATED: tests/e2e/test_e2e_bug.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    # Both unit test and E2E test files should be in changed_files
    assert "tests/test_unit.py" in files
    assert "tests/e2e/test_e2e_bug.py" in files