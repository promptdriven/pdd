"""
Test Plan for pdd.agentic_bug_orchestrator

1. **Happy Path Execution**:
   - Verify that the orchestrator runs through all 11 steps (including 5.5) when no hard stops are triggered.
   - Verify that costs are accumulated correctly.
   - Verify that changed files are aggregated correctly.
   - Verify that the final success message is returned.

2. **Hard Stop Conditions**:
   - **Step 1 (Duplicate)**: Verify early exit if output contains "Duplicate of #".
   - **Step 2 (Not a Bug)**: Verify early exit for "Feature Request" or "User Error".
   - **Step 3 (Needs Info)**: Verify early exit for "Needs More Info".
   - **Step 5.5 (Prompt Review)**: Verify early exit if output contains "PROMPT_REVIEW:".
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
    Test that all 11 steps execute successfully when no stop conditions are met.
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
    assert mock_run.call_count == 11  # 11 steps including step 5.5
    # Use approx for floating point comparison
    assert cost == pytest.approx(1.1)  # 11 steps × 0.1 each
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


def test_hard_stop_step_5_5_prompt_review(mock_dependencies, default_args):
    """
    Test early exit at Step 5.5 if prompt needs human review.
    """
    mock_run, _, _ = mock_dependencies

    # Steps 1-5 pass, Step 5.5 triggers hard stop
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step5_5':
            return (True, "PROMPT_REVIEW: Ambiguous whether to fix code or prompt", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at Step 5.5" in msg
    assert "Ambiguous" in msg or "prompt" in msg.lower()
    # Should stop at step 5.5, so 6 calls (1, 2, 3, 4, 5, 5.5)
    assert mock_run.call_count == 6


def test_step_5_5_prompt_fixed_tracking(mock_dependencies, default_args):
    """
    Test that PROMPT_FIXED: output from step 5.5 is tracked in changed_files.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step5_5':
            return (True, "DEFECT_TYPE: prompt\nPROMPT_FIXED: prompts/my_module_python.prompt", 0.1, "model")
        if label == 'step7':
            return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, _, _, changed_files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    # Both the prompt file and test file should be tracked
    assert "prompts/my_module_python.prompt" in changed_files
    assert "tests/test_fix.py" in changed_files


def test_hard_stop_step_7_no_file_generated(mock_dependencies, default_args):
    """
    Test early exit at Step 7 if no test file is generated.
    """
    mock_run, _, _ = mock_dependencies

    # Steps 1-6 (including 5.5) pass generic
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
    # Should stop at step 7, so 8 calls total (1, 2, 3, 4, 5, 5.5, 6, 7)
    assert mock_run.call_count == 8


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
    # Step 8 is 9th call (1, 2, 3, 4, 5, 5.5, 6, 7, 8)
    assert mock_run.call_count == 9


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
    assert mock_run.call_count == 11  # 11 steps including 5.5


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
    assert mock_run.call_count == 11  # 11 steps including 5.5


def test_step_timeouts_passed_to_run_agentic_task(mock_dependencies, default_args):
    """
    Test that step-specific timeouts from BUG_STEP_TIMEOUTS are passed to run_agentic_task.

    This verifies the fix for Issue #261: Missing timeout parameters caused all steps
    to use the default 240-second timeout instead of step-specific values.

    Note: Per-step timeouts now live in agentic_bug_orchestrator, not agentic_common.
    """
    from pdd.agentic_bug_orchestrator import BUG_STEP_TIMEOUTS

    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "gen\nFILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    run_agentic_bug_orchestrator(**default_args)

    # Verify timeout is passed for each step (11 steps including 5.5)
    assert mock_run.call_count == 11

    for call_obj in mock_run.call_args_list:
        label = call_obj.kwargs.get('label', '')
        timeout = call_obj.kwargs.get('timeout')

        # Extract step number from label (e.g., 'step7' -> 7.0, 'step5_5' -> 5.5)
        step_str = label.replace('step', '').replace('_', '.')
        step_num = float(step_str)
        expected_timeout = BUG_STEP_TIMEOUTS.get(step_num, 340.0)

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
    # Should stop at step 9, not reach step 10 (10 calls: 1, 2, 3, 4, 5, 5.5, 6, 7, 8, 9)
    assert mock_run.call_count == 10


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


# --- Resume Functionality Tests ---


def test_state_save_after_each_step(mock_dependencies, default_args, tmp_path):
    """
    Test that state is saved after each step completes.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Run only 2 steps then fail on step 3
    call_count = [0]
    def side_effect_run(*args, **kwargs):
        call_count[0] += 1
        label = kwargs.get('label', '')
        if label == 'step3':
            # Return "Needs More Info" to trigger hard stop
            return (True, "Needs More Info", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Should have stopped at step 3
    assert success is False
    assert "Step 3" in msg

    # State file should exist with last_completed_step = 2 (hard stop returns BEFORE saving)
    state_dir = _get_state_dir(tmp_path)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"
    assert state_file.exists(), f"State file not found at {state_file}"
    with open(state_file) as f:
        state = json.load(f)
    assert state is not None
    assert state["last_completed_step"] == 2  # Hard stop at step 3 returns before saving step 3
    assert "1" in state["step_outputs"]
    assert "2" in state["step_outputs"]


def test_resume_skips_completed_steps(mock_dependencies, default_args, tmp_path):
    """
    Test that resuming from step 5 skips steps 1-4.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create state file with last_completed_step=4 using new naming convention
    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 4,
        "step_outputs": {
            "1": "Step 1 output",
            "2": "Step 2 output",
            "3": "Step 3 output",
            "4": "Step 4 output",
        },
        "total_cost": 0.4,
        "model_used": "gpt-4",
        "changed_files": [],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(state, f)

    # Mock step 7 to return files
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True

    # Should only call steps 5, 5.5, 6-10 (7 steps), not 1-4
    assert mock_run.call_count == 7

    # Verify the labels of called steps
    called_labels = [call.kwargs['label'] for call in mock_run.call_args_list]
    assert 'step1' not in called_labels
    assert 'step2' not in called_labels
    assert 'step3' not in called_labels
    assert 'step4' not in called_labels
    assert 'step5' in called_labels
    assert 'step5_5' in called_labels
    assert 'step10' in called_labels


def test_state_cleared_on_success(mock_dependencies, default_args, tmp_path):
    """
    Test that state file is deleted on successful completion.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create initial state file using new naming convention
    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "last_completed_step": 0,
        "step_outputs": {},
        "total_cost": 0.0,
        "model_used": "unknown",
        "changed_files": [],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(state, f)

    # Mock step 7 to return files
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True

    # State file should be deleted on success
    assert not state_file.exists()


def test_resume_restores_context(mock_dependencies, default_args, tmp_path):
    """
    Test that resumed runs have access to previous step outputs in context.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create state file with step outputs using new naming convention
    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 2,
        "step_outputs": {
            "1": "Step 1 found no duplicates",
            "2": "Step 2 confirmed it's a bug",
        },
        "total_cost": 0.2,
        "model_used": "gpt-4",
        "changed_files": [],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(state, f)

    # Track the formatted prompts to verify context
    formatted_prompts = []

    def side_effect_load(name):
        # Return a template that includes previous step outputs
        if "step3" in name:
            return "Step 3: Previous outputs are {step1_output} and {step2_output}"
        return "Generic prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    def side_effect_run(instruction, **kwargs):
        formatted_prompts.append(instruction)
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Step 3 should have received the restored context from steps 1 and 2
    step3_prompt = formatted_prompts[0]  # First call is step 3 (steps 1-2 skipped)
    assert "Step 1 found no duplicates" in step3_prompt
    assert "Step 2 confirmed it's a bug" in step3_prompt


def test_failed_step_not_marked_completed(mock_dependencies, default_args, tmp_path):
    """
    Issue #190: Failed steps should not increment last_completed_step in saved state.
    When a step fails, it should be stored as "FAILED: {output}" and last_completed_step
    should remain at the previous step's number.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    saved_states = []

    # Step 6 fails (simulating Gemini timeout/failure)
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        # Parse step number: step5_5 -> 5.5, step6 -> 6
        step_str = label.replace('step', '').replace('_', '.')
        step_num = float(step_str) if '.' in step_str else int(step_str) if step_str else 0
        if step_num == 6:
            return (False, "All agent providers failed", 0.0, "")
        if step_num == 7:
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Step {step_num} output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Capture saved states
    original_save = None
    def capture_state(cwd, issue_number, workflow_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        saved_states.append(state.copy())
        return None

    with patch("pdd.agentic_bug_orchestrator.save_workflow_state", side_effect=capture_state):
        run_agentic_bug_orchestrator(**default_args)

    # Find the state saved after step 6 failed
    step6_state = next((s for s in saved_states if "6" in s.get("step_outputs", {})), None)
    assert step6_state is not None, "State should have been saved after step 6"

    # Key assertion: last_completed_step should be 5.5, not 6 (because step 6 failed)
    # Step 5.5 is the step before step 6
    assert step6_state["last_completed_step"] == 5.5, \
        f"Expected last_completed_step=5.5 after step 6 failed, got {step6_state['last_completed_step']}"

    # The failed output should be prefixed with "FAILED:"
    assert step6_state["step_outputs"]["6"].startswith("FAILED:"), \
        "Failed step output should be prefixed with 'FAILED:'"


def test_resume_reruns_failed_step(mock_dependencies, default_args, tmp_path):
    """
    Issue #190: Resume should re-run a failed step, not skip it.
    If last_completed_step=5 and step 5.5/6 has "FAILED:" output, resume should re-run from step 5.5.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create state file where step 5 completed but step 5.5 failed
    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 5,  # Step 5.5 failed, so last COMPLETED is 5
        "step_outputs": {
            "1": "ok", "2": "ok", "3": "ok", "4": "ok", "5": "ok",
            "5.5": "FAILED: All agent providers failed"  # Failed output stored
        },
        "total_cost": 0.5,
        "model_used": "gpt-4",
        "changed_files": [],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(state, f)

    executed_steps = []

    def track_execution(*args, **kwargs):
        label = kwargs.get('label', '')
        executed_steps.append(label)
        if label == 'step7':
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = track_execution

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Step 5.5 should be re-executed (not skipped) because last_completed_step=5
    assert "step5_5" in executed_steps, \
        f"Step 5.5 should be re-executed on resume, but executed steps were: {executed_steps}"

    # Steps 1-5 should NOT be executed (skipped due to resume)
    assert "step1" not in executed_steps, "Step 1 should be skipped on resume"
    assert "step2" not in executed_steps, "Step 2 should be skipped on resume"
    assert "step3" not in executed_steps, "Step 3 should be skipped on resume"
    assert "step4" not in executed_steps, "Step 4 should be skipped on resume"
    assert "step5" not in executed_steps, "Step 5 should be skipped on resume"

    # Steps 5.5, 6-10 should all be executed (6 steps)
    assert len(executed_steps) == 6, \
        f"Expected 6 steps to be executed (5.5, 6-10), but got {len(executed_steps)}: {executed_steps}"


# --- Issue #352: Worktree Creation Timing Tests ---


def test_worktree_created_before_step_5_5(tmp_path):
    """
    Issue #352: Verify that worktree is created BEFORE step 5.5 runs.

    Bug: Step 5.5 (prompt classification) can edit prompt files when it detects
    a "Prompt Defect" via PROMPT_FIXED marker. However, worktree creation happens
    at Step 7, so prompt edits made by Step 5.5 land on the main branch instead
    of the isolated worktree branch.

    This test verifies that _setup_worktree is called BEFORE the run_agentic_task
    call for step5_5, ensuring any prompt edits happen in the worktree.
    """
    # Track the order of calls
    call_order = []
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree:

        def track_worktree(*args, **kwargs):
            call_order.append(("_setup_worktree", kwargs.get("issue_number")))
            return (mock_worktree_path, None)

        def track_run(*args, **kwargs):
            label = kwargs.get("label", "")
            call_order.append(("run_agentic_task", label))
            if label == "step7":
                return (True, "FILES_CREATED: test.py", 0.1, "model")
            return (True, f"Output for {label}", 0.1, "model")

        mock_worktree.side_effect = track_worktree
        mock_run.side_effect = track_run
        mock_load.return_value = "Prompt for {issue_number}"

        run_agentic_bug_orchestrator(
            issue_url="http://github.com/owner/repo/issues/1",
            issue_content="Bug description",
            repo_owner="owner",
            repo_name="repo",
            issue_number=1,
            issue_author="user",
            issue_title="Bug Title",
            cwd=tmp_path,
            verbose=False,
            quiet=True
        )

    # Find indices of key events
    step5_5_idx = None
    worktree_idx = None

    for i, (call_type, arg) in enumerate(call_order):
        if call_type == "_setup_worktree" and worktree_idx is None:
            worktree_idx = i
        if call_type == "run_agentic_task" and arg == "step5_5":
            step5_5_idx = i

    assert step5_5_idx is not None, "Step 5.5 should have been executed"
    assert worktree_idx is not None, "Worktree should have been created"

    # Key assertion: worktree must be created BEFORE step 5.5 runs
    assert worktree_idx < step5_5_idx, (
        f"Worktree creation (index {worktree_idx}) must happen BEFORE "
        f"step5_5 execution (index {step5_5_idx}). "
        f"Call order: {call_order}"
    )


def test_step_5_5_runs_in_worktree_directory(tmp_path):
    """
    Issue #352: Verify that step 5.5 runs with the worktree path as cwd.

    Bug: Step 5.5 runs with current_cwd pointing to the main repository,
    but it should run in the worktree so that any prompt edits land on the
    isolated branch, not the main branch.
    """
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree:

        mock_worktree.return_value = (mock_worktree_path, None)
        mock_load.return_value = "Prompt for {issue_number}"

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step7":
                return (True, "FILES_CREATED: test.py", 0.1, "model")
            return (True, f"Output for {label}", 0.1, "model")

        mock_run.side_effect = side_effect_run

        run_agentic_bug_orchestrator(
            issue_url="http://github.com/owner/repo/issues/1",
            issue_content="Bug description",
            repo_owner="owner",
            repo_name="repo",
            issue_number=1,
            issue_author="user",
            issue_title="Bug Title",
            cwd=tmp_path,
            verbose=False,
            quiet=True
        )

    # Find the step 5.5 call
    step5_5_call = None
    for call_obj in mock_run.call_args_list:
        if call_obj.kwargs.get("label") == "step5_5":
            step5_5_call = call_obj
            break

    assert step5_5_call is not None, "Step 5.5 should have been called"

    # Key assertion: step 5.5 should run in the worktree, not main repo
    step5_5_cwd = step5_5_call.kwargs.get("cwd")
    assert step5_5_cwd == mock_worktree_path, (
        f"Step 5.5 should run in worktree ({mock_worktree_path}), "
        f"but ran in {step5_5_cwd}"
    )


def test_steps_1_to_5_run_in_main_directory(tmp_path):
    """
    Issue #352 regression test: Steps 1-5 should still run in main directory.

    The fix for #352 should move worktree creation to before Step 5.5,
    but Steps 1-5 should still run in the main directory since they are
    read-only analysis steps that don't modify files.
    """
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree:

        mock_worktree.return_value = (mock_worktree_path, None)
        mock_load.return_value = "Prompt for {issue_number}"

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step7":
                return (True, "FILES_CREATED: test.py", 0.1, "model")
            return (True, f"Output for {label}", 0.1, "model")

        mock_run.side_effect = side_effect_run

        run_agentic_bug_orchestrator(
            issue_url="http://github.com/owner/repo/issues/1",
            issue_content="Bug description",
            repo_owner="owner",
            repo_name="repo",
            issue_number=1,
            issue_author="user",
            issue_title="Bug Title",
            cwd=tmp_path,
            verbose=False,
            quiet=True
        )

    # Verify steps 1-5 ran in main directory (tmp_path)
    main_dir_steps = ["step1", "step2", "step3", "step4", "step5"]
    for call_obj in mock_run.call_args_list:
        label = call_obj.kwargs.get("label", "")
        cwd = call_obj.kwargs.get("cwd")
        if label in main_dir_steps:
            assert cwd == tmp_path, (
                f"Step {label} should run in main directory ({tmp_path}), "
                f"but ran in {cwd}"
            )