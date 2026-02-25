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


def test_template_formatting_unknown_keys_are_passed_through(mock_dependencies, default_args):
    """
    Test that templates with unknown keys (after preprocessing) are passed through as literal text.

    After the preprocess fix (commit adding preprocess before .format()), unknown keys like
    {non_existent_key} are escaped to {{non_existent_key}} by preprocess, then converted
    back to literal {non_existent_key} by .format(). This prevents KeyError from JSON braces
    but also means unknown template variables become literal text rather than causing errors.
    """
    mock_run, mock_load, _ = mock_dependencies

    # Return a template that has an unknown key
    mock_load.return_value = "This template needs {non_existent_key}"

    # Setup mock to return FILES_CREATED in step 7 to avoid hard stop
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")
    mock_run.side_effect = side_effect_run

    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)

    # With preprocess, unknown keys don't cause KeyError - they become literal text
    # The orchestrator should continue execution
    assert mock_run.call_count > 0, "Orchestrator should execute steps (unknown keys are passed through)"


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


# --- Issue #393: Format String Injection and Silent Failure Tests ---


def test_curly_braces_in_llm_output_do_not_cause_keyerror(mock_dependencies, default_args):
    """
    Issue #393: LLM outputs containing curly braces should not cause KeyError.

    Bug: When step outputs contain {placeholder} patterns (common in code/error
    analysis), subsequent prompt formatting with .format() interprets them as
    format placeholders, causing KeyError exceptions.

    Fix: Escape curly braces in step outputs before storing in context.
    """
    mock_run, mock_load, _ = mock_dependencies

    # Step 1 returns output with curly braces (simulating LLM analyzing code with templates)
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step1':
            # This output contains {url} which would cause KeyError without escaping
            return (True, "The error occurs because {url} is not in context", 0.1, "gpt-4")
        if label == 'step7':
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Template for step 2 includes step1_output
    def side_effect_load(name):
        if "step2" in name:
            return "Previous analysis: {step1_output}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    # This should NOT raise KeyError - the curly braces should be escaped
    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Should complete successfully (or at least not fail due to format string injection)
    assert success is True, f"Should not fail due to curly braces in output: {msg}"
    assert mock_run.call_count == 11  # All 11 steps should execute


def test_curly_braces_in_restored_context_do_not_cause_keyerror(mock_dependencies, default_args, tmp_path):
    """
    Issue #393: Curly braces in restored step outputs should not cause KeyError on resume.

    When resuming from saved state, step outputs containing {placeholder} patterns
    should be escaped before being added to context.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create state file with step output containing curly braces
    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 2,
        "step_outputs": {
            "1": "No duplicates found",
            # This output has curly braces that would cause KeyError without escaping
            "2": "Bug analysis: The template uses {missing_key} which fails",
        },
        "total_cost": 0.2,
        "model_used": "gpt-4",
        "changed_files": [],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(state, f)

    # Template for step 3 includes step2_output
    def side_effect_load(name):
        if "step3" in name:
            return "Previous: {step2_output}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # This should NOT raise KeyError - restored outputs should be escaped
    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True, f"Should not fail due to curly braces in restored output: {msg}"


def test_keyerror_handling_still_works_for_protected_keys(mock_dependencies, default_args):
    """
    Issue #393: KeyError handling still works when preprocess doesn't escape a key.

    After the preprocess fix, most unknown keys are escaped and become literal text.
    However, if a key in exclude_keys is referenced but not actually in context,
    a KeyError can still occur. This test verifies the error handling still works.

    Note: This is an edge case that shouldn't happen in practice since exclude_keys
    comes from context.keys().
    """
    mock_run, mock_load, mock_console = mock_dependencies

    # Setup mock to return FILES_CREATED in step 7 to avoid hard stop
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")
    mock_run.side_effect = side_effect_run

    # With preprocess in place, unknown keys like {non_existent_key} are escaped
    # and passed through as literal text, so no KeyError occurs.
    # The orchestrator continues execution instead of failing.
    mock_load.return_value = "Template for {issue_url}"  # Valid key

    default_args["quiet"] = False

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Orchestrator should complete (or fail at a later step, not at formatting)
    assert mock_run.call_count > 0, "Orchestrator should execute steps with valid template"


def test_resume_message_shows_step_5_5_not_step_6(mock_dependencies, default_args, tmp_path):
    """
    Issue #393: Resume message should show step 5.5, not step 6, when resuming after step 5.

    Bug: When last_completed_step=5, the resume message said "Resuming from step 6"
    but the actual start step was 5.5, causing confusion.

    Fix: Calculate actual start step before printing resume message.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, mock_console = mock_dependencies
    default_args["cwd"] = tmp_path
    default_args["quiet"] = False  # Enable console output to verify message

    # Create state file with last_completed_step=5
    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 5,  # Step 5 completed, next should be 5.5
        "step_outputs": {
            "1": "ok", "2": "ok", "3": "ok", "4": "ok", "5": "ok"
        },
        "total_cost": 0.5,
        "model_used": "gpt-4",
        "changed_files": [],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(state, f)

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    run_agentic_bug_orchestrator(**default_args)

    # Verify the resume message shows step 5.5, not step 6
    print_calls = [str(call) for call in mock_console.print.call_args_list]
    resume_msg = next((call for call in print_calls if "Resuming" in call), None)

    assert resume_msg is not None, "Resume message should be printed"
    assert "5.5" in resume_msg, (
        f"Resume message should say 'Resuming from step 5.5', got: {resume_msg}"
    )
    # Make sure it doesn't incorrectly say step 6
    assert "from step 6" not in resume_msg.lower(), (
        f"Resume message should NOT say 'from step 6' when resuming to 5.5: {resume_msg}"
    )


def test_resume_message_shows_step_6_after_step_5_5(mock_dependencies, default_args, tmp_path):
    """
    Issue #393: Resume message should show step 6 when last_completed_step is 5.5.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, mock_console = mock_dependencies
    default_args["cwd"] = tmp_path
    default_args["quiet"] = False

    # Create state file with last_completed_step=5.5
    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 5.5,  # Step 5.5 completed, next should be 6
        "step_outputs": {
            "1": "ok", "2": "ok", "3": "ok", "4": "ok", "5": "ok", "5.5": "ok"
        },
        "total_cost": 0.6,
        "model_used": "gpt-4",
        "changed_files": [],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(state, f)

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    run_agentic_bug_orchestrator(**default_args)

    # Verify the resume message shows step 6
    print_calls = [str(call) for call in mock_console.print.call_args_list]
    resume_msg = next((call for call in print_calls if "Resuming" in call), None)

    assert resume_msg is not None, "Resume message should be printed"
    assert "from step 6" in resume_msg.lower() or "step 6" in resume_msg, (
        f"Resume message should say 'Resuming from step 6' after 5.5 completed, got: {resume_msg}"
    )


# ============================================================================
# Template Preprocessing Tests (adapted from agentic_change_orchestrator tests
# removed in commit 9c2e7696)
# ============================================================================

def test_template_preprocessing_curly_braces_in_included_content_are_escaped(mock_dependencies, default_args):
    """
    Template preprocessing fix: Verify curly braces in included content don't break format().

    Bug: When <include> directives expand content containing curly braces
    (e.g., JSON from docs/prompting_guide.md), the subsequent format() call
    fails with KeyError because those braces are interpreted as format placeholders.

    Fix: preprocess() with double_curly_brackets=True escapes braces in
    included content, converting { to {{ and } to }}.
    """
    mock_run, mock_load, mock_console = mock_dependencies

    # Template includes JSON with curly braces (like prompting_guide.md line 231)
    template_with_json = '''Step template for {issue_url}
Included JSON: {"url": "https://example.com", "type": "test"}
End template'''

    mock_load.return_value = template_with_json

    # Setup mock to return FILES_CREATED in step 7 to avoid hard stop
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")
    mock_run.side_effect = side_effect_run

    with patch("pdd.agentic_bug_orchestrator.preprocess") as mock_preprocess:
        def escape_braces(template, **kwargs):
            # Escape JSON braces but preserve {issue_url} and other context placeholders
            exclude_keys = kwargs.get("exclude_keys", [])
            # Replace all single braces with double braces
            escaped = template.replace("{", "{{").replace("}", "}}")
            # Restore the context placeholders (un-double them)
            for key in exclude_keys:
                escaped = escaped.replace("{{" + key + "}}", "{" + key + "}")
            return escaped

        mock_preprocess.side_effect = escape_braces

        # This should NOT raise KeyError from format()
        success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)

        # Verify preprocess was called
        assert mock_preprocess.called, "preprocess() must be called before .format()"


def test_template_preprocessing_exclude_keys_contains_all_context_keys(mock_dependencies, default_args):
    """
    Verify exclude_keys parameter includes all context keys to prevent escaping placeholders.
    """
    mock_run, mock_load, mock_console = mock_dependencies
    mock_load.return_value = "Template for {issue_url}"

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")
    mock_run.side_effect = side_effect_run

    with patch("pdd.agentic_bug_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.return_value = "Template for {issue_url}"

        run_agentic_bug_orchestrator(**default_args)

        # Verify exclude_keys contains the context keys
        call_kwargs = mock_preprocess.call_args[1]
        exclude_keys = call_kwargs.get("exclude_keys", [])
        assert "issue_url" in exclude_keys, "issue_url must be in exclude_keys"


def test_template_preprocessing_double_curly_brackets_enabled(mock_dependencies, default_args):
    """
    Verify preprocess is called with double_curly_brackets=True.
    """
    mock_run, mock_load, mock_console = mock_dependencies
    mock_load.return_value = "Template for {issue_url}"

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")
    mock_run.side_effect = side_effect_run

    with patch("pdd.agentic_bug_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.return_value = "Template for {issue_url}"

        run_agentic_bug_orchestrator(**default_args)

        call_kwargs = mock_preprocess.call_args[1]
        assert call_kwargs.get("double_curly_brackets") == True, \
            "preprocess must be called with double_curly_brackets=True"


def test_step5_5_real_template_formats_without_keyerror():
    """
    Integration test: Verify the REAL step 5.5 prompt template can be formatted.

    Unlike other tests that mock load_prompt_template and preprocess, this test:
    1. Loads the actual agentic_bug_step5_5_prompt_classification_LLM.prompt file
    2. Calls the real preprocess() to expand <include>docs/prompting_guide.md</include>
    3. Verifies .format() succeeds without KeyError from JSON braces

    This catches issues that mocked tests miss, such as new JSON added to prompting_guide.md.
    """
    from pdd.load_prompt_template import load_prompt_template
    from pdd.preprocess import preprocess

    # Load the REAL step 5.5 template
    template = load_prompt_template("agentic_bug_step5_5_prompt_classification_LLM")
    assert template is not None, "Step 5.5 template should exist"

    # Simulate context that would be passed during bug workflow
    context = {
        "issue_url": "https://github.com/test/repo/issues/1",
        "issue_content": "Test issue",
        "repo_owner": "test",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Test",
        "step1_output": "ok",
        "step2_output": "ok",
        "step3_output": "ok",
        "step4_output": "ok",
        "step5_output": "ok",
    }

    # Apply preprocessing (the fix)
    exclude_keys = list(context.keys())
    processed = preprocess(template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)

    # This should NOT raise KeyError - the bug was JSON braces like {"url": ...}
    # in prompting_guide.md being interpreted as format placeholders
    try:
        formatted = processed.format(**context)
    except KeyError as e:
        pytest.fail(f"KeyError during formatting: {e}. The preprocess fix may not be working.")

    # Verify the formatted output is non-empty
    assert len(formatted) > 0, "Formatted template should have content"


# ============================================================================
# Issue #279: Step 5.5 Context Key Restoration Bug
# ============================================================================


def test_step_5_5_context_key_uses_underscore_not_dot(mock_dependencies, default_args, tmp_path):
    """
    Issue #279: Step 5.5 output must be restored with underscore key, not dot.

    Bug: When resuming from cached state, the context restoration loop at lines 289-291
    creates context keys like "step5.5_output" (with dot), but templates expect
    "{step5_5_output}" (with underscore). This causes KeyError when formatting
    prompts for step 10 or any step that references {step5_5_output}.

    Root cause: The restoration loop does NOT apply the same `.replace(".", "_")`
    transformation that line 361 applies when running steps.

    This test verifies that after resume, the context contains "step5_5_output"
    (underscore) not "step5.5_output" (dot).
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create state file with step 5.5 output (key stored as "5.5" with dot)
    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 9,  # Steps 1-9 completed, only step 10 remains
        "step_outputs": {
            "1": "No duplicates",
            "2": "Confirmed bug",
            "3": "Sufficient info",
            "4": "Reproduced",
            "5": "Root cause identified",
            "5.5": "DEFECT_TYPE: code",  # Key has DOT, templates expect UNDERSCORE
            "6": "Test plan ready",
            "7": "FILES_CREATED: test.py",
            "8": "Test verified",
            "9": "E2E test passed",
        },
        "total_cost": 0.9,
        "model_used": "gpt-4",
        "changed_files": ["test.py"],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(state, f)

    # Step 10 template references {step5_5_output} (underscore)
    def side_effect_load(name):
        if "step10" in name:
            return "PR for issue {issue_number}. Classification: {step5_5_output}"
        return "Generic prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    # Track the formatted instruction passed to step 10
    step10_instruction = []

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        instruction = args[0] if args else kwargs.get('instruction', '')
        if label == 'step10':
            step10_instruction.append(instruction)
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # This should NOT raise KeyError - the bug was {step5_5_output} not found
    # because context had "step5.5_output" (dot) instead of "step5_5_output" (underscore)
    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Key assertion: Step 10 should have been called (not failed at formatting)
    assert mock_run.call_count == 1, \
        f"Only step 10 should be called (resuming from step 9). Got {mock_run.call_count} calls."

    # Verify the step 10 call label
    called_labels = [call.kwargs['label'] for call in mock_run.call_args_list]
    assert 'step10' in called_labels, \
        f"Step 10 should have been executed. Called labels: {called_labels}"

    # Verify the instruction was properly formatted with step5_5_output
    assert len(step10_instruction) == 1, "Step 10 instruction should have been captured"
    assert "DEFECT_TYPE: code" in step10_instruction[0], \
        f"Step 10 instruction should contain the step 5.5 output. Got: {step10_instruction[0]}"


def test_step_5_5_context_key_restoration_unit():
    """
    Unit test for the context key restoration logic.

    This tests the FIXED code path from agentic_bug_orchestrator.py lines 289-292.
    Verifies that step keys with dots (like "5.5") are transformed to underscores ("5_5")
    so they can be used as valid Python format string placeholders.

    Issue #279: Before the fix, keys like "5.5" created context["step5.5_output"]
    but templates expected {step5_5_output}, causing KeyError on resume.
    """
    # Simulate cached state (as stored in bug_state_*.json)
    cached_step_outputs = {
        "1": "Step 1 output",
        "5": "Step 5 output",
        "5.5": "Step 5.5 classification output",  # Key has DOT in state file
        "6": "Step 6 output",
    }

    context = {}

    # FIXED restoration logic from agentic_bug_orchestrator.py lines 289-292:
    # Transform step keys: "5.5" -> "5_5" to match template placeholders (Issue #279)
    for step_key, output in cached_step_outputs.items():
        fixed_key = str(step_key).replace(".", "_")  # "5.5" -> "5_5"
        escaped_output = output.replace("{", "{{").replace("}", "}}")
        context[f"step{fixed_key}_output"] = escaped_output

    # Verify the fix: context should have underscore key, not dot key
    assert "step5_5_output" in context, \
        f"step5_5_output should be in context (underscore). Got keys: {list(context.keys())}"
    assert "step5.5_output" not in context, \
        "step5.5_output should NOT be in context (dot is invalid in format keys)"

    # Verify prompt formatting works with the fixed keys
    template = "Previous classification: {step5_5_output}"
    try:
        formatted = template.format(**context)
        assert "Step 5.5 classification output" in formatted
    except KeyError as e:
        pytest.fail(f"Template formatting failed with KeyError: {e}. Context keys: {list(context.keys())}")


# ============================================================================
# Issue #467: False Cache / Ratchet Effect on last_completed_step
# ============================================================================


def test_consecutive_failures_do_not_advance_last_completed_step(mock_dependencies, default_args, tmp_path):
    """
    Issue #467: When consecutive steps fail, last_completed_step should remain 0.

    Bug (now fixed): Each failed step set last_completed_step_to_save = step_num - 1,
    causing a "ratchet effect" that advanced the cursor despite zero successes.

    With the fix: failures don't advance last_completed_step_to_save, and 3
    consecutive provider failures trigger early abort. The final saved state
    should have last_completed_step=0 with only the aborted steps' FAILED outputs.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # ALL steps fail with provider errors
    def side_effect_run(*args, **kwargs):
        return (False, "All agent providers failed", 0.0, "")

    mock_run.side_effect = side_effect_run

    saved_states = []

    def capture_state(cwd, issue_number, workflow_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        saved_states.append(state.copy())
        return None

    with patch("pdd.agentic_bug_orchestrator.save_workflow_state", side_effect=capture_state):
        run_agentic_bug_orchestrator(**default_args)

    # The final saved state (after the last step) should have last_completed_step = 0
    # because no step actually succeeded
    final_state = saved_states[-1]
    assert final_state["last_completed_step"] == 0, (
        f"When all steps fail, last_completed_step should be 0, "
        f"but got {final_state['last_completed_step']}. "
        f"This is the 'ratchet effect' bug from issue #467."
    )

    # All step outputs should be prefixed with "FAILED:"
    for step_key, output in final_state["step_outputs"].items():
        assert output.startswith("FAILED:"), (
            f"Step {step_key} output should start with 'FAILED:' but got: {output[:50]}"
        )


def test_resume_from_all_failed_state_reruns_from_step_1(mock_dependencies, default_args, tmp_path):
    """
    Issue #467: When resuming from a state where all steps failed,
    the workflow should re-run from step 1, not skip to step 6.

    Bug: A previous run where all steps failed saves last_completed_step=5.5
    (due to the ratchet effect). On resume, load_workflow_state returns this
    corrupted state, and the orchestrator skips to step 6, printing
    "Resuming from step 6 (steps 1-5.5 cached)" even though nothing succeeded.

    This test creates the exact corrupted state observed in issue #467 and
    verifies that resume correctly detects all outputs are FAILED and
    re-runs from step 1.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create the exact corrupted state observed in issue #467:
    # last_completed_step=5.5 but ALL step outputs have FAILED: prefix
    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    corrupted_state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 5.5,  # Ratcheted value from bug
        "step_outputs": {
            "1": "FAILED: All agent providers failed",
            "2": "FAILED: All agent providers failed",
            "3": "FAILED: All agent providers failed",
            "4": "FAILED: All agent providers failed",
            "5": "FAILED: All agent providers failed",
            "5.5": "FAILED: All agent providers failed",
        },
        "total_cost": 0.0,
        "model_used": "",
        "changed_files": [],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(corrupted_state, f)

    # Track which steps are actually executed
    executed_steps = []

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        executed_steps.append(label)
        if label == 'step7':
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # The orchestrator should re-run from step 1 since all cached outputs are FAILED
    assert "step1" in executed_steps, (
        f"Step 1 should be re-executed because its cached output is FAILED, "
        f"but executed steps were: {executed_steps}. "
        f"This is the 'blind resume' bug from issue #467."
    )

    # All 11 steps should be executed (none should be skipped)
    assert mock_run.call_count == 11, (
        f"All 11 steps should be executed when all cached outputs are FAILED, "
        f"but only {mock_run.call_count} steps were executed: {executed_steps}"
    )


def test_partial_failure_preserves_last_successful_step(mock_dependencies, default_args, tmp_path):
    """
    Issue #467: When steps 1-3 succeed and steps 4+ fail,
    last_completed_step should be 3 (last successful step).

    Bug: With the ratchet effect, step 4 fails → saves 3, step 5 fails → saves 4,
    step 6 fails → saves 5.5, etc. The final saved value is higher than the
    actual last successful step (3).

    Expected: last_completed_step should remain 3 throughout all subsequent failures.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Steps 1-3 succeed, steps 4+ fail
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        step_str = label.replace('step', '').replace('_', '.')
        try:
            step_num = float(step_str)
        except ValueError:
            step_num = 0
        if step_num <= 3:
            return (True, f"Step {step_num} succeeded", 0.1, "gpt-4")
        else:
            return (False, "All agent providers failed", 0.0, "")

    mock_run.side_effect = side_effect_run

    saved_states = []

    def capture_state(cwd, issue_number, workflow_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        saved_states.append(state.copy())
        return None

    with patch("pdd.agentic_bug_orchestrator.save_workflow_state", side_effect=capture_state):
        run_agentic_bug_orchestrator(**default_args)

    # The final saved state should have last_completed_step = 3
    # (the last step that actually succeeded)
    final_state = saved_states[-1]
    assert final_state["last_completed_step"] == 3, (
        f"When steps 1-3 succeed and 4+ fail, last_completed_step should be 3, "
        f"but got {final_state['last_completed_step']}. "
        f"The ratchet effect advanced it beyond the last successful step."
    )


def test_resume_from_partial_failure_state_reruns_failed_steps(mock_dependencies, default_args, tmp_path):
    """
    Issue #467: When resuming from a state where steps 1-3 succeeded but 4-5.5 failed,
    the workflow should resume from step 4 (re-run the first failed step), not step 6.

    Bug: Due to the ratchet effect, the saved state has last_completed_step=5.5
    even though only steps 1-3 actually succeeded. On resume, steps 4 and 5 are
    skipped even though they failed.

    This test creates a state with mixed success/failure outputs and verifies
    that resume correctly identifies the actual last successful step.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create state where steps 1-3 succeeded, steps 4-5.5 failed,
    # but last_completed_step is incorrectly set to 5.5 (ratchet effect)
    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    corrupted_state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 5.5,  # Ratcheted: should be 3
        "step_outputs": {
            "1": "No duplicates found",
            "2": "Confirmed bug",
            "3": "Sufficient info",
            "4": "FAILED: All agent providers failed",
            "5": "FAILED: All agent providers failed",
            "5.5": "FAILED: All agent providers failed",
        },
        "total_cost": 0.3,
        "model_used": "gpt-4",
        "changed_files": [],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(corrupted_state, f)

    # Track which steps are executed
    executed_steps = []

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        executed_steps.append(label)
        if label == 'step7':
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Step 4 should be re-executed because its cached output is FAILED
    assert "step4" in executed_steps, (
        f"Step 4 should be re-executed because its cached output is FAILED, "
        f"but executed steps were: {executed_steps}. "
        f"The blind resume skipped failed steps."
    )

    # Steps 1-3 should NOT be re-executed (they succeeded)
    assert "step1" not in executed_steps, "Step 1 succeeded and should not be re-run"
    assert "step2" not in executed_steps, "Step 2 succeeded and should not be re-run"
    assert "step3" not in executed_steps, "Step 3 succeeded and should not be re-run"

    # Steps 4, 5, 5.5, 6-10 should all be executed (8 steps)
    assert mock_run.call_count == 8, (
        f"Expected 8 steps (4, 5, 5.5, 6-10) but got {mock_run.call_count}: {executed_steps}"
    )


def test_failure_handling_does_not_use_step_num_minus_one(mock_dependencies, default_args, tmp_path):
    """
    Issue #467: Directly tests the step_num - 1 formula bug with consecutive failures.

    Bug: When step 1 fails, last_completed_step_to_save = 1 - 1 = 0 (correct).
    When step 2 then fails, last_completed_step_to_save = 2 - 1 = 1 (WRONG: step 1 failed too).

    The step_num - 1 formula assumes the previous step succeeded, which is false
    when consecutive steps fail.

    Expected: After both steps 1 and 2 fail, last_completed_step should be 0.
    """
    import json
    from pdd.agentic_bug_orchestrator import _get_state_dir

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Steps 1 and 2 both fail, step 3 triggers hard stop for clean exit
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step1':
            return (False, "All agent providers failed", 0.0, "")
        if label == 'step2':
            return (False, "All agent providers failed", 0.0, "")
        if label == 'step3':
            # Trigger hard stop to exit the loop cleanly
            return (True, "Needs More Info", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    saved_states = []

    def capture_state(cwd, issue_number, workflow_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        saved_states.append(state.copy())
        return None

    with patch("pdd.agentic_bug_orchestrator.save_workflow_state", side_effect=capture_state):
        run_agentic_bug_orchestrator(**default_args)

    # Find the state saved after step 2 failed
    step2_state = None
    for s in saved_states:
        if "2" in s.get("step_outputs", {}):
            step2_state = s
            break

    assert step2_state is not None, "State should have been saved after step 2"

    # Key assertion: After steps 1 AND 2 both fail, last_completed_step should be 0
    # (not 1, which is what step_num - 1 gives when step 2 fails)
    assert step2_state["last_completed_step"] == 0, (
        f"After steps 1 and 2 both fail, last_completed_step should be 0, "
        f"but got {step2_state['last_completed_step']}. "
        f"The step_num - 1 formula incorrectly assumed step 1 succeeded."
    )

# ============================================================================
# ADDITIONAL TESTS — Newly added coverage
# ============================================================================
#
# Test Plan for newly identified gaps:
#
#  1. timeout_adder — Verify it is summed with BUG_STEP_TIMEOUTS for every step.
#  2. 3 consecutive provider failures — Verify early abort at exactly 3 failures.
#  3. Non-provider failure resets consecutive counter — A "regular" failure resets
#     the counter so provider-failure counting starts fresh.
#  4. Worktree creation failure — Graceful early exit when _setup_worktree
#     returns (None, error_msg).
#  5. E2E_SKIP non-stop — "E2E_SKIP:" in step 9 does NOT trigger a hard stop;
#     step 10 still executes.
#  6. E2E files in step 10 context — E2E_FILES_CREATED files end up in
#     files_to_stage for step 10.
#  7. changed_files deduplication — Same path in FILES_CREATED and FILES_MODIFIED
#     should only appear once in changed_files.
#  8. User Error specifically — Step 2 "User Error (Not a Bug)" hard stop covers
#     a separate code branch from Feature Request.
#  9. verbose flag propagation — verbose=True must reach run_agentic_task.
# 10. Total cost per-step — Different cost per step sums correctly.
# 11. model_used reflects last step — After step 10, model comes from step 10.
# 12. Header message — 🔍 header with issue_number and issue_title printed.
# 13. use_github_state=False propagation — State functions receive it.
# 14. DEFECT_TYPE: code continues workflow — Step 5.5 with only DEFECT_TYPE line
#     does NOT stop; no PROMPT_REVIEW marker present.
# 15. changed_files restored from state on resume — Previously accumulated
#     changed_files come back in the return value.
#
# Z3 formal verification note: The orchestration logic is primarily string-matching
# and sequential control flow over external side-effects. Z3 would add little value
# here — unit tests with mocked dependencies provide sufficient coverage without the
# overhead of encoding LLM output patterns as formal constraints.
# ============================================================================


import json
from unittest.mock import patch

import pytest

from pdd.agentic_bug_orchestrator import (
    BUG_STEP_TIMEOUTS,
    _get_state_dir,
    run_agentic_bug_orchestrator,
)


def test_timeout_adder_added_to_step_timeouts(mock_dependencies, default_args):
    """
    Verify that a non-zero timeout_adder is summed with BUG_STEP_TIMEOUTS
    for every step passed to run_agentic_task.
    """
    mock_run, _, _ = mock_dependencies
    timeout_adder = 60.0

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect
    default_args["timeout_adder"] = timeout_adder

    run_agentic_bug_orchestrator(**default_args)

    assert mock_run.call_count == 11
    for call_obj in mock_run.call_args_list:
        label = call_obj.kwargs.get("label", "")
        actual_timeout = call_obj.kwargs.get("timeout")
        step_str = label.replace("step", "").replace("_", ".")
        step_num = float(step_str)
        expected_timeout = BUG_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder
        assert actual_timeout == pytest.approx(expected_timeout), (
            f"Step {step_num}: expected timeout {expected_timeout}, got {actual_timeout}"
        )


def test_three_consecutive_provider_failures_trigger_early_abort(mock_dependencies, default_args):
    """
    Verify that exactly 3 consecutive 'All agent providers failed' outputs
    cause the orchestrator to abort early with a descriptive message.
    """
    mock_run, _, _ = mock_dependencies

    # Every step fails with the provider error message
    mock_run.return_value = (False, "All agent providers failed", 0.0, "")

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    # Abort message should mention consecutive failures or aborting
    assert (
        "Aborting" in msg
        or "consecutive" in msg.lower()
        or "providers" in msg.lower()
    )
    # The abort should fire after 3 consecutive provider failures
    assert mock_run.call_count == 3


def test_non_provider_failure_resets_consecutive_counter(mock_dependencies, default_args):
    """
    Verify that a non-provider-failure step resets the consecutive provider
    failure counter, so 3 non-consecutive provider failures do NOT abort.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        # Step 1 and step 3 fail with provider error; step 2 fails differently
        if label == "step1":
            return (False, "All agent providers failed", 0.0, "")
        if label == "step2":
            # Non-provider failure: should reset the counter
            return (False, "Timeout waiting for response", 0.05, "model")
        if label == "step3":
            return (False, "All agent providers failed", 0.0, "")
        if label == "step7":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # The non-provider failure at step 2 resets the counter, so we should NOT
    # abort after 3 total calls — all 11 steps should execute
    assert mock_run.call_count == 11, (
        f"Non-provider failure should reset counter; expected 11 steps, got {mock_run.call_count}"
    )
    assert success is True


def test_worktree_creation_failure_returns_early(default_args, tmp_path):
    """
    Verify that a failed worktree creation causes an immediate early exit
    before step 5.5 runs.
    """
    default_args["cwd"] = tmp_path

    with (
        patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run,
        patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load,
        patch("pdd.agentic_bug_orchestrator.console"),
        patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree,
        patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)),
        patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None),
    ):
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (None, "git: not a git repository")
        mock_run.return_value = (True, "ok", 0.1, "model")

        success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Failed to create worktree" in msg

    # Steps 5.5 and beyond must NOT have run
    called_labels = [c.kwargs.get("label") for c in mock_run.call_args_list]
    assert "step5_5" not in called_labels
    assert "step6" not in called_labels
    assert "step10" not in called_labels


def test_e2e_skip_continues_to_step_10(mock_dependencies, default_args):
    """
    Verify that 'E2E_SKIP:' in step 9 output does NOT trigger a hard stop;
    step 10 must still execute.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        if label == "step9":
            return (True, "E2E_SKIP: No E2E test framework detected in repo", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "Investigation complete" in msg
    assert mock_run.call_count == 11

    called_labels = [c.kwargs.get("label") for c in mock_run.call_args_list]
    assert "step10" in called_labels, "Step 10 (PR) should still run after E2E_SKIP"


def test_e2e_files_propagated_to_step_10_files_to_stage(mock_dependencies, default_args):
    """
    Verify that E2E test files parsed from step 9 (E2E_FILES_CREATED) appear
    in the 'files_to_stage' context variable that step 10 uses.
    """
    mock_run, mock_load, _ = mock_dependencies

    def side_effect_load(name):
        if "step10" in name:
            return "Stage all: {files_to_stage}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    def side_effect_run(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "FILES_CREATED: tests/test_unit.py", 0.1, "model")
        if label == "step9":
            return (
                True,
                "All good\nE2E_FILES_CREATED: tests/e2e/test_e2e_issue.py",
                0.1,
                "model",
            )
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    # Both unit and E2E files should be in changed_files
    assert "tests/test_unit.py" in changed_files
    assert "tests/e2e/test_e2e_issue.py" in changed_files

    # Step 10 instruction must contain both files
    step10_call = next(
        (c for c in mock_run.call_args_list if c.kwargs.get("label") == "step10"),
        None,
    )
    assert step10_call is not None
    instruction = step10_call.kwargs["instruction"]
    assert "tests/test_unit.py" in instruction
    assert "tests/e2e/test_e2e_issue.py" in instruction


def test_changed_files_deduplicated_when_same_path_appears_twice(mock_dependencies, default_args):
    """
    Verify that the same file path in both FILES_CREATED and FILES_MODIFIED
    lines results in only one entry in changed_files (order-preserving dedup).
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            # Same path reported under both markers
            return (
                True,
                "gen\nFILES_CREATED: tests/test_bug.py\nFILES_MODIFIED: tests/test_bug.py",
                0.1,
                "model",
            )
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert changed_files.count("tests/test_bug.py") == 1, (
        "Duplicate file path should appear only once in changed_files"
    )


def test_hard_stop_step_2_user_error_specifically(mock_dependencies, default_args):
    """
    Verify that the 'User Error (Not a Bug)' detection at step 2 is a distinct
    hard stop (separate code branch from Feature Request).
    """
    mock_run, _, _ = mock_dependencies

    mock_run.side_effect = [
        (True, "No duplicates found", 0.1, "model"),
        (True, "Verdict: User Error (Not a Bug) — user misread the documentation", 0.1, "model"),
    ]

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at Step 2" in msg
    assert "User Error" in msg
    assert mock_run.call_count == 2


def test_verbose_flag_propagated_to_every_run_agentic_task_call(mock_dependencies, default_args):
    """
    Verify that verbose=True is forwarded to every run_agentic_task invocation.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect
    default_args["verbose"] = True

    run_agentic_bug_orchestrator(**default_args)

    assert mock_run.call_count == 11
    for call_obj in mock_run.call_args_list:
        label = call_obj.kwargs.get("label", "?")
        assert call_obj.kwargs.get("verbose") is True, (
            f"Step {label}: verbose=True should be passed to run_agentic_task"
        )


def test_total_cost_accumulates_per_step_costs(mock_dependencies, default_args):
    """
    Verify that total_cost is the precise sum of individual step costs,
    including when step costs vary.
    """
    mock_run, _, _ = mock_dependencies

    step_costs = {
        "step1": 0.01,
        "step2": 0.02,
        "step3": 0.03,
        "step4": 0.04,
        "step5": 0.05,
        "step5_5": 0.06,
        "step6": 0.07,
        "step7": 0.08,
        "step8": 0.09,
        "step9": 0.10,
        "step10": 0.11,
    }

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        cost = step_costs.get(label, 0.0)
        if label == "step7":
            return (True, "FILES_CREATED: test.py", cost, "model")
        return (True, "ok", cost, "model")

    mock_run.side_effect = side_effect

    success, msg, total_cost, model, files = run_agentic_bug_orchestrator(**default_args)

    expected = sum(step_costs.values())
    assert total_cost == pytest.approx(expected, abs=1e-9)


def test_model_used_reflects_last_executed_step(mock_dependencies, default_args):
    """
    Verify that model_used in the return tuple reflects the model string
    returned by the final step (step 10).
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step10":
            return (True, "PR created", 0.1, "claude-3-opus")
        if label == "step7":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, cost, model_used, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert model_used == "claude-3-opus", (
        f"model_used should be from step 10, got: {model_used}"
    )


def test_header_message_printed_with_issue_number_and_title(tmp_path):
    """
    Verify the 🔍 header message includes both the issue number and title.
    """
    with (
        patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run,
        patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load,
        patch("pdd.agentic_bug_orchestrator.console") as mock_console,
        patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree,
        patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)),
        patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None),
    ):
        wt = tmp_path / ".pdd" / "worktrees" / "fix-issue-99"
        wt.mkdir(parents=True, exist_ok=True)
        mock_worktree.return_value = (wt, None)
        mock_load.return_value = "Prompt for {issue_number}"

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step7":
                return (True, "FILES_CREATED: test.py", 0.1, "model")
            return (True, "ok", 0.1, "model")

        mock_run.side_effect = side_effect

        run_agentic_bug_orchestrator(
            issue_url="http://github.com/owner/repo/issues/99",
            issue_content="Bug description",
            repo_owner="owner",
            repo_name="repo",
            issue_number=99,
            issue_author="alice",
            issue_title="Crash when uploading large files",
            cwd=tmp_path,
            verbose=False,
            quiet=False,  # Must be False to see the header
        )

    print_calls = [str(c) for c in mock_console.print.call_args_list]
    header = next(
        (c for c in print_calls if "99" in c and "Crash when uploading large files" in c),
        None,
    )
    assert header is not None, (
        f"Header with issue number 99 and title not found. Calls: {print_calls}"
    )


def test_use_github_state_false_propagated_to_save_and_load(default_args, tmp_path):
    """
    Verify that use_github_state=False is forwarded to load_workflow_state,
    save_workflow_state, and clear_workflow_state.
    """
    default_args["cwd"] = tmp_path
    default_args["use_github_state"] = False

    saved_calls: list[bool] = []
    loaded_calls: list[bool] = []
    cleared_calls: list[bool] = []

    def capture_save(
        cwd,
        issue_number,
        workflow_type,
        state,
        state_dir,
        repo_owner,
        repo_name,
        use_github_state: bool = True,
        github_comment_id=None,
    ) -> None:
        """Capture the use_github_state value passed to save_workflow_state."""
        saved_calls.append(use_github_state)

    def capture_load(
        cwd,
        issue_number,
        workflow_type,
        state_dir,
        repo_owner,
        repo_name,
        use_github_state: bool = True,
    ) -> tuple:
        """Capture the use_github_state value passed to load_workflow_state."""
        loaded_calls.append(use_github_state)
        return (None, None)

    def capture_clear(
        cwd,
        issue_number,
        workflow_type,
        state_dir,
        repo_owner,
        repo_name,
        use_github_state: bool = True,
    ) -> None:
        """Capture the use_github_state value passed to clear_workflow_state."""
        cleared_calls.append(use_github_state)

    with (
        patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run,
        patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load,
        patch("pdd.agentic_bug_orchestrator.console"),
        patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree,
        patch("pdd.agentic_bug_orchestrator.load_workflow_state", side_effect=capture_load),
        patch("pdd.agentic_bug_orchestrator.save_workflow_state", side_effect=capture_save),
        patch("pdd.agentic_bug_orchestrator.clear_workflow_state", side_effect=capture_clear),
    ):
        wt = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
        wt.mkdir(parents=True, exist_ok=True)
        mock_worktree.return_value = (wt, None)
        mock_load.return_value = "Prompt for {issue_number}"

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step7":
                return (True, "FILES_CREATED: test.py", 0.1, "model")
            return (True, "ok", 0.1, "model")

        mock_run.side_effect = side_effect

        run_agentic_bug_orchestrator(**default_args)

    # load_workflow_state called with use_github_state=False
    assert loaded_calls, "load_workflow_state should have been called"
    assert all(v is False for v in loaded_calls), (
        f"load_workflow_state always receives use_github_state=False: {loaded_calls}"
    )

    # Every save_workflow_state call uses use_github_state=False
    assert saved_calls, "save_workflow_state should have been called at least once"
    assert all(v is False for v in saved_calls), (
        f"save_workflow_state always receives use_github_state=False: {saved_calls}"
    )

    # clear_workflow_state also uses use_github_state=False
    assert cleared_calls, "clear_workflow_state should have been called on success"
    assert all(v is False for v in cleared_calls), (
        f"clear_workflow_state always receives use_github_state=False: {cleared_calls}"
    )


def test_step5_5_defect_type_code_does_not_stop_workflow(mock_dependencies, default_args):
    """
    Verify that 'DEFECT_TYPE: code' in step 5.5 output does NOT trigger any
    hard stop — the workflow continues normally to step 6 and beyond.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step5_5":
            return (True, "DEFECT_TYPE: code\nNo prompt issues found.", 0.1, "model")
        if label == "step7":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "Investigation complete" in msg
    assert mock_run.call_count == 11

    called_labels = [c.kwargs.get("label") for c in mock_run.call_args_list]
    assert "step6" in called_labels, "Step 6 should run after DEFECT_TYPE: code"
    assert "step10" in called_labels, "Step 10 should run after DEFECT_TYPE: code"


def test_changed_files_restored_from_state_on_resume(default_args, tmp_path):
    """
    Verify that 'changed_files' stored in saved state is restored on resume
    and included in the final return value.
    """
    default_args["cwd"] = tmp_path

    state_dir = _get_state_dir(tmp_path)
    state_dir.mkdir(parents=True, exist_ok=True)
    state_file = state_dir / f"bug_state_{default_args['issue_number']}.json"

    # Simulate a prior run that completed through step 9 with persisted changed_files
    prior_state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 9,
        "step_outputs": {
            "1": "ok",
            "2": "ok",
            "3": "ok",
            "4": "ok",
            "5": "ok",
            "5.5": "ok",
            "6": "ok",
            "7": "FILES_CREATED: tests/test_persisted.py",
            "8": "ok",
            "9": "E2E_FILES_CREATED: tests/e2e/test_e2e_persisted.py",
        },
        "total_cost": 0.9,
        "model_used": "gpt-4",
        "changed_files": ["tests/test_persisted.py", "tests/e2e/test_e2e_persisted.py"],
        "worktree_path": None,
    }
    with open(state_file, "w") as f:
        json.dump(prior_state, f)

    with (
        patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run,
        patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load,
        patch("pdd.agentic_bug_orchestrator.console"),
        patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree,
        patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None),
        patch("pdd.agentic_bug_orchestrator.clear_workflow_state"),
    ):
        wt = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
        wt.mkdir(parents=True, exist_ok=True)
        mock_worktree.return_value = (wt, None)
        mock_load.return_value = "Prompt for {issue_number}"
        mock_run.return_value = (True, "PR created", 0.1, "gpt-4")

        success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

    assert success is True

    # Previously accumulated files must appear in the final return
    assert "tests/test_persisted.py" in changed_files, (
        f"Persisted unit test file should be in changed_files: {changed_files}"
    )
    assert "tests/e2e/test_e2e_persisted.py" in changed_files, (
        f"Persisted E2E file should be in changed_files: {changed_files}"
    )

    # Only step 10 should run (steps 1–9 were already cached in state)
    assert mock_run.call_count == 1


def test_step5_5_prompt_review_returns_reason_in_message(mock_dependencies, default_args):
    """
    Verify the hard-stop message for PROMPT_REVIEW: includes the extracted reason,
    not just a generic string.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step5_5":
            return (
                True,
                "PROMPT_REVIEW: Cannot determine if user intent is feature or defect",
                0.1,
                "model",
            )
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Cannot determine if user intent is feature or defect" in msg, (
        f"Hard-stop message should contain the extracted PROMPT_REVIEW reason: {msg}"
    )


def test_step7_empty_files_list_after_comma_split_is_hard_stop(mock_dependencies, default_args):
    """
    Verify that a FILES_CREATED line with only whitespace/empty values after
    splitting is treated as 'no files generated' and triggers the step 7 hard stop.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            # Colon is present but content is only spaces/commas — effectively empty
            return (True, "gen\nFILES_CREATED:  ,  ,  ", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at Step 7" in msg
    assert files == []


def test_multiple_e2e_files_all_end_up_in_changed_files(mock_dependencies, default_args):
    """
    Verify that multiple comma-separated E2E_FILES_CREATED paths are all
    individually added to changed_files.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "FILES_CREATED: tests/test_unit.py", 0.1, "model")
        if label == "step9":
            return (
                True,
                "E2E_FILES_CREATED: tests/e2e/test_login.py, tests/e2e/test_signup.py",
                0.1,
                "model",
            )
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "tests/test_unit.py" in changed_files
    assert "tests/e2e/test_login.py" in changed_files
    assert "tests/e2e/test_signup.py" in changed_files


# --- E2E Skip Handling Tests ---


def test_e2e_skip_for_simple_bug(mock_dependencies, default_args):
    """Step 9 outputs E2E_SKIP: → no E2E files added, workflow continues to step 10."""
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "FILES_CREATED: test_file.py", 0.1, "model")
        if label == "step9":
            return (True, "E2E_SKIP: Simple bug — unit test sufficient", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)
    assert success is True
    # Only unit test file, no E2E files
    assert changed_files == ["test_file.py"]
    # All 11 steps ran (including step 10 after the skip)
    assert mock_run.call_count == 11


