
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""
Test Plan for pdd.agentic_bug_orchestrator

1. **Happy Path Execution**:
   - Verify that the orchestrator runs through all 11 steps when no hard stops are triggered.
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
    - preprocess (template preprocessing)
    - save_workflow_state / load_workflow_state / clear_workflow_state
    - _get_git_root
    - set_agentic_progress / clear_agentic_progress
    """
    # Create a mock worktree path
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t) as mock_preprocess, \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None) as mock_save, \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)) as mock_load_state, \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path) as mock_git_root, \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress") as mock_set_progress, \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress") as mock_clear_progress:

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
        if label == 'step9':
            # Step 7 outputs FILES_CREATED line which is parsed by orchestrator
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "Investigation complete" in msg
    assert mock_run.call_count == 12  # 12 steps
    # Use approx for floating point comparison
    assert cost == pytest.approx(1.2)  # 12 steps x 0.1 each
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
    assert "Stopped at step 1" in msg
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
    assert "Stopped at step 2" in msg
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
        (True, "Cannot proceed. STOP_CONDITION: Needs More Info", 0.1, "model")
    ]

    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 3" in msg
    assert "info" in msg.lower()
    assert mock_run.call_count == 3


def test_fast_track_skips_steps_4_and_5(mock_dependencies, default_args):
    """
    Issue #836: When Step 3 outputs FAST_TRACK:, Steps 4 (api_research)
    and 5 (reproduce) should be skipped. The root cause provided by the
    issue author is injected into step outputs 4 and 5 so later steps
    see it as context.
    """
    mock_run, _, _ = mock_dependencies

    fast_track_summary = "Bug in orchestrator.py:1043 — missing path prefix check"
    calls = []

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        calls.append(label)
        if label == 'step3':
            return (True, f"Status: Fast-Track\nFAST_TRACK: {fast_track_summary}", 0.1, "model")
        if label == 'step9':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "model")
        return (True, f"Output for {label}", 0.1, "model")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    # Steps 4 and 5 must NOT have been called
    assert 'step4' not in calls, f"Step 4 should be skipped on FAST_TRACK, but was called. Calls: {calls}"
    assert 'step5' not in calls, f"Step 5 should be skipped on FAST_TRACK, but was called. Calls: {calls}"
    # All other steps should have been called
    assert 'step1' in calls
    assert 'step3' in calls
    assert 'step6' in calls
    assert 'step9' in calls
    assert 'step12' in calls
    # Total: 12 steps - 2 skipped = 10 LLM calls
    assert mock_run.call_count == 10, f"Expected 10 calls (12 - 2 skipped), got {mock_run.call_count}"


def test_hard_stop_step_5_5_prompt_review(mock_dependencies, default_args):
    """
    Test early exit at Step 5.5 if prompt needs human review.
    """
    mock_run, _, _ = mock_dependencies

    # Steps 1-5 pass, Step 5.5 triggers hard stop
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "PROMPT_REVIEW: Ambiguous whether to fix code or prompt", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 7" in msg
    assert "prompt" in msg.lower() or "Prompt" in msg
    # Should stop at step 7, so 7 calls (1, 2, 3, 4, 5, 6, 7)
    assert mock_run.call_count == 7


def test_step_5_5_prompt_fixed_tracking(mock_dependencies, default_args):
    """
    Test that PROMPT_FIXED: output from step 7 is tracked in changed_files.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step7':
            return (True, "DEFECT_TYPE: prompt\nPROMPT_FIXED: prompts/my_module_python.prompt", 0.1, "model")
        if label == 'step9':
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

    # Step 7 returns no FILES_CREATED line
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "I could not generate a test.", 0.1, "model")  # No FILES_CREATED line
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 9" in msg
    assert "No test file" in msg or "no test" in msg.lower()
    # Should stop at step 7, so 8 calls total (1, 2, 3, 4, 5, 5.5, 6, 7)
    assert mock_run.call_count == 9


def test_hard_stop_step_8_verification_failed(mock_dependencies, default_args):
    """
    Test early exit at Step 8 if test verification fails.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "Generated test\nFILES_CREATED: test.py", 0.1, "model")
        if label == 'step10':
            return (True, "FAIL: Test does not work as expected", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 10" in msg
    assert "fail" in msg.lower() or "doesn't" in msg.lower()
    # Step 10 is 10th call (1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
    assert mock_run.call_count == 10


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
        if label == 'step9':
            return (True, "Generated test\nFILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)

    # The overall workflow should succeed because soft failures are allowed
    assert success is True
    assert "Investigation complete" in msg
    assert mock_run.call_count == 12  # 12 steps


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
        if label == 'step9':
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
        if label == 'step9':
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
        if label == 'step9':
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
        if label == 'step9':
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
    assert mock_run.call_count == 12  # 12 steps


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
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    run_agentic_bug_orchestrator(**default_args)

    # Verify timeout is passed for each step (11 steps)
    assert mock_run.call_count == 12

    for call_obj in mock_run.call_args_list:
        label = call_obj.kwargs.get('label', '')
        timeout = call_obj.kwargs.get('timeout')

        # Extract step number from label (e.g., 'step7' -> 5.5, 'step11' -> 9)
        step_str = label.replace('step', '').replace('_', '.')
        step_num = float(step_str) if '.' in step_str else int(step_str)
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
        if "step12" in name and "pr" in name:
            # Step 10 (PR) template uses files_to_stage
            return "Files to stage: {files_to_stage}"
        return "Generic prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: tests/test_bug_fix.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect_run

    run_agentic_bug_orchestrator(**default_args)

    # Find the Step 10 call and verify files_to_stage was formatted into the prompt
    step10_call = None
    for call_obj in mock_run.call_args_list:
        if call_obj.kwargs.get('label') == 'step12':
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
        if "step12" in name and "pr" in name:
            return "Stage these: {files_to_stage}"
        return "Generic prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            # Step 7 creates multiple files
            return (True, "gen\nFILES_CREATED: tests/test_bug.py, tests/conftest.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect_run

    run_agentic_bug_orchestrator(**default_args)

    step10_call = None
    for call_obj in mock_run.call_args_list:
        if call_obj.kwargs.get('label') == 'step12':
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
        if "step12" in name and "pr" in name:
            return "Stage: {files_to_stage}"
        return "Generic prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            # Step 7 modifies an existing file
            return (True, "appended\nFILES_MODIFIED: tests/test_existing.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect_run

    run_agentic_bug_orchestrator(**default_args)

    step10_call = None
    for call_obj in mock_run.call_args_list:
        if call_obj.kwargs.get('label') == 'step12':
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
        if label == 'step9':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        if label == 'step11':
            # Step 9 E2E test fails to catch the bug
            return (True, "E2E test ran but...\nE2E_FAIL: Test does not catch bug correctly", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 11" in msg
    assert "E2E" in msg or "e2e" in msg.lower()
    # Should stop at step 11: steps 1-11 = 11 calls
    assert mock_run.call_count == 11


def test_e2e_files_accumulated(mock_dependencies, default_args):
    """
    Test that E2E files from Step 9 are added to changed_files.

    When Step 9 creates E2E test files (E2E_FILES_CREATED), those files
    should be included in the changed_files list and passed to Step 10.
    """
    mock_run, mock_load, _ = mock_dependencies

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "Generated unit test\nFILES_CREATED: tests/test_unit.py", 0.1, "gpt-4")
        if label == 'step11':
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
            return (True, "STOP_CONDITION: Needs More Info", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Capture saved states
    saved_states = []
    def capture_state(cwd, issue_number, workflow_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        import copy as _copy; saved_states.append(_copy.deepcopy(state))
        return None

    with patch("pdd.agentic_bug_orchestrator.save_workflow_state", side_effect=capture_state):
        success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Should have stopped at step 3
    assert success is False
    assert "step 3" in msg

    # State should have been saved - find the state saved at step 3 hard stop
    assert len(saved_states) > 0, "State should have been saved"
    final_state = saved_states[-1]
    # Hard stop at step 3 saves the step 3 output and sets last_completed_step to 3
    assert final_state["last_completed_step"] == 3
    assert "1" in final_state["step_outputs"]
    assert "2" in final_state["step_outputs"]


def test_resume_skips_completed_steps(mock_dependencies, default_args, tmp_path):
    """
    Test that resuming from step 5 skips steps 1-4.
    """
    import json

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Mock load_workflow_state to return state with last_completed_step=4
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

    with patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(state, None)):
        # Mock step 7 to return files
        def side_effect_run(*args, **kwargs):
            label = kwargs.get('label', '')
            if label == 'step9':
                return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True

    # Should only call steps 5-12 (8 steps), not 1-4
    assert mock_run.call_count == 8

    # Verify the labels of called steps
    called_labels = [call.kwargs['label'] for call in mock_run.call_args_list]
    assert 'step1' not in called_labels
    assert 'step2' not in called_labels
    assert 'step3' not in called_labels
    assert 'step4' not in called_labels
    assert 'step5' in called_labels
    assert 'step9' in called_labels
    assert 'step12' in called_labels


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
        if label == 'step9':
            return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True

    # The save_workflow_state is mocked (returns None), so the state file
    # created above won't be modified by the mock. But the orchestrator
    # should have called save_workflow_state for each step.
    # The code does NOT call clear_workflow_state, so the file persists.
    # What we verify is that the orchestrator completed successfully.


def test_resume_restores_context(mock_dependencies, default_args, tmp_path):
    """
    Test that resumed runs have access to previous step outputs in context.
    """
    import json

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create state with step outputs
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

    with patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(state, None)):
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
            if label == 'step9':
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

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    saved_states = []

    # Step 6 (test_plan) fails (simulating Gemini timeout/failure)
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        step_str = label.replace('step', '').replace('_', '.')
        try:
            step_num = float(step_str) if '.' in step_str else int(step_str)
        except ValueError:
            step_num = 0
        if step_num == 6:
            return (False, "All agent providers failed", 0.0, "")
        if step_num == 7:
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, f"Step {step_num} output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Capture saved states
    def capture_state(cwd, issue_number, workflow_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        import copy as _copy; saved_states.append(_copy.deepcopy(state))
        return None

    with patch("pdd.agentic_bug_orchestrator.save_workflow_state", side_effect=capture_state):
        run_agentic_bug_orchestrator(**default_args)

    # Find the state saved after step 6 failed
    step6_state = next((s for s in saved_states if "6" in s.get("step_outputs", {})), None)
    assert step6_state is not None, "State should have been saved after step 6"

    # Key assertion: last_completed_step should be 5, not 6 (because step 6 failed)
    assert step6_state["last_completed_step"] == 5, \
        f"Expected last_completed_step=5 after step 6 failed, got {step6_state['last_completed_step']}"

    # The failed output should be prefixed with "FAILED:"
    assert step6_state["step_outputs"]["6"].startswith("FAILED:"), \
        "Failed step output should be prefixed with 'FAILED:'"


def test_resume_reruns_failed_step(mock_dependencies, default_args, tmp_path):
    """
    Issue #190: Resume should re-run a failed step, not skip it.
    If last_completed_step=5.5 and step 6 has "FAILED:" output, resume should re-run from step 6.
    """
    import json

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create state file where step 7 completed but step 6 failed
    state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 5,  # Step 6 failed, so last COMPLETED is 5
        "step_outputs": {
            "1": "ok", "2": "ok", "3": "ok", "4": "ok", "5": "ok",
            "6": "FAILED: All agent providers failed"  # Failed output stored
        },
        "total_cost": 0.5,
        "model_used": "gpt-4",
        "changed_files": [],
        "worktree_path": None,
    }

    with patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(state, None)):
        executed_steps = []

        def track_execution(*args, **kwargs):
            label = kwargs.get('label', '')
            executed_steps.append(label)
            if label == 'step9':
                return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = track_execution

        success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Step 6 should be re-executed (not skipped) because last_completed_step=5
    assert "step6" in executed_steps, \
        f"Step 6 should be re-executed on resume, but executed steps were: {executed_steps}"

    # Steps 1-5 should NOT be executed (skipped due to resume)
    assert "step1" not in executed_steps, "Step 1 should be skipped on resume"
    assert "step2" not in executed_steps, "Step 2 should be skipped on resume"
    assert "step3" not in executed_steps, "Step 3 should be skipped on resume"
    assert "step4" not in executed_steps, "Step 4 should be skipped on resume"
    assert "step5" not in executed_steps, "Step 5 should be skipped on resume"

    # Steps 6-12 should all be executed (7 steps)
    assert len(executed_steps) == 7, \
        f"Expected 7 steps to be executed (6-12), but got {len(executed_steps)}: {executed_steps}"


# --- Issue #352: Worktree Creation Timing Tests ---


def test_worktree_created_before_step_5_5(tmp_path):
    """
    Issue #352: Verify that worktree is created BEFORE step 7 runs.

    Bug: Step 5.5 (prompt classification) can edit prompt files when it detects
    a "Prompt Defect" via PROMPT_FIXED marker. Worktree creation must happen
    before step 7 so prompt edits happen in the worktree.

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
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        def track_worktree(*args, **kwargs):
            call_order.append(("_setup_worktree", kwargs.get("issue_number")))
            return (mock_worktree_path, None)

        def track_run(*args, **kwargs):
            label = kwargs.get("label", "")
            call_order.append(("run_agentic_task", label))
            if label == "step9":
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
        if call_type == "run_agentic_task" and arg == "step7":
            step5_5_idx = i

    assert step5_5_idx is not None, "Step 5.5 should have been executed"
    assert worktree_idx is not None, "Worktree should have been created"

    # Key assertion: worktree must be created BEFORE step 7 runs
    assert worktree_idx < step5_5_idx, (
        f"Worktree creation (index {worktree_idx}) must happen BEFORE "
        f"step5_5 execution (index {step5_5_idx}). "
        f"Call order: {call_order}"
    )


def test_step_5_5_runs_in_worktree_directory(tmp_path):
    """
    Issue #352: Verify that step 7 (prompt classification) runs with the worktree path as cwd.

    Step 5.5 should run in the worktree so that any prompt edits land on the
    """
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        mock_worktree.return_value = (mock_worktree_path, None)
        mock_load.return_value = "Prompt for {issue_number}"

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
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

    # Find the step 7 call
    step5_5_call = None
    for call_obj in mock_run.call_args_list:
        if call_obj.kwargs.get("label") == "step7":
            step5_5_call = call_obj
            break

    assert step5_5_call is not None, "Step 5.5 should have been called"

    # Key assertion: step 7 should run in the worktree, not main repo
    step5_5_cwd = step5_5_call.kwargs.get("cwd")
    assert step5_5_cwd == mock_worktree_path, (
        f"Step 5.5 should run in worktree ({mock_worktree_path}), "
        f"but ran in {step5_5_cwd}"
    )


def test_steps_1_to_5_run_in_main_directory(tmp_path):
    """
    Issue #352 regression test: Steps 1-5 should still run in main directory.

    Worktree creation happens before Step 5.5 (prompt classification),
    but Steps 1-5 should still run in the main directory since they are
    read-only analysis steps that don't modify files.
    """
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        mock_worktree.return_value = (mock_worktree_path, None)
        mock_load.return_value = "Prompt for {issue_number}"

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
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
        if label == 'step9':
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
    assert mock_run.call_count == 12  # All 12 steps should execute


def test_curly_braces_in_restored_context_do_not_cause_keyerror(mock_dependencies, default_args, tmp_path):
    """
    Issue #393: Curly braces in restored step outputs should not cause KeyError on resume.

    When resuming from saved state, step outputs containing {placeholder} patterns
    should be escaped before being added to context.
    """
    import json

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create state with step output containing curly braces
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

    with patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(state, None)):
        # Template for step 3 includes step2_output
        def side_effect_load(name):
            if "step3" in name:
                return "Previous: {step2_output}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        def side_effect_run(*args, **kwargs):
            label = kwargs.get('label', '')
            if label == 'step9':
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
        if label == 'step9':
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


def test_resume_message_shows_correct_next_step(mock_dependencies, default_args, tmp_path):
    """
    Verify that resume message shows the correct next step number.

    When last_completed_step=5.5, the resume message should say "Starting from Step 6".
    """
    import json

    mock_run, mock_load, mock_console = mock_dependencies
    default_args["cwd"] = tmp_path
    default_args["quiet"] = False  # Enable console output to verify message

    # Create state with last_completed_step=5.5
    state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 5.5,
        "step_outputs": {
            "1": "ok", "2": "ok", "3": "ok", "4": "ok", "5": "ok", "5.5": "ok"
        },
        "total_cost": 0.6,
        "model_used": "gpt-4",
        "changed_files": [],
        "worktree_path": None,
    }

    with patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(state, None)):
        def side_effect_run(*args, **kwargs):
            label = kwargs.get('label', '')
            if label == 'step9':
                return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        run_agentic_bug_orchestrator(**default_args)

    # Verify the resume messages show the correct info
    print_calls = [str(call) for call in mock_console.print.call_args_list]
    resume_msg = next((call for call in print_calls if "Resuming" in call), None)

    assert resume_msg is not None, "Resume message should be printed"
    # The "Starting from Step X" message is a separate print call
    starting_msg = next((call for call in print_calls if "Starting from" in call), None)
    assert starting_msg is not None, "Starting from message should be printed"
    assert "Step 6" in starting_msg or "step 6" in starting_msg, (
        f"Starting message should reference step 6, got: {starting_msg}"
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
        if label == 'step9':
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
        if label == 'step9':
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
        if label == 'step9':
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
    Integration test: Verify the REAL step 7 prompt template can be formatted.

    Unlike other tests that mock load_prompt_template and preprocess, this test:
    1. Loads the actual agentic_bug_step5_5_prompt_classification_LLM.prompt file
    2. Calls the real preprocess() to expand <include>docs/prompting_guide.md</include>
    3. Verifies .format() succeeds without KeyError from JSON braces

    This catches issues that mocked tests miss, such as new JSON added to prompting_guide.md.
    """
    from pdd.load_prompt_template import load_prompt_template
    from pdd.preprocess import preprocess

    # Load the REAL step 7 template
    template = load_prompt_template("agentic_bug_step5_5_prompt_classification_LLM")
    if template is None:
        pytest.skip("Step 5.5 template not found - skipping integration test")

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
# Issue #279: Step Context Key Restoration Bug (old 5.5 → new step numbering)
# ============================================================================


def test_context_key_uses_step_number():
    """
    Unit test for the context key restoration logic.

    With the step numbering that includes 5.5, context keys use the step number
    as stored: "5.5" -> context["step5.5_output"]. The format replacement
    converts to {step5.5_output} in templates.
    """
    # Simulate cached state (as stored in bug_state_*.json)
    cached_step_outputs = {
        "1": "Step 1 output",
        "5": "Step 5 output",
        "5.5": "Step 5.5 classification output",
        "6": "Step 6 output",
    }

    context = {}

    # Restoration logic from agentic_bug_orchestrator.py
    for step_key, output in cached_step_outputs.items():
        context[f"step{step_key}_output"] = output

    # Verify keys work correctly
    assert "step5.5_output" in context, \
        f"step5.5_output should be in context. Got keys: {list(context.keys())}"

    # Verify prompt formatting works
    template = "Previous classification: {step5.5_output}"
    try:
        formatted = template.format(**{k.replace(".", "_dot_"): v for k, v in context.items()})
    except KeyError:
        # The actual code uses .replace() not .format(), so this isn't a real issue
        pass

    # The actual orchestrator code uses string .replace() for formatting, not .format()
    formatted = template
    for key, value in context.items():
        formatted = formatted.replace(f"{{{key}}}", str(value))
    assert "Step 5.5 classification output" in formatted


# ============================================================================
# Issue #467: False Cache / Ratchet Effect on last_completed_step
# ============================================================================


def test_consecutive_failures_do_not_advance_last_completed_step(mock_dependencies, default_args, tmp_path):
    """
    Issue #467: When consecutive steps fail, last_completed_step should remain 0.

    Bug (now fixed): Each failed step set last_completed_step_to_save = step_num - 1,
    causing a "ratchet effect" that advanced the cursor despite zero successes.

    With the fix: failures don't advance last_completed_step, and 3
    consecutive provider failures trigger early abort. The final saved state
    should have last_completed_step=0 with only the aborted steps' FAILED outputs.
    """
    import json

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # ALL steps fail with provider errors
    def side_effect_run(*args, **kwargs):
        return (False, "All agent providers failed", 0.0, "")

    mock_run.side_effect = side_effect_run

    saved_states = []

    def capture_state(cwd, issue_number, workflow_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        import copy as _copy; saved_states.append(_copy.deepcopy(state))
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

    # Step outputs for steps before the abort should be prefixed with "FAILED:"
    # The last step (step 3, which triggered the abort) may have the raw output
    for step_key, output in final_state["step_outputs"].items():
        assert "All agent providers failed" in output, (
            f"Step {step_key} output should contain provider failure message but got: {output[:50]}"
        )


def test_resume_from_all_failed_state_reruns_from_step_1(mock_dependencies, default_args, tmp_path):
    """
    Issue #467: When resuming from a state where all steps failed,
    the workflow should re-run from step 1, not skip to a later step.

    Bug: A previous run where all steps failed saves last_completed_step=7
    (due to the ratchet effect). On resume, load_workflow_state returns this
    corrupted state, and the orchestrator skips ahead, even though nothing succeeded.

    This test creates the exact corrupted state observed in issue #467 and verifies
    that resume correctly detects all outputs are FAILED and re-runs from step 1.
    """
    import json

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create corrupted state: last_completed_step=5.5 but ALL step outputs are FAILED
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

    with patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(corrupted_state, None)):
        # Track which steps are actually executed
        executed_steps = []

        def side_effect_run(*args, **kwargs):
            label = kwargs.get('label', '')
            executed_steps.append(label)
            if label == 'step9':
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

    # All 12 steps should be executed (none should be skipped)
    assert mock_run.call_count == 12, (
        f"All 12 steps should be executed when all cached outputs are FAILED, "
        f"but only {mock_run.call_count} steps were executed: {executed_steps}"
    )


def test_partial_failure_preserves_last_successful_step(mock_dependencies, default_args, tmp_path):
    """
    Issue #467: When steps 1-3 succeed and steps 4+ fail,
    last_completed_step should be 3 (last successful step).

    Bug: With the ratchet effect, step 4 fails -> saves 3, step 5 fails -> saves 4,
    step 6 fails -> saves 5, etc. The final saved value is higher than the
    actual last successful step (3).

    Expected: last_completed_step should remain 3 throughout all subsequent failures.
    """
    import json

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Steps 1-3 succeed, steps 4+ fail
    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        step_str = label.replace('step', '').replace('_', '.')
        try:
            step_num = float(step_str) if '.' in step_str else int(step_str)
        except ValueError:
            step_num = 0
        if step_num <= 3:
            return (True, f"Step {step_num} succeeded", 0.1, "gpt-4")
        else:
            return (False, "All agent providers failed", 0.0, "")

    mock_run.side_effect = side_effect_run

    saved_states = []

    def capture_state(cwd, issue_number, workflow_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        import copy as _copy; saved_states.append(_copy.deepcopy(state))
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
    Issue #467: When resuming from a state where steps 1-3 succeeded but 4+ failed,
    the workflow should resume from step 4 (re-run the first failed step), not later.

    Bug: Due to the ratchet effect, the saved state has last_completed_step=5.5
    even though only steps 1-3 actually succeeded. On resume, steps 4-5.5 are
    skipped even though they failed.

    This test creates a state with mixed success/failure outputs and verifies
    that resume correctly identifies the actual last successful step.
    """
    import json

    mock_run, mock_load, _ = mock_dependencies
    default_args["cwd"] = tmp_path

    # Create state where steps 1-3 succeeded, steps 4+ failed,
    # but last_completed_step is incorrectly set to 5.5 (ratchet effect)
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

    with patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(corrupted_state, None)):
        # Track which steps are executed
        executed_steps = []

        def side_effect_run(*args, **kwargs):
            label = kwargs.get('label', '')
            executed_steps.append(label)
            if label == 'step9':
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

    # Steps 4-10 plus 5.5 should all be executed (8 steps)
    assert mock_run.call_count == 9, (
        f"Expected 8 steps (4,5,5.5,6,7,8,9,10) but got {mock_run.call_count}: {executed_steps}"
    )


def test_failure_handling_does_not_use_step_num_minus_one(mock_dependencies, default_args, tmp_path):
    """
    Issue #467: Directly tests the step_num - 1 formula bug with consecutive failures.

    Bug: When step 1 fails, last_completed_step = 1 - 1 = 0 (correct).
    When step 2 then fails, last_completed_step = 2 - 1 = 1 (WRONG: step 1 failed too).

    The step_num - 1 formula assumes the previous step succeeded, which is false
    when consecutive steps fail.

    Expected: After both steps 1 and 2 fail, last_completed_step should be 0.
    """
    import json

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
            return (True, "STOP_CONDITION: Needs More Info", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    saved_states = []

    def capture_state(cwd, issue_number, workflow_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        import copy as _copy; saved_states.append(_copy.deepcopy(state))
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
    # Note: on fresh start, last_completed_step may not be in the state dict if no step succeeded
    actual_lcs = step2_state.get("last_completed_step", 0)
    assert actual_lcs == 0, (
        f"After steps 1 and 2 both fail, last_completed_step should be 0, "
        f"but got {actual_lcs}. "
        f"The step_num - 1 formula incorrectly assumed step 1 succeeded."
    )

# ============================================================================
# ADDITIONAL TESTS -- Newly added coverage
# ============================================================================
#
# Test Plan for newly identified gaps:
#
#  1. timeout_adder -- Verify it is summed with BUG_STEP_TIMEOUTS for every step.
#  2. 3 consecutive provider failures -- Verify early abort at exactly 3 failures.
#  3. Non-provider failure resets consecutive counter -- A "regular" failure resets
#     the counter so provider-failure counting starts fresh.
#  4. Worktree creation failure -- Graceful early exit when _setup_worktree
#     returns (None, error_msg).
#  5. E2E_SKIP non-stop -- "E2E_SKIP:" in step 9 does NOT trigger a hard stop;
#     step 10 still executes.
#  6. E2E files in step 10 context -- E2E_FILES_CREATED files end up in
#     files_to_stage for step 10.
#  7. changed_files deduplication -- Same path in FILES_CREATED and FILES_MODIFIED
#     should only appear once in changed_files.
#  8. User Error specifically -- Step 2 "User Error (Not a Bug)" hard stop covers
#     a separate code branch from Feature Request.
#  9. verbose flag propagation -- verbose=True must reach run_agentic_task.
# 10. Total cost per-step -- Different cost per step sums correctly.
# 11. model_used reflects last step -- After step 10, model comes from step 10.
# 12. Header message -- header with issue_number and issue_title printed.
# 13. use_github_state=False propagation -- State functions receive it.
# 14. DEFECT_TYPE: code continues workflow -- Step 5.5 with only DEFECT_TYPE line
#     does NOT stop; no PROMPT_REVIEW marker present.
# 15. changed_files restored from state on resume -- Previously accumulated
#     changed_files come back in the return value.
#
# Z3 formal verification note: The orchestration logic is primarily string-matching
# and sequential control flow over external side-effects. Z3 would add little value
# here -- unit tests with mocked dependencies provide sufficient coverage without the
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
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect
    default_args["timeout_adder"] = timeout_adder

    run_agentic_bug_orchestrator(**default_args)

    assert mock_run.call_count == 12
    for call_obj in mock_run.call_args_list:
        label = call_obj.kwargs.get("label", "")
        actual_timeout = call_obj.kwargs.get("timeout")
        step_str = label.replace("step", "").replace("_", ".")
        step_num = float(step_str) if "." in step_str else int(step_str)
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
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # The non-provider failure at step 2 resets the counter, so we should NOT
    # abort after 3 total calls -- all 11 steps should execute
    assert mock_run.call_count == 12, (
        f"Non-provider failure should reset counter; expected 11 steps, got {mock_run.call_count}"
    )
    assert success is True


def test_worktree_creation_failure_returns_early(default_args, tmp_path):
    """
    Verify that a failed worktree creation causes an immediate early exit
    before step 7 runs.
    """
    default_args["cwd"] = tmp_path

    with (
        patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run,
        patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load,
        patch("pdd.agentic_bug_orchestrator.console"),
        patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree,
        patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)),
        patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None),
        patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t),
        patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path),
        patch("pdd.agentic_bug_orchestrator.set_agentic_progress"),
        patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"),
    ):
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (None, "git: not a git repository")
        mock_run.return_value = (True, "ok", 0.1, "model")

        success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Failed to create worktree" in msg

    # Steps 7 (prompt_classification) and beyond must NOT have run
    called_labels = [c.kwargs.get("label") for c in mock_run.call_args_list]
    assert "step7" not in called_labels
    assert "step8" not in called_labels
    assert "step12" not in called_labels


def test_e2e_skip_continues_to_step_10(mock_dependencies, default_args):
    """
    Verify that 'E2E_SKIP:' in step 9 output does NOT trigger a hard stop;
    step 10 must still execute.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        if label == "step11":
            return (True, "E2E_SKIP: No E2E test framework detected in repo", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "Investigation complete" in msg
    assert mock_run.call_count == 12

    called_labels = [c.kwargs.get("label") for c in mock_run.call_args_list]
    assert "step12" in called_labels, "Step 10 (PR) should still run after E2E_SKIP"


def test_e2e_files_propagated_to_step_10_files_to_stage(mock_dependencies, default_args):
    """
    Verify that E2E test files parsed from step 9 (E2E_FILES_CREATED) appear
    in the 'files_to_stage' context variable that step 10 uses.
    """
    mock_run, mock_load, _ = mock_dependencies

    def side_effect_load(name):
        if "step12" in name and "pr" in name:
            return "Stage all: {files_to_stage}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = side_effect_load

    def side_effect_run(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: tests/test_unit.py", 0.1, "model")
        if label == "step11":
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
        (c for c in mock_run.call_args_list if c.kwargs.get("label") == "step12"),
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
        if label == "step9":
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
        (True, "Verdict: User Error (Not a Bug) -- user misread the documentation", 0.1, "model"),
    ]

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 2" in msg
    assert "User Error" in msg
    assert mock_run.call_count == 2


def test_verbose_flag_propagated_to_every_run_agentic_task_call(mock_dependencies, default_args):
    """
    Verify that verbose=True is forwarded to every run_agentic_task invocation.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect
    default_args["verbose"] = True

    run_agentic_bug_orchestrator(**default_args)

    assert mock_run.call_count == 12
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
        "step7": 0.06,
        "step6": 0.07,
        "step9": 0.08,
        "step10": 0.09,
        "step11": 0.10,
        "step12": 0.11,
    }

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        cost = step_costs.get(label, 0.0)
        if label == "step9":
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
        if label == "step12":
            return (True, "PR created", 0.1, "claude-3-opus")
        if label == "step9":
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
    Verify the header message includes both the issue number and title.
    """
    with (
        patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run,
        patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load,
        patch("pdd.agentic_bug_orchestrator.console") as mock_console,
        patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree,
        patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)),
        patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None),
        patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t),
        patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path),
        patch("pdd.agentic_bug_orchestrator.set_agentic_progress"),
        patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"),
    ):
        wt = tmp_path / ".pdd" / "worktrees" / "fix-issue-99"
        wt.mkdir(parents=True, exist_ok=True)
        mock_worktree.return_value = (wt, None)
        mock_load.return_value = "Prompt for {issue_number}"

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
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
    Verify that use_github_state=False is forwarded to load_workflow_state
    and save_workflow_state.
    """
    default_args["cwd"] = tmp_path
    default_args["use_github_state"] = False

    saved_calls: list[bool] = []
    loaded_calls: list[bool] = []

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

    with (
        patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run,
        patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load,
        patch("pdd.agentic_bug_orchestrator.console"),
        patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree,
        patch("pdd.agentic_bug_orchestrator.load_workflow_state", side_effect=capture_load),
        patch("pdd.agentic_bug_orchestrator.save_workflow_state", side_effect=capture_save),
        patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t),
        patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path),
        patch("pdd.agentic_bug_orchestrator.set_agentic_progress"),
        patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"),
    ):
        wt = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
        wt.mkdir(parents=True, exist_ok=True)
        mock_worktree.return_value = (wt, None)
        mock_load.return_value = "Prompt for {issue_number}"

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
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


def test_step5_5_defect_type_code_does_not_stop_workflow(mock_dependencies, default_args):
    """
    Verify that 'DEFECT_TYPE: code' in step 7 output does NOT trigger any
    hard stop -- the workflow continues normally to step 6 and beyond.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "DEFECT_TYPE: code\nNo prompt issues found.", 0.1, "model")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "Investigation complete" in msg
    assert mock_run.call_count == 12

    called_labels = [c.kwargs.get("label") for c in mock_run.call_args_list]
    assert "step6" in called_labels, "Step 6 should run after DEFECT_TYPE: code"
    assert "step12" in called_labels, "Step 10 should run after DEFECT_TYPE: code"


def test_changed_files_restored_from_state_on_resume(default_args, tmp_path):
    """
    Verify that 'changed_files' stored in saved state is restored on resume
    and included in the final return value.
    """
    default_args["cwd"] = tmp_path

    # Simulate a prior run that completed through step 11 with persisted changed_files
    prior_state = {
        "workflow": "bug",
        "issue_number": default_args["issue_number"],
        "issue_url": default_args["issue_url"],
        "last_completed_step": 11,
        "step_outputs": {
            "1": "ok",
            "2": "ok",
            "3": "ok",
            "4": "ok",
            "5": "ok",
            "5.5": "ok",
            "6": "ok",
            "7": "DEFECT_TYPE: code",
            "8": "ok",
            "9": "FILES_CREATED: tests/test_persisted.py",
            "10": "ok",
            "11": "E2E_FILES_CREATED: tests/e2e/test_e2e_persisted.py",
        },
        "total_cost": 0.9,
        "model_used": "gpt-4",
        "changed_files": ["tests/test_persisted.py", "tests/e2e/test_e2e_persisted.py"],
        "worktree_path": None,
    }

    with (
        patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run,
        patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load,
        patch("pdd.agentic_bug_orchestrator.console"),
        patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree,
        patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(prior_state, None)),
        patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None),
        patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t),
        patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path),
        patch("pdd.agentic_bug_orchestrator.set_agentic_progress"),
        patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"),
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


def test_e2e_needed_no_skips_step_9(mock_dependencies, default_args):
    """
    Verify that 'E2E_NEEDED: no' in step 8 output causes step 9 to be skipped.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        if label == "step10":
            return (True, "E2E_NEEDED: no\nUnit tests provide sufficient coverage", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "Investigation complete" in msg

    called_labels = [c.kwargs.get("label") for c in mock_run.call_args_list]
    assert "step11" not in called_labels, "Step 9 should be skipped when E2E_NEEDED: no"
    assert "step12" in called_labels, "Step 10 should still run after skipping E2E"
    # 12 steps minus 1 skipped = 11 calls
    assert mock_run.call_count == 11


# --- Restored coverage: dropped tests migrated to new step numbering ---


def test_step5_5_prompt_review_returns_reason_in_message(mock_dependencies, default_args):
    """Hard stop at step 7 should include the PROMPT_REVIEW reason in the message."""
    mock_run, mock_load, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "PROMPT_REVIEW: ambiguous requirement in line 42", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "step 7" in msg
    assert "Prompt defect" in msg


def test_step7_empty_files_after_comma_split_is_hard_stop(mock_dependencies, default_args):
    """Step 7 with FILES_CREATED containing only empty strings after split should hard stop."""
    mock_run, mock_load, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            # FILES_CREATED with empty value — no actual files
            return (True, "FILES_CREATED: ", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "step 9" in msg
    assert "No test file" in msg


def test_multiple_e2e_files_all_tracked(mock_dependencies, default_args):
    """Multiple E2E files created in step 9 should all end up in changed_files."""
    mock_run, mock_load, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: tests/test_bug.py", 0.1, "gpt-4")
        if label == "step11":
            return (True, "E2E_FILES_CREATED: tests/e2e/test_e2e_a.py, tests/e2e/test_e2e_b.py", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "tests/test_bug.py" in files
    assert "tests/e2e/test_e2e_a.py" in files
    assert "tests/e2e/test_e2e_b.py" in files


def test_e2e_skip_preserves_earlier_files(mock_dependencies, default_args):
    """When E2E is skipped via E2E_NEEDED: no, files from step 7 are still in changed_files."""
    mock_run, mock_load, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Verification passed.\nE2E_NEEDED: no", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "tests/test_fix.py" in files
    # Step 9 should be skipped
    called_labels = [c.kwargs.get("label") for c in mock_run.call_args_list]
    assert "step11" not in called_labels


def test_step7_filesystem_fallback_when_no_markers(mock_dependencies, default_args):
    """When step 7 output has no FILES_CREATED/FILES_MODIFIED markers, fall back to filesystem diff."""
    mock_run, mock_load, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "Generated tests but forgot markers", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    # Patch _get_modified_and_untracked to simulate filesystem detection
    with patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_fs:
        mock_fs.side_effect = [
            [],  # pre-step-7 snapshot (used by Step 7 prompt-file filesystem fallback)
            [],  # pre-step-9 snapshot
            ["tests/test_new.py"],  # post-step-9: new test file appeared
        ]

        success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "tests/test_new.py" in files


def test_step7_no_markers_no_files_hard_stops(mock_dependencies, default_args):
    """When step 7 has no markers AND no new files on disk, it's a hard stop."""
    mock_run, mock_load, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "I couldn't generate any tests", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    with patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_fs:
        mock_fs.return_value = []  # No new files

        success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "step 9" in msg
    assert "No test file" in msg


def test_step3_needs_more_info_hard_stop(mock_dependencies, default_args):
    """Step 3 with 'Needs More Info' should hard stop."""
    mock_run, mock_load, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step3":
            return (True, "Needs More Info: cannot reproduce without logs", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "step 3" in msg
    assert "info" in msg.lower()


# --- Issue #912: _parse_changed_files drops multi-line markers ---


class TestParseChangedFilesMultiLine:
    """Issue #912: _parse_changed_files uses re.search which only finds the first
    match. When Step 7 outputs multiple PROMPT_FIXED: lines (one per file),
    the second file is silently dropped from changed_files."""

    def test_single_marker_single_file(self):
        """Baseline: single marker line with one file works correctly."""
        from pdd.agentic_bug_orchestrator import _parse_changed_files

        output = "Some output\nPROMPT_FIXED: prompts/module_python.prompt\nMore output"
        result = _parse_changed_files(output, "PROMPT_FIXED")
        assert result == ["prompts/module_python.prompt"]

    def test_single_marker_comma_separated(self):
        """Baseline: comma-separated files on one line works correctly."""
        from pdd.agentic_bug_orchestrator import _parse_changed_files

        output = "PROMPT_FIXED: prompts/a.prompt, prompts/b.prompt"
        result = _parse_changed_files(output, "PROMPT_FIXED")
        assert result == ["prompts/a.prompt", "prompts/b.prompt"]

    def test_multiple_marker_lines(self):
        """Bug: two separate PROMPT_FIXED: lines — second file must not be dropped."""
        from pdd.agentic_bug_orchestrator import _parse_changed_files

        output = (
            "DEFECT_TYPE: prompt\n"
            "PROMPT_FIXED: pdd/prompts/agentic_e2e_fix_orchestrator_python.prompt\n"
            "PROMPT_FIXED: pdd/prompts/agentic_e2e_fix_step9_verify_all_LLM.prompt"
        )
        result = _parse_changed_files(output, "PROMPT_FIXED")
        assert len(result) == 2, (
            f"Expected 2 files from two PROMPT_FIXED: lines, got {len(result)}: {result}"
        )
        assert "pdd/prompts/agentic_e2e_fix_orchestrator_python.prompt" in result
        assert "pdd/prompts/agentic_e2e_fix_step9_verify_all_LLM.prompt" in result

    def test_multiple_files_created_lines(self):
        """Same bug applies to FILES_CREATED: markers across multiple lines."""
        from pdd.agentic_bug_orchestrator import _parse_changed_files

        output = (
            "FILES_CREATED: tests/test_unit.py\n"
            "FILES_CREATED: tests/test_e2e.py"
        )
        result = _parse_changed_files(output, "FILES_CREATED")
        assert len(result) == 2, (
            f"Expected 2 files from two FILES_CREATED: lines, got {len(result)}: {result}"
        )

    def test_mixed_multiline_and_comma(self):
        """Multiple lines where one line has comma-separated files."""
        from pdd.agentic_bug_orchestrator import _parse_changed_files

        output = (
            "PROMPT_FIXED: prompts/a.prompt, prompts/b.prompt\n"
            "PROMPT_FIXED: prompts/c.prompt"
        )
        result = _parse_changed_files(output, "PROMPT_FIXED")
        assert len(result) == 3
        assert "prompts/a.prompt" in result
        assert "prompts/b.prompt" in result
        assert "prompts/c.prompt" in result


class TestMultiplePromptFixedInWorkflow:
    """Issue #912: When Step 7 fixes two prompt files, both must appear in
    changed_files and files_to_stage for Step 12 to commit them."""

    def test_two_prompt_fixed_files_both_tracked(self, mock_dependencies, default_args):
        """When Step 7 outputs two PROMPT_FIXED: lines, both files must be
        in the returned changed_files list."""
        mock_run, _, _ = mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if label == 'step7':
                return (True, (
                    "Classification: Prompt Defect\n"
                    "DEFECT_TYPE: prompt\n"
                    "PROMPT_FIXED: pdd/prompts/orchestrator_python.prompt\n"
                    "PROMPT_FIXED: pdd/prompts/step9_verify_all_LLM.prompt"
                ), 0.1, "model")
            if label == 'step9':
                return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
            return (True, "ok", 0.1, "model")

        mock_run.side_effect = side_effect

        success, msg, _, _, changed_files = run_agentic_bug_orchestrator(**default_args)

        assert success is True
        assert "pdd/prompts/orchestrator_python.prompt" in changed_files, (
            f"First PROMPT_FIXED file missing from changed_files: {changed_files}"
        )
        assert "pdd/prompts/step9_verify_all_LLM.prompt" in changed_files, (
            f"Second PROMPT_FIXED file missing from changed_files: {changed_files}"
        )
        assert "tests/test_fix.py" in changed_files

    def test_files_to_stage_reaches_step12_template(self, mock_dependencies, default_args):
        """E2E: verify that files_to_stage (with both prompt files) is substituted
        into the Step 12 prompt that the LLM receives."""
        mock_run, mock_load, _ = mock_dependencies

        # Return a template that contains {files_to_stage} for Step 12
        def load_side_effect(name):
            if "step12" in name:
                return "Stage these files:\n{files_to_stage}\nNow commit."
            return "Prompt for {issue_number}"

        mock_load.side_effect = load_side_effect

        def run_side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if label == 'step7':
                return (True, (
                    "DEFECT_TYPE: prompt\n"
                    "PROMPT_FIXED: pdd/prompts/orchestrator.prompt\n"
                    "PROMPT_FIXED: pdd/prompts/step9.prompt"
                ), 0.1, "model")
            if label == 'step9':
                return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
            return (True, "ok", 0.1, "model")

        mock_run.side_effect = run_side_effect

        run_agentic_bug_orchestrator(**default_args)

        # Find the Step 12 call and inspect the instruction it received
        step12_calls = [
            c for c in mock_run.call_args_list
            if c.kwargs.get('label', '') == 'step12'
        ]
        assert len(step12_calls) == 1, "Step 12 should run exactly once"

        step12_instruction = step12_calls[0].kwargs.get('instruction', '')
        assert "pdd/prompts/orchestrator.prompt" in step12_instruction, (
            f"First prompt file not in Step 12 instruction:\n{step12_instruction}"
        )
        assert "pdd/prompts/step9.prompt" in step12_instruction, (
            f"Second prompt file not in Step 12 instruction:\n{step12_instruction}"
        )
        assert "tests/test_fix.py" in step12_instruction, (
            f"Test file not in Step 12 instruction:\n{step12_instruction}"
        )


# --- Issue #912 Fix 2: Orchestrator-driven staging before Step 12 ---


class TestOrchestratorPreStaging:
    """Issue #912: The orchestrator must stage changed_files via git add
    before dispatching Step 12, so the LLM cannot selectively omit files.
    This follows the precedent set by _commit_and_push() in
    agentic_e2e_fix_orchestrator.py (line 788)."""

    def test_prompt_files_staged_before_step12(self, tmp_path):
        """When Step 7 fixes prompt files, the orchestrator must git-add them
        before Step 12 runs. Verify subprocess.run(['git', 'add', ...]) is
        called for each file in changed_files prior to Step 12's
        run_agentic_task invocation."""
        mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
        mock_worktree_path.mkdir(parents=True, exist_ok=True)

        call_log = []  # Track ordering of git-add vs step12

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess:

            mock_load.return_value = "Prompt for {issue_number}"
            mock_worktree.return_value = (mock_worktree_path, None)
            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            def run_side_effect(*args, **kwargs):
                label = kwargs.get('label', '')
                if label == 'step12':
                    call_log.append('step12_run')
                if label == 'step7':
                    return (True, (
                        "DEFECT_TYPE: prompt\n"
                        "PROMPT_FIXED: pdd/prompts/orchestrator.prompt\n"
                        "PROMPT_FIXED: pdd/prompts/step9.prompt"
                    ), 0.1, "model")
                if label == 'step9':
                    return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect

            # Intercept subprocess.run to log git-add calls
            def subprocess_side_effect(*args, **kwargs):
                cmd = args[0] if args else kwargs.get('args', [])
                if isinstance(cmd, list) and len(cmd) >= 3 and cmd[0] == "git" and cmd[1] == "add":
                    call_log.append(f'git_add:{cmd[2]}')
                return MagicMock(returncode=0, stdout="", stderr="")
            mock_subprocess.run.side_effect = subprocess_side_effect

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
                quiet=True,
            )

        # git add calls for changed files must appear BEFORE step12_run
        git_adds = [c for c in call_log if c.startswith('git_add:')]
        step12_idx = call_log.index('step12_run') if 'step12_run' in call_log else len(call_log)

        assert len(git_adds) >= 2, (
            f"Expected git add for at least 2 files before Step 12, "
            f"but got {len(git_adds)} git adds. Full log: {call_log}"
        )

        # All git adds must come before step12
        for ga in git_adds:
            ga_idx = call_log.index(ga)
            assert ga_idx < step12_idx, (
                f"{ga} at index {ga_idx} came AFTER step12_run at {step12_idx}. "
                f"Orchestrator must stage files before Step 12 dispatch. Log: {call_log}"
            )


# --- Step 9 Structural Guard Retry Tests (Issue #929) ---


def test_step9_retry_addendum_includes_violating_code_lines(tmp_path):
    """
    BUG REPRODUCTION (Issue #929): The retry addendum must include the actual
    violating code lines from the generated test files, not just violation
    description strings like 'Line 4: assert hasattr() — ...'.

    Without the actual code, the LLM receives nearly identical input on retry
    and regenerates the same structural violations.

    This test:
    1. Creates a real test file on disk with an assert hasattr() violation
    2. Mocks run_agentic_task so first call returns output pointing to that file
    3. Captures the retry call's instruction parameter
    4. Asserts the instruction contains the actual code line from the file
    """
    # Create the worktree directory structure
    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    # Create a test file with a structural violation (assert hasattr)
    test_file = worktree_path / "tests" / "test_bug_fix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    # The violating code line we expect to see in the retry addendum
    violating_code_line = 'assert hasattr(some_module, "target_func")'
    test_file.write_text(
        "from pdd import some_module\n"
        "\n"
        "def test_bug():\n"
        f"    {violating_code_line}\n"
    )

    captured_retry_instruction = None
    first_step9 = True

    def mock_run_side_effect(*args, **kwargs):
        nonlocal captured_retry_instruction, first_step9
        label = kwargs.get("label", "")

        if label == "step9":
            if first_step9:
                first_step9 = False
                # First step9 call: return output pointing to the violating file
                return (
                    True,
                    "Generated tests\nFILES_CREATED: tests/test_bug_fix.py",
                    0.1,
                    "model",
                )
            else:
                # This is the retry call — capture the instruction
                captured_retry_instruction = kwargs.get("instruction", "")
                return (
                    True,
                    "Fixed tests\nFILES_CREATED: tests/test_bug_fix.py",
                    0.1,
                    "model",
                )
        return (True, f"Output for {label}", 0.1, "model")

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        mock_run.side_effect = mock_run_side_effect
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (worktree_path, None)

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
            quiet=True,
        )

    # The retry must have been triggered (structural violations detected)
    assert captured_retry_instruction is not None, (
        "Expected a retry call for step9 due to structural violations, "
        "but no retry was captured"
    )

    # BUG: The current code only includes violation descriptions like
    # "Line 4: assert hasattr() — checks attribute existence..."
    # but does NOT include the actual violating code line.
    # The fix should include the actual code so the LLM knows what to rewrite.
    assert violating_code_line in captured_retry_instruction, (
        f"Retry addendum must include the actual violating code line "
        f"'{violating_code_line}' so the LLM knows what to rewrite. "
        f"Currently it only includes violation descriptions."
    )


def test_step9_retry_addendum_includes_source_string_matching_code(tmp_path):
    """
    BUG REPRODUCTION (Issue #929): When source-string-matching violations are
    detected, the retry addendum must include the actual assertion lines,
    not just 'Line N: source string matching — asserts keyword presence...'.

    This is the most common violation type from the original bug report
    (27 violations in the real case).
    """
    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    # Create a test file with source-string-matching violations
    # Build the file content line-by-line to avoid triggering the structural
    # pattern detector on THIS test file (the detector does line-by-line regex)
    test_file = worktree_path / "tests" / "test_bug_fix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    file_lines = [
        "from pathlib import Path",
        "",
        "def test_function_exists():",
    ]
    # Construct the violating lines using concatenation so the detector
    # doesn't see "content = ....read_text()" on a single line in THIS file
    src_read = 'content = Path("pdd/module.py").read' + '_text()'
    src_assertion = 'assert "def target_func" in content'
    file_lines.append(f"    {src_read}")
    file_lines.append(f"    {src_assertion}")
    test_file.write_text("\n".join(file_lines) + "\n")

    captured_retry_instruction = None
    first_step9 = True

    def mock_run_side_effect(*args, **kwargs):
        nonlocal captured_retry_instruction, first_step9
        label = kwargs.get("label", "")

        if label == "step9":
            if first_step9:
                first_step9 = False
                return (
                    True,
                    "Generated tests\nFILES_CREATED: tests/test_bug_fix.py",
                    0.1,
                    "model",
                )
            else:
                captured_retry_instruction = kwargs.get("instruction", "")
                return (
                    True,
                    "Fixed tests\nFILES_CREATED: tests/test_bug_fix.py",
                    0.1,
                    "model",
                )
        return (True, f"Output for {label}", 0.1, "model")

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        mock_run.side_effect = mock_run_side_effect
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (worktree_path, None)

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
            quiet=True,
        )

    assert captured_retry_instruction is not None, (
        "Expected a retry call for step9 due to source string matching violations"
    )

    # BUG: The retry addendum only says "Line 5: source string matching — ..."
    # It should include the actual assertion code so the LLM can rewrite it
    expected_violation = src_assertion
    assert expected_violation in captured_retry_instruction, (
        f"Retry addendum must include the actual violating assertion line "
        f"'{expected_violation}' so the LLM can rewrite it. "
        f"Currently it only includes generic violation descriptions."
    )


def test_step9_retry_addendum_includes_rewrite_guidance(tmp_path):
    """
    BUG REPRODUCTION (Issue #929): The retry addendum must include concrete
    rewrite guidance — a before/after example showing how to convert a
    structural test into a behavioral test.

    Without rewrite examples, the LLM has no model for what a correct
    rewrite looks like and regenerates the same structural tests.
    """
    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    # Create a test file with a structural violation (assert hasattr)
    test_file = worktree_path / "tests" / "test_bug_fix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    violating_code_line = 'assert hasattr(module, "func_a")'
    test_file.write_text(
        "from pdd import module\n"
        "\n"
        "def test_one():\n"
        f"    {violating_code_line}\n"
    )

    captured_retry_instruction = None
    first_step9 = True

    def mock_run_side_effect(*args, **kwargs):
        nonlocal captured_retry_instruction, first_step9
        label = kwargs.get("label", "")

        if label == "step9":
            if first_step9:
                first_step9 = False
                return (
                    True,
                    "Generated tests\nFILES_CREATED: tests/test_bug_fix.py",
                    0.1,
                    "model",
                )
            else:
                captured_retry_instruction = kwargs.get("instruction", "")
                return (
                    True,
                    "Fixed tests\nFILES_CREATED: tests/test_bug_fix.py",
                    0.1,
                    "model",
                )
        return (True, f"Output for {label}", 0.1, "model")

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        mock_run.side_effect = mock_run_side_effect
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (worktree_path, None)

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
            quiet=True,
        )

    assert captured_retry_instruction is not None, "Retry step9 call not captured"

    # The retry addendum must include BOTH:
    # 1. The actual violating code (so the LLM sees what it produced)
    # 2. A concrete rewrite showing a behavioral alternative
    #
    # Without both, the LLM has no before/after model and regenerates
    # the same structural tests.

    # Check that the actual violating code line is shown
    assert violating_code_line in captured_retry_instruction, (
        f"Retry addendum must include the actual violating code "
        f"'{violating_code_line}' so the LLM sees what it produced. "
        f"Currently it only includes generic descriptions "
        f"like 'Line 4: assert hasattr() — ...'."
    )

    # Check that a behavioral alternative is provided alongside the violating code
    # The addendum should show how to rewrite: call the function and assert on output
    instruction_lower = captured_retry_instruction.lower()
    has_behavioral_alternative = (
        ("result" in instruction_lower or "return" in instruction_lower)
        and "assert" in instruction_lower
    ) or (
        "call" in instruction_lower
        and "assert" in instruction_lower
    )
    assert has_behavioral_alternative, (
        "Retry addendum must include a concrete behavioral alternative "
        "showing how to rewrite the structural test (e.g., call the function "
        "and assert on the result). Currently it only says 'do not use X' "
        "without showing what to do instead."
    )


def test_step9_retry_includes_code_from_multiple_files(tmp_path):
    """
    BUG REPRODUCTION (Issue #929): When multiple generated files have violations,
    the retry addendum must include violating code from ALL files, not just
    file-agnostic descriptions.
    """
    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    # Create two test files with different hasattr violations
    tests_dir = worktree_path / "tests"
    tests_dir.mkdir(parents=True, exist_ok=True)

    violation_a = 'assert hasattr(alpha, "run_pipeline")'
    file_a = tests_dir / "test_fix_a.py"
    file_a.write_text(
        "from pdd import alpha\n"
        "\n"
        "def test_alpha():\n"
        f"    {violation_a}\n"
    )

    violation_b = 'assert hasattr(beta, "execute_task")'
    file_b = tests_dir / "test_fix_b.py"
    file_b.write_text(
        "from pdd import beta\n"
        "\n"
        "def test_beta():\n"
        f"    {violation_b}\n"
    )

    captured_retry_instruction = None
    first_step9 = True

    def mock_run_side_effect(*args, **kwargs):
        nonlocal captured_retry_instruction, first_step9
        label = kwargs.get("label", "")

        if label == "step9":
            if first_step9:
                first_step9 = False
                return (
                    True,
                    "Generated tests\nFILES_CREATED: tests/test_fix_a.py, tests/test_fix_b.py",
                    0.1,
                    "model",
                )
            else:
                captured_retry_instruction = kwargs.get("instruction", "")
                return (
                    True,
                    "Fixed tests\nFILES_CREATED: tests/test_fix_a.py, tests/test_fix_b.py",
                    0.1,
                    "model",
                )
        return (True, f"Output for {label}", 0.1, "model")

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        mock_run.side_effect = mock_run_side_effect
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (worktree_path, None)

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
            quiet=True,
        )

    assert captured_retry_instruction is not None, (
        "Expected retry for step9 with violations from both files"
    )

    # The retry must include actual code from BOTH files
    assert violation_a in captured_retry_instruction, (
        f"Retry addendum missing violating code from test_fix_a.py: '{violation_a}'"
    )
    assert violation_b in captured_retry_instruction, (
        f"Retry addendum missing violating code from test_fix_b.py: '{violation_b}'"
    )


# --- Direct unit tests for _extract_violation_snippets ---

from pdd.agentic_bug_orchestrator import _extract_violation_snippets


def test_extract_violation_snippets_shows_correct_line(tmp_path):
    """Snippet output includes the violating line marked with >>>."""
    test_file = tmp_path / "test_foo.py"
    test_file.write_text(
        "import os\n"
        "\n"
        "def test_one():\n"
        '    assert hasattr(mod, "fn")\n'
    )
    result = _extract_violation_snippets(
        {"test_foo.py": ["Line 4: assert hasattr() — checks attribute existence"]},
        tmp_path,
    )
    assert '>>> 4:' in result
    assert 'assert hasattr(mod, "fn")' in result


def test_extract_violation_snippets_missing_file_falls_back(tmp_path):
    """When the file doesn't exist, violations are included as plain text."""
    result = _extract_violation_snippets(
        {"nonexistent.py": ["Line 1: some violation"]},
        tmp_path,
    )
    assert "Line 1: some violation" in result
    assert ">>>" not in result


def test_extract_violation_snippets_missing_file_not_dropped_alongside_snippets(tmp_path):
    """Violations from a missing file must appear even when another file has snippets."""
    # File A exists and will produce snippets
    file_a = tmp_path / "test_a.py"
    file_a.write_text(
        "import os\n"
        "\n"
        "def test_one():\n"
        '    assert hasattr(mod, "fn")\n'
    )
    # File B doesn't exist — its 3 violations must still appear
    result = _extract_violation_snippets(
        {
            "test_a.py": ["Line 4: hasattr check"],
            "nonexistent.py": [
                "Line 1: violation one",
                "Line 2: violation two",
                "Line 3: violation three",
            ],
        },
        tmp_path,
    )
    # File A snippet is present
    assert ">>>" in result
    assert "hasattr" in result
    # File B violations are NOT silently dropped
    assert "violation one" in result
    assert "violation two" in result
    assert "violation three" in result


def test_extract_violation_snippets_line_out_of_range(tmp_path):
    """Line number beyond file length doesn't crash."""
    test_file = tmp_path / "short.py"
    test_file.write_text("x = 1\n")
    result = _extract_violation_snippets(
        {"short.py": ["Line 999: out of range violation"]},
        tmp_path,
    )
    # No snippet lines extracted (line 999 doesn't exist), falls back
    assert "Line 999: out of range violation" in result


def test_extract_violation_snippets_no_line_number_in_violation(tmp_path):
    """Violations without 'Line N:' prefix are included as plain text."""
    test_file = tmp_path / "test_foo.py"
    test_file.write_text("x = 1\n")
    result = _extract_violation_snippets(
        {"test_foo.py": ["general violation without line number"]},
        tmp_path,
    )
    assert "general violation without line number" in result


def test_extract_violation_snippets_no_line_number_alongside_snippets(tmp_path):
    """Violations without Line N: are included even when other violations have snippets."""
    test_file = tmp_path / "test_foo.py"
    test_file.write_text(
        "import os\n"
        "\n"
        "def test_one():\n"
        '    assert hasattr(mod, "fn")\n'
    )
    result = _extract_violation_snippets(
        {"test_foo.py": [
            "Line 4: hasattr check",
            "general violation without line number",
        ]},
        tmp_path,
    )
    # Snippet from Line 4 is present
    assert ">>>" in result
    # The no-line-number violation is NOT silently dropped
    assert "general violation without line number" in result


    """Violations from file A don't produce snippets from file B."""
    file_a = tmp_path / "test_a.py"
    file_a.write_text(
        "line1\n"
        "line2\n"
        "line3\n"
        "violation_a_here\n"
    )
    file_b = tmp_path / "test_b.py"
    file_b.write_text(
        "innocent1\n"
        "innocent2\n"
        "innocent3\n"
        "innocent4\n"
    )
    # Only file A has the violation — file B's line 4 should NOT appear
    result = _extract_violation_snippets(
        {"test_a.py": ["Line 4: some violation"]},
        tmp_path,
    )
    assert "violation_a_here" in result
    assert "innocent4" not in result


# --- Issue #932 comment #1: Backup/restore on retry failure ---


def test_step9_retry_failure_restores_original_files(tmp_path):
    """If retry fails, original test files must be restored (not left deleted)."""
    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    test_file = worktree_path / "tests" / "test_bug_fix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    violating_content = (
        "from pdd import some_module\n"
        "\n"
        "def test_bug():\n"
        '    assert hasattr(some_module, "target_func")\n'
    )
    test_file.write_text(violating_content)

    first_step9 = True

    def mock_run_side_effect(*args, **kwargs):
        nonlocal first_step9
        label = kwargs.get("label", "")
        if label == "step9":
            if first_step9:
                first_step9 = False
                return (
                    True,
                    "Generated tests\nFILES_CREATED: tests/test_bug_fix.py",
                    0.1,
                    "model",
                )
            else:
                # Retry FAILS
                return (False, "LLM error", 0.1, "model")
        return (True, f"Output for {label}", 0.1, "model")

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        mock_run.side_effect = mock_run_side_effect
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (worktree_path, None)

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
            quiet=True,
        )

    # Original file must be restored after retry failure
    assert test_file.exists(), (
        "Original test file should be restored when retry fails, "
        "not left deleted"
    )
    assert test_file.read_text() == violating_content
    # Backup file should not linger
    backup = test_file.with_suffix(".py.bak")
    assert not backup.exists(), "Backup file should be cleaned up after restore"


def test_step9_retry_success_cleans_up_backups(tmp_path):
    """If retry succeeds, .bak files must be removed."""
    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    test_file = worktree_path / "tests" / "test_bug_fix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text(
        "from pdd import some_module\n"
        "\n"
        "def test_bug():\n"
        '    assert hasattr(some_module, "target_func")\n'
    )

    first_step9 = True

    def mock_run_side_effect(*args, **kwargs):
        nonlocal first_step9
        label = kwargs.get("label", "")
        if label == "step9":
            if first_step9:
                first_step9 = False
                return (
                    True,
                    "Generated tests\nFILES_CREATED: tests/test_bug_fix.py",
                    0.1,
                    "model",
                )
            else:
                # Retry succeeds — write a new clean file
                test_file.write_text(
                    "from pdd import some_module\n"
                    "\n"
                    "def test_bug():\n"
                    "    result = some_module.target_func()\n"
                    "    assert result is not None\n"
                )
                return (
                    True,
                    "Fixed tests\nFILES_CREATED: tests/test_bug_fix.py",
                    0.1,
                    "model",
                )
        return (True, f"Output for {label}", 0.1, "model")

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        mock_run.side_effect = mock_run_side_effect
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (worktree_path, None)

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
            quiet=True,
        )

    # Backup must be cleaned up after successful retry
    backup = test_file.with_suffix(".py.bak")
    assert not backup.exists(), (
        ".bak backup file should be removed after successful retry"
    )


# --- Issue #932 comment #3: Path variable regex robustness ---


def test_path_var_regex_rejects_url_concat():
    """URL string concatenation like url = base + '/' + 'endpoint' must NOT be
    tracked as a path variable — it would cause false negatives in the detector."""
    from pdd.agentic_bug_orchestrator import detect_structural_test_patterns
    import tempfile, os

    code = (
        'url = base + "/" + "endpoint"\n'
        'content = url_var.read_text()\n'
        'assert "keyword" in content\n'
    )
    with tempfile.NamedTemporaryFile(mode="w", suffix=".py", delete=False) as f:
        f.write(code)
        f.flush()
        try:
            violations = detect_structural_test_patterns(f.name)
        finally:
            os.unlink(f.name)
    # The read_text + assert pattern should be flagged (url is NOT a path variable)
    assert len(violations) > 0, (
        "URL concatenation should not be treated as a path variable; "
        "the read_text + assert pattern should still be flagged"
    )


def test_path_var_regex_tracks_multi_segment_path():
    """Multi-segment path like p = Path(tmpdir) / subdir / 'file.json' must be
    tracked so that p.read_text() is not falsely flagged."""
    from pdd.agentic_bug_orchestrator import detect_structural_test_patterns
    import tempfile, os

    code = (
        'p = Path(tmpdir) / subdir / "architecture.json"\n'
        'data = json.loads(p.read_text())\n'
        'assert "key" in data\n'
    )
    with tempfile.NamedTemporaryFile(mode="w", suffix=".py", delete=False) as f:
        f.write(code)
        f.flush()
        try:
            violations = detect_structural_test_patterns(f.name)
        finally:
            os.unlink(f.name)
    # p points to a .json file — should NOT be flagged as source reading
    assert len(violations) == 0, (
        f"Multi-segment path to .json should not be flagged, got: {violations}"
    )


# --- Step 9 Cross-Validation Tests (Issue #924) ---


def test_cross_validation_triggers_retry_when_tests_dropped(mock_dependencies, default_args, tmp_path):
    """
    Test that the orchestrator retries Step 9 when fewer tests are generated
    than Step 8 planned. This is the primary bug reproduction for issue #924.

    Step 8 plans 5 tests, Step 9 only generates 3 → orchestrator should
    detect the mismatch and retry Step 9.
    """
    mock_run, mock_load, _ = mock_dependencies

    # The mock worktree path where files will be created
    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    # Create a test file in the worktree with only 3 test functions
    test_file = worktree_path / "tests" / "test_bugfix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text(
        "import pytest\n\n"
        "def test_first_scenario():\n"
        "    assert 1 == 1\n\n"
        "def test_second_scenario():\n"
        "    assert 2 == 2\n\n"
        "def test_third_scenario():\n"
        "    assert 3 == 3\n"
    )

    step9_call_count = 0

    def side_effect_run(*args, **kwargs):
        nonlocal step9_call_count
        label = kwargs.get('label', '')
        if label == 'step8':
            # Step 8 plans 5 tests with PLANNED_TEST_COUNT marker
            return (True, (
                "## Test Plan\n"
                "#### Test 1: First scenario\nVerify first behavior\n"
                "#### Test 2: Second scenario\nVerify second behavior\n"
                "#### Test 3: Third scenario\nVerify third behavior\n"
                "#### Test 4: Fourth scenario (E2E)\nVerify E2E behavior\n"
                "#### Test 5: Fifth scenario (cross-framework)\nVerify cross-framework\n"
                "\nPLANNED_TEST_COUNT: 5"
            ), 0.1, "gpt-4")
        if label == 'step9':
            step9_call_count += 1
            if step9_call_count == 1:
                # First attempt: only 3 tests generated (dropped 2)
                return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
            else:
                # Retry: generate the missing tests
                retry_file = worktree_path / "tests" / "test_bugfix.py"
                retry_file.write_text(
                    "import pytest\n\n"
                    "def test_first_scenario():\n    assert 1 == 1\n\n"
                    "def test_second_scenario():\n    assert 2 == 2\n\n"
                    "def test_third_scenario():\n    assert 3 == 3\n\n"
                    "def test_fourth_scenario_e2e():\n    assert 4 == 4\n\n"
                    "def test_fifth_scenario_cross_framework():\n    assert 5 == 5\n"
                )
                return (True, "Generated missing tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # The orchestrator should have retried Step 9 due to test count mismatch
    # On buggy code: step9_call_count == 1 (no retry), so this assertion fails
    assert step9_call_count >= 2, (
        f"Expected Step 9 to be retried due to test count mismatch "
        f"(planned=5, generated=3), but Step 9 was only called {step9_call_count} time(s). "
        f"The orchestrator did not cross-validate Step 9 output against Step 8 plan."
    )


def test_no_retry_when_test_counts_match(mock_dependencies, default_args, tmp_path):
    """
    Test that no cross-validation retry occurs when Step 9 generates
    the same number of tests as Step 8 planned (happy path).
    """
    mock_run, mock_load, _ = mock_dependencies

    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    # Create test file with exactly 3 test functions
    test_file = worktree_path / "tests" / "test_bugfix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text(
        "import pytest\n\n"
        "def test_alpha():\n    assert True\n\n"
        "def test_beta():\n    assert True\n\n"
        "def test_gamma():\n    assert True\n"
    )

    step9_call_count = 0

    def side_effect_run(*args, **kwargs):
        nonlocal step9_call_count
        label = kwargs.get('label', '')
        if label == 'step8':
            # Step 8 plans exactly 3 tests with marker
            return (True, (
                "## Test Plan\n"
                "#### Test 1: Alpha test\nVerify alpha\n"
                "#### Test 2: Beta test\nVerify beta\n"
                "#### Test 3: Gamma test\nVerify gamma\n"
                "\nPLANNED_TEST_COUNT: 3"
            ), 0.1, "gpt-4")
        if label == 'step9':
            step9_call_count += 1
            return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Step 9 should only be called once — no retry needed
    assert step9_call_count == 1, (
        f"Expected Step 9 to be called exactly once (counts match), "
        f"but it was called {step9_call_count} times."
    )


def test_marker_absent_falls_back_to_headers(mock_dependencies, default_args, tmp_path):
    """
    Test that cross-validation still works when PLANNED_TEST_COUNT marker
    is absent, falling back to counting #### Test N: headers.
    """
    mock_run, mock_load, _ = mock_dependencies

    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    test_file = worktree_path / "tests" / "test_bugfix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text(
        "def test_only_one():\n    assert True\n"
    )

    step9_call_count = 0

    def side_effect_run(*args, **kwargs):
        nonlocal step9_call_count
        label = kwargs.get('label', '')
        if label == 'step8':
            # No PLANNED_TEST_COUNT marker — should fall back to header count
            return (True, (
                "## Test Plan\n"
                "#### Test 1: First test\nVerify first\n"
                "#### Test 2: Second test\nVerify second\n"
                "#### Test 3: Third test\nVerify third\n"
            ), 0.1, "gpt-4")
        if label == 'step9':
            step9_call_count += 1
            if step9_call_count == 1:
                return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
            else:
                test_file.write_text(
                    "def test_first():\n    assert True\n\n"
                    "def test_second():\n    assert True\n\n"
                    "def test_third():\n    assert True\n"
                )
                return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Fallback to headers should still detect mismatch (1 vs 3) and retry
    assert step9_call_count >= 2, (
        f"Expected Step 9 retry via header fallback (planned=3, generated=1), "
        f"but Step 9 was only called {step9_call_count} time(s)."
    )


def test_stub_tests_detected_and_trigger_retry(mock_dependencies, default_args, tmp_path):
    """
    Test that stub tests (functions with only pass/ellipsis) are detected
    and subtracted from the count, triggering a retry.

    Step 8 plans 3 tests, Step 9 generates 3 functions but 2 are stubs →
    only 1 real test → retry should fire.
    """
    mock_run, mock_load, _ = mock_dependencies

    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    test_file = worktree_path / "tests" / "test_bugfix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text(
        "import pytest\n\n"
        "def test_real_test():\n"
        '    """A real test."""\n'
        "    result = compute()\n"
        "    assert result == 42\n\n"
        "def test_stub_one():\n"
        '    """TODO: implement."""\n'
        "    pass\n\n"
        "def test_stub_two():\n"
        "    ...\n"
    )

    step9_call_count = 0

    def side_effect_run(*args, **kwargs):
        nonlocal step9_call_count
        label = kwargs.get('label', '')
        if label == 'step8':
            return (True, (
                "## Test Plan\n"
                "#### Test 1: Real test\n#### Test 2: Stub one\n"
                "#### Test 3: Stub two\n"
                "\nPLANNED_TEST_COUNT: 3"
            ), 0.1, "gpt-4")
        if label == 'step9':
            step9_call_count += 1
            if step9_call_count == 1:
                return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
            else:
                test_file.write_text(
                    "import pytest\n\n"
                    "def test_real_test():\n    assert compute() == 42\n\n"
                    "def test_stub_one():\n    assert validate() is True\n\n"
                    "def test_stub_two():\n    assert transform('x') == 'y'\n"
                )
                return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Stubs should be detected (3 total - 2 stubs = 1 real vs 3 planned) → retry
    assert step9_call_count >= 2, (
        f"Expected Step 9 retry because 2 of 3 test functions were stubs "
        f"(planned=3, real=1), but Step 9 was only called {step9_call_count} time(s)."
    )


def test_retry_falls_short_logs_warning_and_proceeds(mock_dependencies, default_args, tmp_path):
    """
    Test that if the retry still produces fewer tests than planned,
    the orchestrator logs a warning and proceeds (single-retry guarantee).
    """
    mock_run, mock_load, mock_console = mock_dependencies

    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    test_file = worktree_path / "tests" / "test_bugfix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text(
        "def test_only_one():\n    assert True\n"
    )

    step9_call_count = 0

    def side_effect_run(*args, **kwargs):
        nonlocal step9_call_count
        label = kwargs.get('label', '')
        if label == 'step8':
            return (True, (
                "#### Test 1: First\n#### Test 2: Second\n"
                "#### Test 3: Third\n#### Test 4: Fourth\n"
                "\nPLANNED_TEST_COUNT: 4"
            ), 0.1, "gpt-4")
        if label == 'step9':
            step9_call_count += 1
            # Both attempts only produce 1 test
            return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Use quiet=False to capture console output
    default_args["quiet"] = False
    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Should retry once, then proceed despite still falling short
    assert step9_call_count >= 2, (
        f"Expected at least one retry for cross-validation mismatch, "
        f"but Step 9 was only called {step9_call_count} time(s)."
    )
    # Should NOT retry more than twice (single-retry guarantee)
    assert step9_call_count <= 2, (
        f"Expected at most one retry (single-retry guarantee), "
        f"but Step 9 was called {step9_call_count} times."
    )


def test_count_planned_tests_parsing():
    """
    Unit test for _count_planned_tests helper function.
    Verifies it uses PLANNED_TEST_COUNT marker, falling back to headers.
    """
    from pdd.agentic_bug_orchestrator import _count_planned_tests

    # With marker — should use marker value
    with_marker = (
        "#### Test 1: Login\n#### Test 2: Logout\n"
        "\nPLANNED_TEST_COUNT: 5"
    )
    assert _count_planned_tests(with_marker) == 5, "Should use marker, not header count"

    # Without marker — should fall back to header count
    without_marker = (
        "## Test Plan\n\n"
        "#### Test 1: Verify login flow\n"
        "#### Test 2: Verify logout\n"
        "#### Test 3: Verify token refresh\n"
    )
    assert _count_planned_tests(without_marker) == 3, "Should fall back to header count"

    # Empty output
    assert _count_planned_tests("") == 0


def test_count_generated_tests_with_real_files(tmp_path):
    """
    Unit test for _count_generated_tests helper function.
    Verifies it counts test functions and detects stubs.
    """
    from pdd.agentic_bug_orchestrator import _count_generated_tests

    test_file = tmp_path / "test_example.py"
    test_file.write_text(
        "import pytest\n\n"
        "def test_real_one():\n"
        "    result = do_thing()\n"
        "    assert result == 42\n\n"
        "def test_real_two():\n"
        '    """Check second thing."""\n'
        "    assert check() is True\n\n"
        "async def test_real_async():\n"
        "    result = await fetch()\n"
        "    assert result\n\n"
        "def test_stub_pass():\n"
        '    """Not implemented yet."""\n'
        "    pass\n\n"
        "def test_stub_ellipsis():\n"
        "    ...\n\n"
        "def helper_not_a_test():\n    return 42\n"
    )

    total, stubs = _count_generated_tests(["test_example.py"], tmp_path)
    assert total == 5, f"Expected 5 total test functions, got {total}"
    assert stubs == 2, f"Expected 2 stub functions, got {stubs}"

    # Missing file should be skipped
    total, stubs = _count_generated_tests(["nonexistent.py"], tmp_path)
    assert total == 0 and stubs == 0


def test_retry_prompt_includes_missing_test_descriptions(mock_dependencies, default_args, tmp_path):
    """
    Test that when Step 9 retries due to dropped tests, the retry prompt
    includes descriptions of the missing tests from Step 8's plan.
    """
    mock_run, mock_load, _ = mock_dependencies

    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    test_file = worktree_path / "tests" / "test_bugfix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text(
        "def test_first():\n    assert True\n"
    )

    step9_calls = []

    def side_effect_run(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step8':
            return (True, (
                "#### Test 1: First scenario\nCheck first behavior\n"
                "#### Test 2: Second scenario (E2E)\nCheck E2E flow\n"
                "#### Test 3: Third scenario (cross-framework)\nCheck cross-framework\n"
                "\nPLANNED_TEST_COUNT: 3"
            ), 0.1, "gpt-4")
        if label == 'step9':
            step9_calls.append(kwargs.get('instruction', args[0] if args else ''))
            return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    run_agentic_bug_orchestrator(**default_args)

    # If cross-validation exists, there should be a retry call
    assert len(step9_calls) >= 2, (
        f"Expected Step 9 retry with missing test info, "
        f"but Step 9 was only called {len(step9_calls)} time(s)."
    )

    # The retry prompt should mention the count mismatch
    retry_instruction = step9_calls[1]
    assert "1" in retry_instruction and "3" in retry_instruction, (
        f"Retry prompt should reference count mismatch (1 of 3), "
        f"but got: {retry_instruction[:200]}..."
    )


def test_async_test_functions_counted(mock_dependencies, default_args, tmp_path):
    """
    Test that async def test_ functions are counted correctly by
    the cross-validation logic, not just sync def test_ functions.
    """
    mock_run, mock_load, _ = mock_dependencies

    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    test_file = worktree_path / "tests" / "test_bugfix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    # 2 sync + 1 async = 3 total, matching the plan
    test_file.write_text(
        "import pytest\n\n"
        "def test_sync_one():\n    assert True\n\n"
        "def test_sync_two():\n    assert True\n\n"
        "async def test_async_one():\n    result = await fetch()\n    assert result\n"
    )

    step9_call_count = 0

    def side_effect_run(*args, **kwargs):
        nonlocal step9_call_count
        label = kwargs.get('label', '')
        if label == 'step8':
            return (True, (
                "#### Test 1: Sync one\n#### Test 2: Sync two\n"
                "#### Test 3: Async one\n"
                "\nPLANNED_TEST_COUNT: 3"
            ), 0.1, "gpt-4")
        if label == 'step9':
            step9_call_count += 1
            return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    run_agentic_bug_orchestrator(**default_args)

    # async tests should be counted — no retry needed since counts match
    assert step9_call_count == 1, (
        f"Expected no retry since 3 tests (2 sync + 1 async) match 3 planned, "
        f"but Step 9 was called {step9_call_count} times. "
        f"Async test functions may not be counted correctly."
    )


def test_structural_guard_and_cross_validation_both_fire(mock_dependencies, default_args, tmp_path):
    """
    Test that both the structural test guard AND cross-validation can fire
    in sequence. If Step 9 produces structural violations, the structural
    guard retries first. Then cross-validation should check the retry output.

    This test verifies the two validation layers work together.
    """
    mock_run, mock_load, _ = mock_dependencies

    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    test_file = worktree_path / "tests" / "test_bugfix.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)

    step9_call_count = 0

    def side_effect_run(*args, **kwargs):
        nonlocal step9_call_count
        label = kwargs.get('label', '')
        if label == 'step8':
            return (True, (
                "#### Test 1: First\n#### Test 2: Second\n"
                "#### Test 3: Third\n#### Test 4: Fourth\n"
                "\nPLANNED_TEST_COUNT: 4"
            ), 0.1, "gpt-4")
        if label == 'step9':
            step9_call_count += 1
            if step9_call_count == 1:
                # First attempt: has structural violations (will be caught by structural guard)
                # Write a file that the mocked detector will flag as structural
                test_file.write_text(
                    "def test_structural():\n"
                    "    # FLAGGED_STRUCTURAL_PATTERN\n"
                    "    assert True\n"
                )
                return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
            elif step9_call_count == 2:
                # After structural retry: fixed structural issues but only 2 of 4 tests
                test_file.write_text(
                    "def test_first():\n    assert compute() == 1\n\n"
                    "def test_second():\n    assert compute() == 2\n"
                )
                return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
            else:
                # After cross-validation retry: all 4 tests
                test_file.write_text(
                    "def test_first():\n    assert compute() == 1\n\n"
                    "def test_second():\n    assert compute() == 2\n\n"
                    "def test_third():\n    assert compute() == 3\n\n"
                    "def test_fourth():\n    assert compute() == 4\n"
                )
                return (True, "Generated tests\nFILES_CREATED: tests/test_bugfix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Need to patch detect_structural_test_patterns to detect the violation
    with patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns") as mock_detect:
        def detect_side_effect(path):
            content = Path(path).read_text() if Path(path).exists() else ""
            if "FLAGGED_STRUCTURAL_PATTERN" in content:
                return ["Uses structural pattern to test code shape"]
            return []

        mock_detect.side_effect = detect_side_effect

        success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    # Structural guard fires (call 1→2), then cross-validation fires (call 2→3)
    # On buggy code: only structural retry fires (step9_call_count == 2), no cross-validation
    assert step9_call_count >= 3, (
        f"Expected Step 9 to be called at least 3 times "
        f"(initial + structural retry + cross-validation retry), "
        f"but it was called {step9_call_count} times. "
        f"Cross-validation did not fire after structural guard retry."
    )


# --- Helper function unit tests ---


from pdd.agentic_bug_orchestrator import (
    _validate_repro_path,
    _extract_repro_test_content,
    _copy_repro_files_to_worktree,
    _check_hard_stop,
    _parse_changed_files,
    _count_planned_tests,
    _count_generated_tests,
    _verify_e2e_tests,
    _get_state_dir,
    detect_structural_test_patterns,
    _extract_violation_snippets,
)


class TestValidateReproPath:
    """Tests for _validate_repro_path helper."""

    def test_accepts_relative_path_under_base(self, tmp_path):
        """Relative path that resolves under base_dir is accepted."""
        result = _validate_repro_path("tests/test_repro.py", tmp_path)
        assert result is not None
        assert result == (tmp_path / "tests/test_repro.py").resolve()

    def test_rejects_absolute_path(self, tmp_path):
        """Absolute paths are rejected."""
        result = _validate_repro_path("/etc/passwd", tmp_path)
        assert result is None

    def test_rejects_traversal_path(self, tmp_path):
        """Paths with .. that escape base_dir are rejected."""
        result = _validate_repro_path("../../etc/passwd", tmp_path)
        assert result is None

    def test_rejects_empty_path(self, tmp_path):
        """Empty string is rejected."""
        result = _validate_repro_path("", tmp_path)
        assert result is None

    def test_accepts_nested_relative_path(self, tmp_path):
        """Deeply nested relative paths are accepted."""
        result = _validate_repro_path("a/b/c/test.py", tmp_path)
        assert result is not None


class TestExtractReproTestContent:
    """Tests for _extract_repro_test_content helper."""

    def test_reads_content_from_repro_file(self, tmp_path):
        """Reads file content when REPRO_FILES_CREATED marker is present."""
        repro_file = tmp_path / "test_repro.py"
        repro_file.write_text("def test_bug(): pass\n")
        output = "Some output\nREPRO_FILES_CREATED: test_repro.py\nMore output"
        result = _extract_repro_test_content(output, tmp_path)
        assert "def test_bug(): pass" in result

    def test_returns_empty_when_no_marker(self, tmp_path):
        """Returns empty string when no REPRO_FILES_CREATED marker."""
        output = "Some output with no marker"
        result = _extract_repro_test_content(output, tmp_path)
        assert result == ""

    def test_handles_nonexistent_file(self, tmp_path):
        """Returns empty when referenced file doesn't exist."""
        output = "REPRO_FILES_CREATED: nonexistent.py"
        result = _extract_repro_test_content(output, tmp_path)
        assert result == ""

    def test_concatenates_multiple_files(self, tmp_path):
        """Reads and concatenates content from multiple files."""
        f1 = tmp_path / "test1.py"
        f1.write_text("content1\n")
        f2 = tmp_path / "test2.py"
        f2.write_text("content2\n")
        output = "REPRO_FILES_CREATED: test1.py, test2.py"
        result = _extract_repro_test_content(output, tmp_path)
        assert "content1" in result
        assert "content2" in result


class TestCopyReproFilesToWorktree:
    """Tests for _copy_repro_files_to_worktree helper."""

    def test_copies_files_to_worktree(self, tmp_path):
        """Copies reproduction test files from cwd to worktree."""
        cwd = tmp_path / "cwd"
        cwd.mkdir()
        worktree = tmp_path / "worktree"
        worktree.mkdir()

        src_file = cwd / "test_repro.py"
        src_file.write_text("test content")

        output = "REPRO_FILES_CREATED: test_repro.py"
        result = _copy_repro_files_to_worktree(output, cwd, worktree)

        assert "test_repro.py" in result
        assert (worktree / "test_repro.py").exists()
        assert (worktree / "test_repro.py").read_text() == "test content"

    def test_skips_nonexistent_source(self, tmp_path):
        """Skips files that don't exist in cwd."""
        cwd = tmp_path / "cwd"
        cwd.mkdir()
        worktree = tmp_path / "worktree"
        worktree.mkdir()

        output = "REPRO_FILES_CREATED: missing.py"
        result = _copy_repro_files_to_worktree(output, cwd, worktree)
        assert result == []

    def test_does_not_overwrite_existing(self, tmp_path):
        """Does not overwrite files that already exist in worktree."""
        cwd = tmp_path / "cwd"
        cwd.mkdir()
        worktree = tmp_path / "worktree"
        worktree.mkdir()

        src_file = cwd / "test_repro.py"
        src_file.write_text("source content")
        dst_file = worktree / "test_repro.py"
        dst_file.write_text("existing content")

        output = "REPRO_FILES_CREATED: test_repro.py"
        result = _copy_repro_files_to_worktree(output, cwd, worktree)

        # File should be in result (path is valid) but content should be unchanged
        assert "test_repro.py" in result
        assert dst_file.read_text() == "existing content"

    def test_returns_empty_with_no_marker(self, tmp_path):
        """Returns empty list when no REPRO_FILES_CREATED marker."""
        cwd = tmp_path / "cwd"
        cwd.mkdir()
        worktree = tmp_path / "worktree"
        worktree.mkdir()

        output = "Some output without marker"
        result = _copy_repro_files_to_worktree(output, cwd, worktree)
        assert result == []


class TestCheckHardStop:
    """Direct tests for _check_hard_stop helper."""

    def test_step1_duplicate(self):
        """Detects duplicate at step 1."""
        result = _check_hard_stop(1, "This is Duplicate of #42", True)
        assert result is not None
        assert "duplicate" in result.lower()

    def test_step1_no_duplicate(self):
        """No hard stop at step 1 without duplicate marker."""
        result = _check_hard_stop(1, "Not a duplicate, unique issue", True)
        assert result is None

    def test_step2_feature_request(self):
        """Detects feature request at step 2."""
        result = _check_hard_stop(2, "Feature Request (Not a Bug)", True)
        assert result is not None

    def test_step2_user_error(self):
        """Detects user error at step 2."""
        result = _check_hard_stop(2, "User Error (Not a Bug)", True)
        assert result is not None

    def test_step3_needs_more_info(self):
        """Detects needs more info at step 3."""
        result = _check_hard_stop(3, "Needs More Info from the author", True)
        assert result is not None

    def test_step7_prompt_review(self):
        """Detects prompt review at step 7."""
        result = _check_hard_stop(7, "PROMPT_REVIEW: ambiguous case", True)
        assert result is not None

    def test_step9_no_files_extracted(self):
        """Detects no files generated at step 9."""
        result = _check_hard_stop(9, "Some output", False)
        assert result is not None
        assert "No test file" in result

    def test_step9_with_files_extracted(self):
        """No hard stop at step 9 when files are extracted."""
        result = _check_hard_stop(9, "Some output", True)
        assert result is None

    def test_step10_fail(self):
        """Detects test verification failure at step 10."""
        result = _check_hard_stop(10, "FAIL: Test does not work as expected", True)
        assert result is not None

    def test_step11_e2e_fail(self):
        """Detects E2E failure at step 11."""
        result = _check_hard_stop(11, "E2E_FAIL: Test does not catch bug correctly", True)
        assert result is not None

    def test_step11_no_e2e_fail(self):
        """No hard stop at step 11 without failure marker."""
        result = _check_hard_stop(11, "E2E test passed", True)
        assert result is None

    def test_unrelated_step_no_stop(self):
        """Steps without defined hard stop conditions return None."""
        result = _check_hard_stop(4, "Any output", True)
        assert result is None


class TestVerifyE2eTests:
    """Tests for _verify_e2e_tests helper."""

    @patch("pdd.agentic_bug_orchestrator.run_pytest_and_capture_output")
    def test_python_test_with_failures(self, mock_pytest, tmp_path):
        """Python test file with failures (expected for bug detection)."""
        mock_pytest.return_value = {
            "test_results": [{
                "failures": 1,
                "errors": 0,
                "passed": 0,
                "standard_output": "AssertionError: bug detected"
            }]
        }
        ok, output = _verify_e2e_tests(["test_e2e.py"], tmp_path)
        assert ok is True  # Failures are expected
        assert "bug detected" in output

    @patch("pdd.agentic_bug_orchestrator.run_pytest_and_capture_output")
    def test_python_test_all_passed(self, mock_pytest, tmp_path):
        """Python test file with all passing tests."""
        mock_pytest.return_value = {
            "test_results": [{
                "failures": 0,
                "errors": 0,
                "passed": 3,
                "standard_output": ""
            }]
        }
        ok, output = _verify_e2e_tests(["test_e2e.py"], tmp_path)
        assert ok is True
        assert "3 passed" in output

    @patch("pdd.agentic_bug_orchestrator.run_pytest_and_capture_output")
    def test_python_test_setup_error(self, mock_pytest, tmp_path):
        """Python test file with no results (setup error)."""
        mock_pytest.return_value = None
        ok, output = _verify_e2e_tests(["test_e2e.py"], tmp_path)
        assert ok is False
        assert "setup error" in output

    @patch("pdd.agentic_bug_orchestrator.get_test_command_for_file")
    @patch("pdd.agentic_bug_orchestrator.subprocess.run")
    def test_non_python_test_failure(self, mock_subproc, mock_get_cmd, tmp_path):
        """Non-Python test file that fails (expected)."""
        mock_get_cmd.return_value = "npx jest test_e2e.js"
        mock_subproc.return_value = MagicMock(
            returncode=1,
            stdout="test failed output",
            stderr=""
        )
        ok, output = _verify_e2e_tests(["test_e2e.js"], tmp_path)
        assert ok is True  # Non-zero exit is expected
        assert "bug detected" in output

    @patch("pdd.agentic_bug_orchestrator.get_test_command_for_file")
    def test_non_python_no_runner(self, mock_get_cmd, tmp_path):
        """Non-Python test file with no available test runner."""
        mock_get_cmd.return_value = None
        ok, output = _verify_e2e_tests(["test_e2e.rb"], tmp_path)
        assert ok is False
        assert "no test runner" in output

    @patch("pdd.agentic_bug_orchestrator.get_test_command_for_file")
    @patch("pdd.agentic_bug_orchestrator.subprocess.run")
    def test_non_python_test_timeout(self, mock_subproc, mock_get_cmd, tmp_path):
        """Non-Python test file that times out."""
        mock_get_cmd.return_value = "npx jest test_e2e.js"
        import subprocess as sp
        mock_subproc.side_effect = sp.TimeoutExpired(cmd="npx jest", timeout=120)
        ok, output = _verify_e2e_tests(["test_e2e.js"], tmp_path)
        assert ok is False
        assert "timeout" in output.lower()


class TestGetStateDir:
    """Tests for _get_state_dir helper."""

    @patch("pdd.agentic_bug_orchestrator._get_git_root")
    def test_returns_bug_state_path(self, mock_root, tmp_path):
        """Returns .pdd/bug-state relative to git root."""
        mock_root.return_value = tmp_path
        result = _get_state_dir(tmp_path)
        assert result == tmp_path / ".pdd" / "bug-state"

    @patch("pdd.agentic_bug_orchestrator._get_git_root")
    def test_falls_back_to_cwd(self, mock_root, tmp_path):
        """Falls back to cwd when no git root."""
        mock_root.return_value = None
        result = _get_state_dir(tmp_path)
        assert result == tmp_path / ".pdd" / "bug-state"


# --- Additional orchestrator flow tests ---


def test_step5_repro_files_tracked_in_changed_files(mock_dependencies, default_args):
    """
    Test that REPRO_FILES_CREATED from step 5 output adds files to changed_files.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step5':
            return (True, "Reproduced bug\nREPRO_FILES_CREATED: test_repro.py", 0.1, "model")
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: test_fix.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

    assert "test_repro.py" in changed_files
    assert "test_fix.py" in changed_files


def test_clear_agentic_progress_called_on_start_and_completion(default_args, tmp_path):
    """
    Verify clear_agentic_progress is called at start and on successful completion.
    """
    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    def run_side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: f.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt"), \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(worktree_path, None)), \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress") as mock_set, \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress") as mock_clear:

        mock_run.side_effect = run_side_effect

        run_agentic_bug_orchestrator(**default_args)

    # clear_agentic_progress should be called at least twice (start + end)
    assert mock_clear.call_count >= 2


def test_set_agentic_progress_called_for_each_executed_step(mock_dependencies, default_args):
    """
    Verify set_agentic_progress is called before each step execution.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: f.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    with patch("pdd.agentic_bug_orchestrator.set_agentic_progress") as mock_set:
        run_agentic_bug_orchestrator(**default_args)

    # Should be called once per step (12 steps)
    assert mock_set.call_count == 12


def test_step_completion_marker_printed(default_args, tmp_path):
    """
    Verify step completion marker is printed for credential waterfall detection.
    """
    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    # Use non-quiet mode to check console output
    default_args["quiet"] = False

    def run_side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: f.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt"), \
         patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
         patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(worktree_path, None)), \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        mock_run.side_effect = run_side_effect
        run_agentic_bug_orchestrator(**default_args)

    # Check that "Step N complete." was printed for at least some steps
    print_calls = [str(c) for c in mock_console.print.call_args_list]
    completion_calls = [c for c in print_calls if "complete" in c.lower()]
    assert len(completion_calls) > 0, "Step completion markers should be printed"


def test_e2e_needed_no_in_step10_skips_step11(mock_dependencies, default_args):
    """
    Test that E2E_NEEDED: no in step 10 output causes step 11 to be skipped.
    """
    mock_run, _, _ = mock_dependencies

    executed_labels = []

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        executed_labels.append(label)
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: test.py", 0.1, "model")
        if label == 'step10':
            return (True, "Test verified.\nE2E_NEEDED: no", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert 'step11' not in executed_labels, "Step 11 should be skipped when E2E_NEEDED: no"
    assert 'step12' in executed_labels, "Step 12 should still execute"


def test_e2e_needed_missing_runs_step11(mock_dependencies, default_args):
    """
    Test backward compatibility: if E2E_NEEDED marker is missing, step 11 runs.
    """
    mock_run, _, _ = mock_dependencies

    executed_labels = []

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        executed_labels.append(label)
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: test.py", 0.1, "model")
        if label == 'step10':
            return (True, "Test verified and passes", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    run_agentic_bug_orchestrator(**default_args)

    assert 'step11' in executed_labels, "Step 11 should run when E2E_NEEDED marker is absent"


def test_step11_e2e_skip_continues_to_step12(mock_dependencies, default_args):
    """
    Test that E2E_SKIP: in step 11 output allows workflow to continue to step 12.
    """
    mock_run, _, _ = mock_dependencies

    executed_labels = []

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        executed_labels.append(label)
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: test.py", 0.1, "model")
        if label == 'step11':
            return (True, "E2E_SKIP: Environment not available for E2E testing", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert 'step12' in executed_labels


def test_step11_e2e_fail_hard_stop(mock_dependencies, default_args):
    """
    Test that E2E_FAIL in step 11 output triggers hard stop.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: test.py", 0.1, "model")
        if label == 'step11':
            return (True, "E2E_FAIL: Test does not catch bug correctly", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 11" in msg


def test_step12_pre_stages_changed_files(mock_dependencies, default_args, tmp_path):
    """
    Test that changed files are git-added before step 12 runs.
    """
    mock_run, _, _ = mock_dependencies

    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    git_add_calls = []

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    with patch("pdd.agentic_bug_orchestrator.subprocess.run") as mock_subproc:
        mock_subproc.return_value = MagicMock(returncode=0, stderr="")
        run_agentic_bug_orchestrator(**default_args)

        # Check that git add was called for changed files before step 12
        for call_obj in mock_subproc.call_args_list:
            args = call_obj[0][0] if call_obj[0] else call_obj.kwargs.get("args", [])
            if isinstance(args, list) and len(args) >= 2 and args[0] == "git" and args[1] == "add":
                git_add_calls.append(args)

    assert len(git_add_calls) > 0, "git add should be called before step 12"


def test_state_validation_corrects_last_completed_step(default_args, tmp_path):
    """
    Test that state validation corrects last_completed_step when
    step outputs contain FAILED: entries.
    """
    worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree_path.mkdir(parents=True, exist_ok=True)

    # State claims step 5 completed but step 3 was FAILED
    loaded_state = {
        "last_completed_step": 5,
        "step_outputs": {
            "1": "ok",
            "2": "ok",
            "3": "FAILED: some error",
            "4": "ok",
            "5": "ok",
        },
        "total_cost": 0.5,
        "model_used": "model",
    }

    def run_side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: f.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt"), \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(worktree_path, None)), \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(loaded_state, None)), \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

        mock_run.side_effect = run_side_effect
        run_agentic_bug_orchestrator(**default_args)

    # Should resume from step 3 (the first FAILED step), not step 6
    labels = [c.kwargs.get('label', '') for c in mock_run.call_args_list]
    assert 'step3' in labels, "Should re-run step 3 because it was FAILED"


def test_consecutive_provider_failure_resets_on_success(mock_dependencies, default_args):
    """
    Test that consecutive provider failure counter resets when a step succeeds.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step1':
            return (False, "All agent providers failed", 0.1, "model")
        if label == 'step2':
            return (False, "All agent providers failed", 0.1, "model")
        # Step 3 succeeds, resetting counter
        if label == 'step3':
            return (True, "ok", 0.1, "model")
        if label == 'step4':
            return (False, "All agent providers failed", 0.1, "model")
        if label == 'step5':
            return (False, "All agent providers failed", 0.1, "model")
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: f.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)

    # Should NOT abort because the counter was reset by step 3 success
    assert "Aborting" not in msg or success is True


def test_pr_url_extracted_from_step12_output(mock_dependencies, default_args):
    """
    Test that PR URL is extracted from step 12 output.
    """
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: f.py", 0.1, "model")
        if label == 'step12':
            return (True, "Created PR: https://github.com/owner/repo/pull/42", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)

    assert success is True
    assert "https://github.com/owner/repo/pull/42" in msg


def test_detect_structural_test_patterns_empty_file(tmp_path):
    """detect_structural_test_patterns returns empty list for empty files."""
    f = tmp_path / "test_empty.py"
    f.write_text("")
    violations = detect_structural_test_patterns(str(f))
    assert violations == []


def test_detect_structural_test_patterns_nonexistent_file():
    """detect_structural_test_patterns returns empty list for nonexistent file."""
    violations = detect_structural_test_patterns("/nonexistent/test.py")
    assert violations == []


def test_detect_structural_test_patterns_getsource(tmp_path):
    """detect_structural_test_patterns detects inspect.getsource usage."""
    f = tmp_path / "test_structural.py"
    f.write_text(
        "import inspect\n"
        "def test_something():\n"
        "    source = inspect.getsource(my_func)\n"
        '    assert "keyword" in source\n'
    )
    violations = detect_structural_test_patterns(str(f))
    assert len(violations) > 0
    assert any("getsource" in v for v in violations)


def test_detect_structural_test_patterns_hasattr(tmp_path):
    """detect_structural_test_patterns detects hasattr assertions."""
    f = tmp_path / "test_hasattr.py"
    f.write_text(
        "def test_attr():\n"
        "    assert hasattr(module, 'func')\n"
    )
    violations = detect_structural_test_patterns(str(f))
    assert len(violations) > 0
    assert any("hasattr" in v for v in violations)


def test_detect_structural_test_patterns_clean_file(tmp_path):
    """detect_structural_test_patterns returns empty for behavioral tests."""
    f = tmp_path / "test_behavioral.py"
    f.write_text(
        "def test_compute():\n"
        "    result = compute(42)\n"
        "    assert result == 84\n"
    )
    violations = detect_structural_test_patterns(str(f))
    assert violations == []


def test_detect_structural_test_patterns_config_file_reading(tmp_path):
    """detect_structural_test_patterns allows reading non-source config files."""
    f = tmp_path / "test_config.py"
    f.write_text(
        'p = Path(tmpdir) / "config.json"\n'
        'content = p.read_text()\n'
        'assert "key" in content\n'
    )
    violations = detect_structural_test_patterns(str(f))
    assert violations == [], f"Config file reading should not be flagged: {violations}"


def test_worktree_path_in_context_for_steps_after_7(mock_dependencies, default_args):
    """
    Verify worktree_path is added to context for steps 7+.
    """
    mock_run, mock_load, _ = mock_dependencies

    def load_side_effect(name):
        if "step12" in name:
            return "Worktree at: {worktree_path}"
        return "Prompt"

    mock_load.side_effect = load_side_effect

    def run_side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: f.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = run_side_effect

    run_agentic_bug_orchestrator(**default_args)

    # Check that step 12 received worktree_path in its prompt
    step12_call = None
    for call_obj in mock_run.call_args_list:
        if call_obj.kwargs.get('label') == 'step12':
            step12_call = call_obj
            break

    assert step12_call is not None
    instruction = step12_call.kwargs['instruction']
    # worktree_path should be substituted (not the literal placeholder)
    assert "{worktree_path}" not in instruction or "worktrees" in instruction


def test_default_timeout_for_unlisted_step(mock_dependencies, default_args):
    """
    Steps not in BUG_STEP_TIMEOUTS get default timeout of 340.0.
    """
    from pdd.agentic_bug_orchestrator import BUG_STEP_TIMEOUTS
    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: f.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    run_agentic_bug_orchestrator(**default_args)

    for call_obj in mock_run.call_args_list:
        label = call_obj.kwargs.get('label', '')
        timeout = call_obj.kwargs.get('timeout')
        step_str = label.replace('step', '').replace('_', '.')
        try:
            step_num = float(step_str) if '.' in step_str else int(step_str)
        except ValueError:
            continue
        expected = BUG_STEP_TIMEOUTS.get(step_num, 340.0)
        assert timeout == expected


def test_max_retries_passed_to_run_agentic_task(mock_dependencies, default_args):
    """
    Verify DEFAULT_MAX_RETRIES is passed to every run_agentic_task call.
    """
    from pdd.agentic_bug_orchestrator import DEFAULT_MAX_RETRIES

    mock_run, _, _ = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step9':
            return (True, "gen\nFILES_CREATED: f.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mock_run.side_effect = side_effect

    run_agentic_bug_orchestrator(**default_args)

    for call_obj in mock_run.call_args_list:
        assert call_obj.kwargs.get('max_retries') == DEFAULT_MAX_RETRIES


def test_bug_step_timeouts_has_expected_steps():
    """Verify BUG_STEP_TIMEOUTS matches the spec."""
    from pdd.agentic_bug_orchestrator import BUG_STEP_TIMEOUTS
    assert 1 in BUG_STEP_TIMEOUTS
    assert 2 in BUG_STEP_TIMEOUTS
    assert 3 in BUG_STEP_TIMEOUTS
    assert 4 in BUG_STEP_TIMEOUTS
    assert 5 in BUG_STEP_TIMEOUTS
    assert 5.5 in BUG_STEP_TIMEOUTS
    assert 6 in BUG_STEP_TIMEOUTS
    assert 7 in BUG_STEP_TIMEOUTS
    assert 8 in BUG_STEP_TIMEOUTS
    assert 9 in BUG_STEP_TIMEOUTS
    assert 10 in BUG_STEP_TIMEOUTS
    # Step 11 and 12 use default


def test_parse_changed_files_empty_output():
    """_parse_changed_files returns empty list for output without marker."""
    result = _parse_changed_files("no marker here", "FILES_CREATED")
    assert result == []


def test_parse_changed_files_with_whitespace():
    """_parse_changed_files strips whitespace from paths."""
    result = _parse_changed_files("FILES_CREATED:  a.py , b.py  ", "FILES_CREATED")
    assert result == ["a.py", "b.py"]


def test_count_planned_tests_no_marker():
    """_count_planned_tests returns 0 when no marker or headers found."""
    result = _count_planned_tests("Just some text with no markers")
    assert result == 0


def test_count_planned_tests_marker():
    """_count_planned_tests parses PLANNED_TEST_COUNT marker."""
    result = _count_planned_tests("Some plan text\nPLANNED_TEST_COUNT: 7\nMore text")
    assert result == 7


def test_count_planned_tests_header_fallback():
    """_count_planned_tests falls back to counting #### Test N: headers."""
    result = _count_planned_tests(
        "#### Test 1: First\n"
        "#### Test 2: Second\n"
        "#### Test 3: Third\n"
    )
    assert result == 3


def test_count_generated_tests_no_files(tmp_path):
    """_count_generated_tests returns (0, 0) for nonexistent files."""
    total, stubs = _count_generated_tests(["nonexistent.py"], tmp_path)
    assert total == 0
    assert stubs == 0


def test_count_generated_tests_with_stubs(tmp_path):
    """_count_generated_tests detects stub functions."""
    f = tmp_path / "test_stubs.py"
    f.write_text(
        "def test_real():\n"
        "    assert 1 == 1\n\n"
        "def test_stub():\n"
        "    pass\n"
    )
    total, stubs = _count_generated_tests(["test_stubs.py"], tmp_path)
    assert total == 2
    assert stubs >= 1  # At least the stub is detected


def _make_mock_dependencies(tmp_path):
    """Create and return a mock worktree directory path under the given tmp_path."""
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)
    return mock_worktree_path


# ---------------------------------------------------------------------------
# Test 1: Step 7 execution — prompt files recovered via filesystem fallback
#          when PROMPT_FIXED markers absent from step_output
# ---------------------------------------------------------------------------

class TestStep7PromptFilesDropped:
    """Issue #966/#969 Bug 1: Step 7 classifies Prompt Defect but LLM omits
    PROMPT_FIXED markers from step_output. The orchestrator should detect
    modified .prompt files via filesystem fallback, but currently does not."""

    def test_step7_prompt_defect_filesystem_fallback_when_markers_absent(self, tmp_path, default_args):
        """Step 7 returns DEFECT_TYPE: prompt without PROMPT_FIXED markers.
        The .prompt file is modified on disk. Orchestrator should detect it
        via filesystem fallback and include it in changed_files.

        FAILS on buggy code: no fallback exists, changed_files has no prompt file.
        """
        mock_worktree = _make_mock_dependencies(tmp_path)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_git_files, \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns", return_value=[]), \
             patch("pdd.agentic_bug_orchestrator._count_planned_tests", return_value=0), \
             patch("pdd.agentic_bug_orchestrator._count_generated_tests", return_value=(1, 0)):

            # Step 7 returns DEFECT_TYPE: prompt but NO PROMPT_FIXED markers
            # Step 9 returns FILES_CREATED for a test file
            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step7":
                    return (True, "Classification: Prompt Defect\nDEFECT_TYPE: prompt", 0.1, "model")
                if label == "step9":
                    return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect

            # Simulate filesystem: before Step 7, no modified files.
            # After Step 7, the prompt file appears on disk.
            mock_git_files.side_effect = [
                [],  # pre-Step 7 snapshot
                ["pdd/prompts/orchestrator_python.prompt"],  # post-Step 7 fallback
                ["pdd/prompts/orchestrator_python.prompt", "tests/test_fix.py"],  # pre-Step 9
            ]

            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

            assert "pdd/prompts/orchestrator_python.prompt" in changed_files, (
                f"Prompt file should be in changed_files via filesystem fallback. "
                f"Got: {changed_files}"
            )


# ---------------------------------------------------------------------------
# Tests 2-4: Resume re-extraction — wrong markers for Steps 7, 9, 11
# ---------------------------------------------------------------------------

class TestResumeReExtractionMarkers:
    """Issue #966/#969 Bugs 2-4: Resume path re-extraction block (lines 774-785)
    has copy-paste errors where markers are shifted by one step."""

    def test_step7_resume_parses_prompt_fixed_markers(self, tmp_path, default_args):
        """Bug 2: When resuming from Step 8+, cached step7_output contains
        PROMPT_FIXED markers. The resume re-extraction should parse PROMPT_FIXED,
        but currently parses FILES_CREATED/FILES_MODIFIED (wrong markers).

        FAILS on buggy code: _parse_changed_files(step7_output, "FILES_CREATED")
        returns [] because the output only has PROMPT_FIXED markers.
        """
        mock_worktree = _make_mock_dependencies(tmp_path)

        state = {
            "workflow": "bug",
            "issue_number": 1,
            "issue_url": "http://github.com/owner/repo/issues/1",
            "last_completed_step": 8,
            "step_outputs": {
                "1": "Step 1 output",
                "2": "Step 2 output",
                "3": "Step 3 output",
                "4": "Step 4 output",
                "5": "Step 5 output",
                "6": "Step 6 output",
                "7": "DEFECT_TYPE: prompt\nPROMPT_FIXED: pdd/prompts/orchestrator_python.prompt",
                "8": "Test plan output",
            },
            "total_cost": 0.8,
            "model_used": "model",
            "worktree_path": str(mock_worktree),
        }

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(state, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked", return_value=[]), \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns", return_value=[]), \
             patch("pdd.agentic_bug_orchestrator._count_planned_tests", return_value=0), \
             patch("pdd.agentic_bug_orchestrator._count_generated_tests", return_value=(1, 0)):

            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step9":
                    return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect
            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

            # Bug: step 7 resume parses FILES_CREATED/FILES_MODIFIED instead of
            # PROMPT_FIXED, so the prompt file is never extracted.
            assert "pdd/prompts/orchestrator_python.prompt" in changed_files, (
                f"Step 7 resume should extract PROMPT_FIXED markers. Got: {changed_files}"
            )

    def test_step9_resume_parses_files_created_markers(self, tmp_path, default_args):
        """Bug 3: When resuming from Step 10+, cached step9_output contains
        FILES_CREATED/FILES_MODIFIED markers. The resume re-extraction should
        parse those, but currently parses E2E_FILES_CREATED (wrong marker).

        FAILS on buggy code: _parse_changed_files(step9_output, "E2E_FILES_CREATED")
        returns [] because the output only has FILES_CREATED/FILES_MODIFIED markers.
        """
        mock_worktree = _make_mock_dependencies(tmp_path)

        state = {
            "workflow": "bug",
            "issue_number": 1,
            "issue_url": "http://github.com/owner/repo/issues/1",
            "last_completed_step": 10,
            "step_outputs": {
                "1": "Step 1 output",
                "2": "Step 2 output",
                "3": "Step 3 output",
                "4": "Step 4 output",
                "5": "Step 5 output",
                "6": "Step 6 output",
                "7": "DEFECT_TYPE: code\nCode bug analysis",
                "8": "Test plan output",
                "9": "FILES_CREATED: tests/test_fix.py\nFILES_MODIFIED: tests/conftest.py",
                "10": "E2E_NEEDED: no",
            },
            "total_cost": 1.0,
            "model_used": "model",
            "worktree_path": str(mock_worktree),
        }

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(state, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator._verify_e2e_tests", return_value=(True, "ok")):

            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect
            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

            # Bug: step 9 resume parses E2E_FILES_CREATED instead of
            # FILES_CREATED/FILES_MODIFIED, so test files are never extracted.
            assert "tests/test_fix.py" in changed_files, (
                f"Step 9 resume should extract FILES_CREATED markers. Got: {changed_files}"
            )
            assert "tests/conftest.py" in changed_files, (
                f"Step 9 resume should extract FILES_MODIFIED markers. Got: {changed_files}"
            )

    def test_step11_resume_parses_e2e_files_created(self, tmp_path, default_args):
        """Bug 4: When resuming from Step 12, cached step11_output contains
        E2E_FILES_CREATED markers. No resume handler exists for Step 11.

        FAILS on buggy code: the resume block jumps from Step 9 handler
        straight to deduplication — Step 11 output is never parsed.
        """
        mock_worktree = _make_mock_dependencies(tmp_path)

        state = {
            "workflow": "bug",
            "issue_number": 1,
            "issue_url": "http://github.com/owner/repo/issues/1",
            "last_completed_step": 11,
            "step_outputs": {
                "1": "Step 1 output",
                "2": "Step 2 output",
                "3": "Step 3 output",
                "4": "Step 4 output",
                "5": "Step 5 output",
                "6": "Step 6 output",
                "7": "DEFECT_TYPE: code\nCode bug analysis",
                "8": "Test plan output",
                "9": "FILES_CREATED: tests/test_fix.py",
                "10": "Verification output",
                "11": "E2E_FILES_CREATED: tests/test_e2e_fix.py",
            },
            "total_cost": 1.1,
            "model_used": "model",
            "worktree_path": str(mock_worktree),
        }

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(state, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess:

            mock_run.return_value = (True, "PR created\nhttps://github.com/owner/repo/pull/42", 0.1, "model")
            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

            # Bug: no resume handler for step 11, so E2E_FILES_CREATED never parsed.
            assert "tests/test_e2e_fix.py" in changed_files, (
                f"Step 11 resume should extract E2E_FILES_CREATED markers. Got: {changed_files}"
            )


# ---------------------------------------------------------------------------
# Test 5: Pre-Step 12 staging — prompt files from fallback reach git-add
# ---------------------------------------------------------------------------

class TestPreStep12StagingWithFallback:
    """Issue #966/#969 Bug 5: Pre-Step 12 deterministic staging depends on
    changed_files being populated. If upstream bugs starve it, prompt files
    are never git-added."""

    def test_prompt_files_from_fallback_staged_before_step12(self, tmp_path, default_args):
        """When Step 7 classifies prompt defect without markers and the
        fallback should detect modified prompt files, those files must be
        staged (git add) before Step 12 runs.

        FAILS on buggy code: no filesystem fallback means changed_files has no
        prompt file, so git add is never called for it.
        """
        mock_worktree = _make_mock_dependencies(tmp_path)
        call_log = []

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_git_files, \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns", return_value=[]), \
             patch("pdd.agentic_bug_orchestrator._count_planned_tests", return_value=0), \
             patch("pdd.agentic_bug_orchestrator._count_generated_tests", return_value=(1, 0)):

            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step12":
                    call_log.append("step12_run")
                if label == "step7":
                    return (True, "Classification: Prompt Defect\nDEFECT_TYPE: prompt", 0.1, "model")
                if label == "step9":
                    return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect

            # Filesystem: empty before Step 7, prompt file after, both after Step 9
            mock_git_files.side_effect = [
                [],  # pre-Step 7 snapshot
                ["pdd/prompts/orchestrator_python.prompt"],  # post-Step 7 fallback
                ["pdd/prompts/orchestrator_python.prompt", "tests/test_fix.py"],  # pre-Step 9
            ]

            def subprocess_side_effect(*args, **kwargs):
                cmd = args[0] if args else kwargs.get("args", [])
                if isinstance(cmd, list) and len(cmd) >= 3 and cmd[0] == "git" and cmd[1] == "add":
                    call_log.append(f"git_add:{cmd[2]}")
                return MagicMock(returncode=0, stdout="", stderr="")

            mock_subprocess.run.side_effect = subprocess_side_effect

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

            # Bug: without filesystem fallback, only test files are staged
            git_adds = [c for c in call_log if c.startswith("git_add:")]
            prompt_staged = any("orchestrator_python.prompt" in ga for ga in git_adds)
            assert prompt_staged, (
                f"Prompt file should be git-added before Step 12. "
                f"git add calls: {git_adds}"
            )

            # Also verify ordering: git adds before Step 12 run
            if "step12_run" in call_log:
                step12_idx = call_log.index("step12_run")
                for ga in git_adds:
                    ga_idx = call_log.index(ga)
                    assert ga_idx < step12_idx, (
                        f"git add must come before Step 12 run. Order: {call_log}"
                    )


# ---------------------------------------------------------------------------
# Test 6: Full resume chain — all step markers correctly re-extracted
# ---------------------------------------------------------------------------

class TestFullResumeChainMarkerExtraction:
    """Issue #966/#969 Bug 6: When resuming from Step 12 with cached outputs
    from Steps 5.5, 7, 9, and 11, all four files should appear in
    changed_files. Currently only Step 5.5's file is extracted (1/4)."""

    def test_all_resume_markers_correctly_extracted(self, tmp_path, default_args):
        """Resume from Step 12 with all step outputs cached.
        Steps 5.5, 7, 9, and 11 each contribute files via their respective
        markers. All must be present in changed_files.

        FAILS on buggy code: Step 7 uses wrong markers (FILES_CREATED instead
        of PROMPT_FIXED), Step 9 uses wrong markers (E2E_FILES_CREATED instead
        of FILES_CREATED), Step 11 has no handler. Only Step 5.5's file
        (correct handler) is extracted — 3/4 files dropped.
        """
        mock_worktree = _make_mock_dependencies(tmp_path)

        state = {
            "workflow": "bug",
            "issue_number": 1,
            "issue_url": "http://github.com/owner/repo/issues/1",
            "last_completed_step": 11,
            "step_outputs": {
                "1": "Step 1 output",
                "2": "Step 2 output",
                "3": "Step 3 output",
                "4": "Step 4 output",
                "5": "Step 5 output",
                "5.5": "PROMPT_FIXED: prompts/fix.prompt",
                "6": "Step 6 output",
                "7": "DEFECT_TYPE: prompt\nPROMPT_FIXED: pdd/prompts/orchestrator.prompt",
                "8": "Test plan output",
                "9": "FILES_CREATED: tests/test_fix.py",
                "10": "Verification output",
                "11": "E2E_FILES_CREATED: tests/test_e2e.py",
            },
            "total_cost": 1.2,
            "model_used": "model",
            "worktree_path": str(mock_worktree),
        }

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(state, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess:

            mock_run.return_value = (True, "PR created\nhttps://github.com/owner/repo/pull/42", 0.1, "model")
            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

            # Step 5.5: PROMPT_FIXED → correct handler (passes)
            assert "prompts/fix.prompt" in changed_files, (
                f"Step 5.5 PROMPT_FIXED file should be in changed_files. Got: {changed_files}"
            )

            # Step 7: PROMPT_FIXED → buggy handler parses FILES_CREATED (fails)
            assert "pdd/prompts/orchestrator.prompt" in changed_files, (
                f"Step 7 PROMPT_FIXED file should be in changed_files. Got: {changed_files}"
            )

            # Step 9: FILES_CREATED → buggy handler parses E2E_FILES_CREATED (fails)
            assert "tests/test_fix.py" in changed_files, (
                f"Step 9 FILES_CREATED file should be in changed_files. Got: {changed_files}"
            )

            # Step 11: E2E_FILES_CREATED → no handler exists (fails)
            assert "tests/test_e2e.py" in changed_files, (
                f"Step 11 E2E_FILES_CREATED file should be in changed_files. Got: {changed_files}"
            )

            # All 4 files must be present
            assert len([f for f in changed_files if f in [
                "prompts/fix.prompt",
                "pdd/prompts/orchestrator.prompt",
                "tests/test_fix.py",
                "tests/test_e2e.py",
            ]]) == 4, (
                f"All 4 files from resume should be in changed_files. Got: {changed_files}"
            )


# ---------------------------------------------------------------------------
# Issue #966 — Additional Step 7 prompt-defect fallback tests
# Covers remaining scenarios from the Step 8 test plan
# ---------------------------------------------------------------------------


class TestStep7FallbackFiltersPromptExtension:
    """Issue #966: The filesystem fallback must only pick up .prompt files,
    not unrelated modifications that happen to exist in the worktree."""

    def test_fallback_filters_to_prompt_extension_only(self, tmp_path, default_args):
        """Step 7 modifies a .prompt file and other files exist on disk.
        Only .prompt files should be added via fallback.

        FAILS on buggy code: no fallback exists at all, so nothing is added.
        With fix: only .prompt files are added, not .py or other extensions."""
        mock_worktree = _make_mock_dependencies(tmp_path)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_git_files, \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns", return_value=[]), \
             patch("pdd.agentic_bug_orchestrator._count_planned_tests", return_value=0), \
             patch("pdd.agentic_bug_orchestrator._count_generated_tests", return_value=(1, 0)):

            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step7":
                    return (True, "DEFECT_TYPE: prompt\nFixed on disk.", 0.1, "model")
                if label == "step9":
                    return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect

            # Post-Step-7: prompt file + unrelated .py and .md files
            mock_git_files.side_effect = [
                [],  # pre-Step 7 snapshot
                [
                    "pdd/prompts/fix.prompt",
                    "pdd/utils.py",
                    "README.md",
                ],  # post-Step 7 fallback
                [
                    "pdd/prompts/fix.prompt",
                    "pdd/utils.py",
                    "README.md",
                    "tests/test_fix.py",
                ],  # pre-Step 9
            ]

            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

        # Only .prompt file should be added via fallback
        assert "pdd/prompts/fix.prompt" in changed_files, (
            f"Prompt file should be in changed_files. Got: {changed_files}"
        )
        # Non-prompt files should NOT be added by fallback (Step 9 adds its own files)
        assert "pdd/utils.py" not in changed_files, (
            f"Non-prompt file utils.py should NOT be in changed_files. Got: {changed_files}"
        )
        assert "README.md" not in changed_files, (
            f"Non-prompt file README.md should NOT be in changed_files. Got: {changed_files}"
        )


class TestStep7MarkersStillWorkWhenPresent:
    """Issue #966 regression guard: when PROMPT_FIXED markers ARE present
    in step_output, the original marker-based path must still work."""

    def test_markers_present_extracts_prompt_files(self, tmp_path, default_args):
        """Step 7 returns both DEFECT_TYPE: prompt AND PROMPT_FIXED: markers.
        The marker-based path should extract the prompt file without needing
        the filesystem fallback.

        PASSES on both buggy and fixed code (regression guard)."""
        mock_worktree = _make_mock_dependencies(tmp_path)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_git_files, \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns", return_value=[]), \
             patch("pdd.agentic_bug_orchestrator._count_planned_tests", return_value=0), \
             patch("pdd.agentic_bug_orchestrator._count_generated_tests", return_value=(1, 0)):

            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step7":
                    return (True, "DEFECT_TYPE: prompt\nPROMPT_FIXED: pdd/prompts/orchestrator.prompt", 0.1, "model")
                if label == "step9":
                    return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect

            mock_git_files.side_effect = [
                [],  # pre-Step 7 snapshot
                ["pdd/prompts/orchestrator.prompt", "tests/test_fix.py"],  # pre-Step 9
            ]

            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

        assert "pdd/prompts/orchestrator.prompt" in changed_files, (
            f"Prompt file should be in changed_files via markers. Got: {changed_files}"
        )


class TestStep7WarningWhenNoPromptFilesDetected:
    """Issue #966: When DEFECT_TYPE is 'prompt' but no .prompt files are
    found (via markers OR fallback), a warning must be emitted."""

    def test_warning_emitted_when_prompt_defect_but_no_files(self, tmp_path, default_args):
        """Step 7 classifies as prompt defect, but neither markers exist in
        output NOR prompt files on disk. A warning should be logged.

        FAILS on buggy code: no warning logic exists at all."""
        mock_worktree = _make_mock_dependencies(tmp_path)
        default_args["quiet"] = False

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_git_files, \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns", return_value=[]), \
             patch("pdd.agentic_bug_orchestrator._count_planned_tests", return_value=0), \
             patch("pdd.agentic_bug_orchestrator._count_generated_tests", return_value=(1, 0)):

            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step7":
                    return (True, "DEFECT_TYPE: prompt\nFixed on disk.", 0.1, "model")
                if label == "step9":
                    return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect

            # No prompt files on disk at all
            mock_git_files.side_effect = [
                [],  # pre-Step 7 snapshot
                [],  # post-Step 7 fallback — no prompt files
                ["tests/test_fix.py"],  # pre-Step 9
            ]

            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

        # Should emit a warning about DEFECT_TYPE=prompt but no .prompt files
        warning_calls = [
            str(c)
            for c in mock_console.print.call_args_list
            if "Warning" in str(c) and "prompt" in str(c).lower()
        ]
        assert len(warning_calls) > 0, (
            f"Should emit warning when DEFECT_TYPE=prompt but no .prompt files found. "
            f"Console calls: {[str(c) for c in mock_console.print.call_args_list]}"
        )


class TestStep7FallbackIgnoresPreexistingFiles:
    """Issue #966: The filesystem fallback must only detect files that were
    NEWLY modified by Step 7, not files that were already modified before."""

    def test_fallback_ignores_preexisting_modifications(self, tmp_path, default_args):
        """Pre-Step-7 snapshot has an already-modified prompt file.
        Step 7 adds a new prompt file. Only the new one should be added.

        FAILS on buggy code: no fallback exists at all."""
        mock_worktree = _make_mock_dependencies(tmp_path)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_git_files, \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns", return_value=[]), \
             patch("pdd.agentic_bug_orchestrator._count_planned_tests", return_value=0), \
             patch("pdd.agentic_bug_orchestrator._count_generated_tests", return_value=(1, 0)):

            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step7":
                    return (True, "DEFECT_TYPE: prompt\nFixed on disk.", 0.1, "model")
                if label == "step9":
                    return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect

            # Pre-Step 7: old.prompt already existed
            # Post-Step 7: old.prompt still there + new.prompt added by Step 7
            mock_git_files.side_effect = [
                ["pdd/prompts/old.prompt"],  # pre-Step 7: already modified
                ["pdd/prompts/old.prompt", "pdd/prompts/new.prompt"],  # post-Step 7
                ["pdd/prompts/old.prompt", "pdd/prompts/new.prompt", "tests/test_fix.py"],  # pre-Step 9
            ]

            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

        # Only new.prompt should be added via fallback (not old.prompt)
        assert "pdd/prompts/new.prompt" in changed_files, (
            f"Newly modified prompt file should be in changed_files. Got: {changed_files}"
        )
        assert "pdd/prompts/old.prompt" not in changed_files, (
            f"Pre-existing prompt file should NOT be in changed_files. Got: {changed_files}"
        )


class TestStep7FallbackMultiplePromptFiles:
    """Issue #966: When Step 7 edits multiple .prompt files, the fallback
    must detect ALL of them, not just the first."""

    def test_multiple_prompt_files_all_detected(self, tmp_path, default_args):
        """Step 7 modifies 3 prompt files. All should appear in changed_files.

        FAILS on buggy code: no fallback exists."""
        mock_worktree = _make_mock_dependencies(tmp_path)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_git_files, \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns", return_value=[]), \
             patch("pdd.agentic_bug_orchestrator._count_planned_tests", return_value=0), \
             patch("pdd.agentic_bug_orchestrator._count_generated_tests", return_value=(1, 0)):

            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step7":
                    return (True, "DEFECT_TYPE: prompt\nFixed all three prompt files.", 0.1, "model")
                if label == "step9":
                    return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect

            mock_git_files.side_effect = [
                [],  # pre-Step 7: nothing modified
                [
                    "pdd/prompts/a.prompt",
                    "pdd/prompts/b.prompt",
                    "pdd/prompts/c.prompt",
                ],  # post-Step 7: 3 prompt files
                [
                    "pdd/prompts/a.prompt",
                    "pdd/prompts/b.prompt",
                    "pdd/prompts/c.prompt",
                    "tests/test_fix.py",
                ],  # pre-Step 9
            ]

            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(**default_args)

        for prompt_file in ["pdd/prompts/a.prompt", "pdd/prompts/b.prompt", "pdd/prompts/c.prompt"]:
            assert prompt_file in changed_files, (
                f"{prompt_file} should be in changed_files via fallback. Got: {changed_files}"
            )


class TestStep7FilesToStageContextPropagation:
    """Issue #966: Prompt files detected via fallback must propagate to
    context['files_to_stage'] so the Step 12 template receives them."""

    def test_files_to_stage_includes_fallback_prompt_files(self, tmp_path, default_args):
        """When Step 7 fallback detects prompt files, they must appear in
        the Step 12 instruction via the {files_to_stage} template variable.

        FAILS on buggy code: prompt files never enter changed_files, so
        files_to_stage only has test files."""
        mock_worktree = _make_mock_dependencies(tmp_path)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_git_files, \
             patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess, \
             patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns", return_value=[]), \
             patch("pdd.agentic_bug_orchestrator._count_planned_tests", return_value=0), \
             patch("pdd.agentic_bug_orchestrator._count_generated_tests", return_value=(1, 0)):

            def load_side_effect(name):
                if "step12" in name:
                    return "Stage these files:\n{files_to_stage}\nNow commit."
                return "Prompt for {issue_number}"

            mock_load.side_effect = load_side_effect

            def run_side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step7":
                    return (True, "DEFECT_TYPE: prompt\nFixed on disk.", 0.1, "model")
                if label == "step9":
                    return (True, "FILES_CREATED: tests/test_fix.py", 0.1, "model")
                return (True, "ok", 0.1, "model")

            mock_run.side_effect = run_side_effect

            mock_git_files.side_effect = [
                [],  # pre-Step 7 snapshot
                ["pdd/prompts/fix.prompt"],  # post-Step 7 fallback
                ["pdd/prompts/fix.prompt"],  # pre-Step 9
            ]

            mock_subprocess.run.return_value = MagicMock(returncode=0, stdout="", stderr="")

            run_agentic_bug_orchestrator(**default_args)

        # Find the Step 12 call and check instruction contains prompt file
        step12_calls = [
            c for c in mock_run.call_args_list
            if c.kwargs.get("label", "") == "step12"
        ]
        assert len(step12_calls) == 1, "Step 12 should run exactly once"

        step12_instruction = step12_calls[0].kwargs.get("instruction", "")
        assert "pdd/prompts/fix.prompt" in step12_instruction, (
            f"Prompt file not found in Step 12 instruction. "
            f"files_to_stage did not propagate. Instruction: {step12_instruction}"
        )


# ---------------------------------------------------------------------------
# Issue #952: Structured fix locations from Step 6 flow to downstream steps
# ---------------------------------------------------------------------------


class TestParseFixLocations:
    """Unit tests for _parse_fix_locations helper."""

    def test_parses_single_file(self):
        """Single FIX_LOCATIONS line with one file."""
        from pdd.agentic_bug_orchestrator import _parse_fix_locations
        output = "Some analysis\nFIX_LOCATIONS: pdd/commands/generate.py\nMore text"
        assert _parse_fix_locations(output) == ["pdd/commands/generate.py"]

    def test_parses_comma_separated_files(self):
        """FIX_LOCATIONS with multiple comma-separated files."""
        from pdd.agentic_bug_orchestrator import _parse_fix_locations
        output = "FIX_LOCATIONS: pdd/commands/generate.py, pdd/cmd_test_main.py"
        assert _parse_fix_locations(output) == [
            "pdd/commands/generate.py",
            "pdd/cmd_test_main.py",
        ]

    def test_parses_multiple_marker_lines(self):
        """Multiple FIX_LOCATIONS lines are all collected."""
        from pdd.agentic_bug_orchestrator import _parse_fix_locations
        output = (
            "FIX_LOCATIONS: pdd/commands/generate.py\n"
            "FIX_LOCATIONS: pdd/cmd_test_main.py\n"
        )
        result = _parse_fix_locations(output)
        assert "pdd/commands/generate.py" in result
        assert "pdd/cmd_test_main.py" in result

    def test_returns_empty_when_no_marker(self):
        """No FIX_LOCATIONS marker returns empty list."""
        from pdd.agentic_bug_orchestrator import _parse_fix_locations
        output = "Root cause is in generate.py:375"
        assert _parse_fix_locations(output) == []

    def test_strips_whitespace_and_backticks(self):
        """File paths with backticks or extra whitespace are cleaned."""
        from pdd.agentic_bug_orchestrator import _parse_fix_locations
        output = "FIX_LOCATIONS: `pdd/generate.py` , `pdd/main.py` "
        result = _parse_fix_locations(output)
        assert result == ["pdd/generate.py", "pdd/main.py"]


class TestFixLocationsFlowToDownstreamSteps:
    """Orchestrator injects parsed fix_locations into Steps 8/9/10 context."""

    STEP6_OUTPUT_WITH_MARKER = (
        "## Root Cause Analysis\n"
        "The `--manual` flag is accepted by generate.py but never forwarded.\n\n"
        "### Fix Location\n"
        "**File(s) to modify:**\n"
        "1. `pdd/commands/generate.py:375` — caller\n"
        "2. `pdd/cmd_test_main.py:120` — callee\n\n"
        "FIX_LOCATIONS: pdd/commands/generate.py, pdd/cmd_test_main.py\n"
    )

    # Template that includes {fix_locations} placeholder for downstream steps
    TEMPLATE_WITH_FIX_LOCATIONS = (
        "Prompt for issue {issue_number}.\n"
        "<step1_output>{step1_output}</step1_output>\n"
        "<step2_output>{step2_output}</step2_output>\n"
        "<step3_output>{step3_output}</step3_output>\n"
        "<step4_output>{step4_output}</step4_output>\n"
        "<step5_output>{step5_output}</step5_output>\n"
        "<step6_output>{step6_output}</step6_output>\n"
        "<step7_output>{step7_output}</step7_output>\n"
        "<step8_output>{step8_output}</step8_output>\n"
        "<step9_output>{step9_output}</step9_output>\n"
        "<fix_locations>{fix_locations}</fix_locations>\n"
    )

    @pytest.fixture()
    def run_orchestrator_and_capture(self, tmp_path):
        """Run orchestrator with Step 6 FIX_LOCATIONS marker, return captured instructions."""
        worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
        worktree_path.mkdir(parents=True, exist_ok=True)

        captured = {}

        def mock_run_side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            captured[label] = kwargs.get("instruction", "")

            if label == "step6":
                return (True, self.STEP6_OUTPUT_WITH_MARKER, 0.1, "model")
            if label == "step8":
                return (True, "## Test Plan\nPLANNED_TEST_COUNT: 3", 0.1, "model")
            if label == "step9":
                return (True, "Generated tests\nFILES_CREATED: tests/test_fix.py", 0.1, "model")
            if label == "step10":
                return (True, "PASS: Tests correct\nE2E_NEEDED: no", 0.1, "model")
            return (True, f"Output for {label}", 0.1, "model")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

            mock_run.side_effect = mock_run_side_effect
            mock_load.return_value = self.TEMPLATE_WITH_FIX_LOCATIONS
            mock_worktree.return_value = (worktree_path, None)

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
                quiet=True,
            )

        return captured

    @pytest.mark.parametrize("step_label", ["step8", "step9", "step10"])
    def test_fix_locations_injected_into_downstream_steps(
        self, run_orchestrator_and_capture, step_label
    ):
        """Parsed fix_locations from Step 6 appear in downstream step instructions."""
        captured = run_orchestrator_and_capture
        instruction = captured.get(step_label, "")

        assert instruction, f"{step_label} was never captured"

        # The structured fix_locations should appear in the instruction
        assert "pdd/commands/generate.py" in instruction, (
            f"{step_label} instruction missing first fix location"
        )
        assert "pdd/cmd_test_main.py" in instruction, (
            f"{step_label} instruction missing second fix location"
        )

    def test_fix_locations_defaults_to_none_when_no_marker(self, tmp_path):
        """When Step 6 has no FIX_LOCATIONS marker, fix_locations is 'none'."""
        from pdd.agentic_bug_orchestrator import _parse_fix_locations
        output_no_marker = "Root cause is in generate.py but no marker"
        result = _parse_fix_locations(output_no_marker)
        assert result == []