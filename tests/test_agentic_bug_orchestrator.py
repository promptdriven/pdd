"""
Test Plan for pdd.agentic_bug_orchestrator

1. **Happy Path Execution**:
   - Verify that the orchestrator runs through all 9 steps when no hard stops are triggered.
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
def mock_dependencies():
    """
    Mocks external dependencies:
    - run_agentic_task
    - load_prompt_template
    - console (to suppress output during tests)
    """
    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console") as mock_console:

        # Default behavior: successful run, generic output
        # Note: run_agentic_task returns 4 values: (success, output, cost, provider)
        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        # Default behavior: return a simple format string
        mock_load.return_value = "Prompt for {issue_number}"

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
    Test that all 9 steps execute successfully when no stop conditions are met.
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
    assert mock_run.call_count == 9
    # Use approx for floating point comparison
    assert cost == pytest.approx(0.9)
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
    assert "Issue is a duplicate" in msg
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
        (True, "Cannot proceed. Needs More Info from user.", 0.1, "model")
    ]
    
    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)
    
    assert success is False
    assert "Stopped at step 3" in msg
    assert "Needs more info" in msg
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
    assert "Stopped at step 7" in msg
    assert "No test file created or modified" in msg
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
    assert "Stopped at step 8" in msg
    assert "Test verification failed" in msg
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
    assert mock_run.call_count == 9


def test_template_loading_failure(mock_dependencies, default_args):
    """
    Test graceful exit if a prompt template cannot be loaded.
    """
    mock_run, mock_load, _ = mock_dependencies
    
    # Mock template loader to return None for step 1
    mock_load.return_value = None
    
    success, msg, _, _, _ = run_agentic_bug_orchestrator(**default_args)
    
    assert success is False
    assert "Failed to load prompt template" in msg
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
    assert "Template formatting error" in msg
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
    assert mock_run.call_count == 9