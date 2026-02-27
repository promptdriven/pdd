from __future__ import annotations

import pytest
from pathlib import Path
from unittest.mock import MagicMock, patch, call
from typing import List, Tuple

# Import the actual function from the module
from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

"""
Detailed Test Plan for agentic_bug_orchestrator

1. Functional Requirements Testing:
    - Verify the 11-step sequential execution (including step 5.5).
    - Verify context accumulation (step N output passed to step N+1).
    - Verify total cost accumulation across all steps.
    - Verify worktree creation before Step 7.
    - Verify file extraction from Step 7 output (FILES_CREATED/FILES_MODIFIED).

2. Hard Stop Condition Testing:
    - Step 1: "Duplicate of #" -> Stop.
    - Step 2: "Feature Request (Not a Bug)" or "User Error (Not a Bug)" -> Stop.
    - Step 3: "Needs More Info" -> Stop.
    - Step 7: No files generated -> Stop.
    - Step 8: "FAIL: Test does not work as expected" -> Stop.

3. Error Handling & Edge Cases:
    - Missing prompt templates (should return False).
    - Prompt formatting errors (missing keys).
    - Worktree creation failure (should return False).
    - run_agentic_task returning success=False but no hard stop (should continue).

4. Formal Verification vs. Unit Testing:
    - Sequential Logic & State Transitions: Unit tests are better for verifying the specific string-matching logic and the order of operations.
    - Context Accumulation: Unit tests with mocks can verify that the dictionary passed to the formatter grows correctly.
    - Cost Summation: Unit tests are sufficient.
    - Worktree Isolation: Unit tests with subprocess mocking are best to ensure the correct git commands are issued.
    - Z3 Formal Verification: Not strictly necessary for this orchestrator as there are no complex mathematical constraints or combinatorial logic; it's primarily a state-machine/workflow manager. However, we can use Z3-style logic to verify that "If a hard stop condition is met, no subsequent steps are called."

"""

@pytest.fixture
def mock_dependencies():
    with patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_wt:
        
        # Default behavior: return a template string that can be formatted
        mock_load.return_value = "Template for {issue_number}"
        # Default behavior: successful task
        mock_run.return_value = (True, "Default Output", 0.1, "gpt-4")
        # Default behavior: successful worktree
        mock_wt.return_value = (Path("/tmp/worktree"), None)
        
        yield mock_load, mock_run, mock_wt

def test_orchestrator_full_success(mock_dependencies, tmp_path):
    """Tests a successful 11-step run with context accumulation (includes step 5.5)."""
    mock_load, mock_run, mock_wt = mock_dependencies

    # Mock Step 7 to return files
    def side_effect(instruction, **kwargs):
        if "step7" in kwargs.get("label", ""):
            return (True, "FILES_CREATED: test_file.py", 0.5, "gpt-4")
        return (True, f"Output for {kwargs.get('label')}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is True
    assert "Investigation complete" in msg
    assert cost > 0
    assert files == ["test_file.py"]
    assert mock_run.call_count == 11  # 11 steps including step 5.5
    assert mock_wt.called

def test_hard_stop_step1_duplicate(mock_dependencies, tmp_path):
    """Tests early exit if Step 1 detects a duplicate."""
    mock_load, mock_run, _ = mock_dependencies
    
    mock_run.return_value = (True, "This is a Duplicate of #42", 0.1, "gpt-4")

    success, msg, cost, model, files = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is False
    assert "Stopped at Step 1" in msg
    assert mock_run.call_count == 1

def test_hard_stop_step2_user_error(mock_dependencies, tmp_path):
    """Tests early exit if Step 2 detects user error."""
    mock_load, mock_run, _ = mock_dependencies
    
    def side_effect(instruction, **kwargs):
        if "step1" in kwargs.get("label"):
            return (True, "Not a duplicate", 0.1, "gpt-4")
        return (True, "This is a User Error (Not a Bug)", 0.1, "gpt-4")
    
    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is False
    assert "Stopped at Step 2" in msg
    assert "User Error" in msg
    assert mock_run.call_count == 2

def test_hard_stop_step7_no_files(mock_dependencies, tmp_path):
    """Tests early exit if Step 7 fails to generate files."""
    mock_load, mock_run, _ = mock_dependencies

    def side_effect(instruction, **kwargs):
        if "step7" in kwargs.get("label"):
            return (True, "I tried but found no files to create.", 0.1, "gpt-4")
        return (True, "Success", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is False
    assert "Stopped at Step 7" in msg
    assert mock_run.call_count == 8  # Steps 1,2,3,4,5,5.5,6,7

def test_soft_failure_continuation(mock_dependencies, tmp_path):
    """Tests that the orchestrator continues on non-critical agent failures."""
    mock_load, mock_run, _ = mock_dependencies

    # Step 4 fails (success=False) but doesn't match a hard stop pattern
    def side_effect(instruction, **kwargs):
        if "step4" in kwargs.get("label"):
            return (False, "Random API Error", 0.0, "gpt-4")
        if "step7" in kwargs.get("label"):
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, "Success", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is True
    assert mock_run.call_count == 11  # 11 steps including step 5.5

def test_worktree_creation_failure(mock_dependencies, tmp_path):
    """Tests behavior when worktree setup fails."""
    mock_load, mock_run, mock_wt = mock_dependencies

    mock_wt.return_value = (None, "Git error")

    success, msg, _, _, _ = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is False
    assert "Failed to create worktree" in msg
    # Should stop before Step 5.5 runs (steps 1,2,3,4,5 = 5 steps)
    # Issue #352 moved worktree creation from before Step 7 to before Step 5.5
    assert mock_run.call_count == 5

def test_prompt_formatting_unknown_placeholder_left_intact(mock_dependencies, tmp_path):
    """Tests that unknown placeholders in prompt templates are left intact.

    Issue #549 fix: str.replace() substitution does not raise KeyError for
    unknown placeholders — they are left as-is in the formatted prompt.
    The orchestrator continues without error.
    """
    mock_load, mock_run, _ = mock_dependencies

    captured = {}

    def run_side_effect(**kwargs):
        label = kwargs.get("label", "")
        captured[label] = kwargs.get("instruction", "")
        if label == "step7":
            return (True, "FILES_CREATED: tests/test_foo.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = run_side_effect

    # Template has a placeholder not in context — with str.replace(), it stays as-is
    mock_load.return_value = "Hello {non_existent_key} and {issue_number}"

    run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    step1_instr = captured.get("step1", "")
    assert step1_instr, "step1 was not called"
    # Known placeholder substituted, unknown one left as-is
    assert "123" in step1_instr, "issue_number should be substituted"
    assert "{non_existent_key}" in step1_instr, (
        "Unknown placeholder should remain intact with str.replace() (Issue #549 fix)"
    )

def test_step_7_parsing_logic(mock_dependencies, tmp_path):
    """Verifies complex parsing of FILES_CREATED and FILES_MODIFIED."""
    mock_load, mock_run, _ = mock_dependencies
    
    output = (
        "Some reasoning here...\n"
        "FILES_CREATED: path/to/test1.py, path/to/test2.py\n"
        "FILES_MODIFIED: existing_file.py \n"
        "More text..."
    )
    
    def side_effect(instruction, **kwargs):
        if "step7" in kwargs.get("label"):
            return (True, output, 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")
    
    mock_run.side_effect = side_effect

    _, _, _, _, changed_files = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert "path/to/test1.py" in changed_files
    assert "path/to/test2.py" in changed_files
    assert "existing_file.py" in changed_files
    assert len(changed_files) == 3

def test_context_accumulation_verification(mock_dependencies, tmp_path):
    """Verifies that output from Step 1 is available in Step 2's prompt."""
    mock_load, mock_run, _ = mock_dependencies
    
    # We want to check if the prompt formatting uses the previous step's output
    # Since we mock load_prompt_template, we can return a template that uses step1_output
    def load_side_effect(name):
        if "step2" in name:
            return "Previous: {step1_output}"
        return "Step: {issue_number}"
    
    mock_load.side_effect = load_side_effect
    
    def run_side_effect(instruction, **kwargs):
        if "step1" in kwargs.get("label"):
            return (True, "STEP1_SECRET", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")
    
    mock_run.side_effect = run_side_effect

    run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    # Check the instruction passed to Step 2
    # Call 0 is step 1, Call 1 is step 2
    step2_call_args = mock_run.call_args_list[1]
    assert "Previous: STEP1_SECRET" in step2_call_args.kwargs["instruction"]