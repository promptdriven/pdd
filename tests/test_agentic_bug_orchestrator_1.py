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
    - Verify the 11-step sequential execution (including step 7).
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
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_wt, \
         patch("pdd.agentic_bug_orchestrator._get_modified_and_untracked") as mock_git_files, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda prompt, **kw: prompt) as mock_pp, \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)) as mock_load_state, \
         patch("pdd.agentic_bug_orchestrator._get_git_root") as mock_git_root, \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress") as mock_progress, \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress") as mock_clear_progress, \
         patch("pdd.agentic_bug_orchestrator.subprocess") as mock_subprocess:

        # Default behavior: return a template string that can be formatted
        mock_load.return_value = "Template for {issue_number}"
        # Default behavior: successful task
        mock_run.return_value = (True, "Default Output", 0.1, "gpt-4")
        # Default behavior: successful worktree
        mock_wt.return_value = (Path("/tmp/worktree"), None)
        # Default behavior: no modified/untracked files (avoids FileNotFoundError
        # from subprocess using mock worktree path as cwd)
        mock_git_files.return_value = []
        # Default behavior: git root returns tmp_path (set per-test if needed)
        mock_git_root.return_value = Path("/tmp")

        yield mock_load, mock_run, mock_wt

def test_orchestrator_full_success(mock_dependencies, tmp_path):
    """Tests a successful 12-step run with context accumulation (includes api_research and prompt_classification)."""
    mock_load, mock_run, mock_wt = mock_dependencies

    # Mock Step 7 (generate) to return files
    def side_effect(instruction, **kwargs):
        if "step9" in kwargs.get("label", ""):
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
    assert "test_file.py" in files
    assert mock_run.call_count == 12  # 12 steps
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
    assert "Stopped at step 1" in msg
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
    assert "Stopped at step 2" in msg
    assert "User Error" in msg
    assert mock_run.call_count == 2

def test_hard_stop_step7_no_files(mock_dependencies, tmp_path):
    """Tests early exit if Step 7 (generate) fails to generate files."""
    mock_load, mock_run, _ = mock_dependencies

    def side_effect(instruction, **kwargs):
        if "step9" in kwargs.get("label", ""):
            return (True, "I tried but found no files to create.", 0.1, "gpt-4")
        return (True, "Success", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is False
    assert "Stopped at step 9" in msg
    assert mock_run.call_count == 9  # Steps 1,2,3,4,5,5.5,6,7

def test_soft_failure_continuation(mock_dependencies, tmp_path):
    """Tests that the orchestrator continues on non-critical agent failures."""
    mock_load, mock_run, _ = mock_dependencies

    # Step 5 (reproduce) fails (success=False) but doesn't match a hard stop pattern
    def side_effect(instruction, **kwargs):
        if "step5" in kwargs.get("label"):
            return (False, "Random API Error", 0.0, "gpt-4")
        if "step9" in kwargs.get("label", ""):
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, "Success", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is True
    assert mock_run.call_count == 12  # 12 steps

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
    assert "worktree" in msg.lower()
    # Should stop before Step 5.5 runs (steps 1,2,3,4,5 = 5 steps)
    assert mock_run.call_count == 6

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
        if "step9" in label:
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
        if "step9" in kwargs.get("label", ""):
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


# ============================================================================
# Issue #928: Step 5 reproduction tests must flow into Step 9 via context
# ============================================================================


def test_step5_repro_content_passed_to_step9_context(mock_dependencies, tmp_path):
    """Verifies that when Step 5 emits REPRO_FILES_CREATED and the file exists
    on disk, its content is stored in context['step5_reproduction_tests'] and
    appears in Step 9's formatted prompt.

    Bug: The orchestrator has no handler for step_num == 5, so REPRO_FILES_CREATED
    output is never parsed and reproduction test content never reaches Step 9.
    """
    mock_load, mock_run, mock_wt = mock_dependencies

    # Create the reproduction test file that Step 5 would write in cwd
    repro_file = tmp_path / "tests" / "test_issue_123_reproduction.py"
    repro_file.parent.mkdir(parents=True, exist_ok=True)
    repro_file.write_text(
        "import pytest\n\ndef test_bug_exists():\n    assert 1 == 1  # proves bug\n"
    )

    captured_instructions = {}

    def run_side_effect(instruction, **kwargs):
        label = kwargs.get("label", "")
        captured_instructions[label] = instruction
        if label == "step5":
            return (True, "Reproduced.\nREPRO_FILES_CREATED: tests/test_issue_123_reproduction.py", 0.1, "gpt-4")
        if label == "step9":
            return (True, "FILES_CREATED: tests/test_issue_123_fix.py", 0.5, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = run_side_effect

    # Step 9 template must include {step5_reproduction_tests} placeholder
    def load_side_effect(name):
        if "step9" in name:
            return "Tests: {step5_reproduction_tests} Issue: {issue_number}"
        return "Template for {issue_number}"

    mock_load.side_effect = load_side_effect

    success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is True
    step9_instruction = captured_instructions.get("step9", "")
    assert step9_instruction, "Step 9 was never called"
    assert "test_bug_exists" in step9_instruction, (
        "Step 5's reproduction test content was not passed to Step 9 via "
        "context['step5_reproduction_tests'] — reproduction tests are lost (issue #928)"
    )


def test_step5_no_repro_marker_leaves_empty_context(mock_dependencies, tmp_path):
    """Verifies that when Step 5 output has no REPRO_FILES_CREATED marker,
    step5_reproduction_tests stays empty and Step 9 template resolves cleanly.

    This is the normal case when Step 5 could not reproduce the bug.
    """
    mock_load, mock_run, mock_wt = mock_dependencies

    captured_instructions = {}

    def run_side_effect(instruction, **kwargs):
        label = kwargs.get("label", "")
        captured_instructions[label] = instruction
        if label == "step5":
            return (True, "Could not reproduce the bug.", 0.1, "gpt-4")
        if label == "step9":
            return (True, "FILES_CREATED: tests/test_issue_123_fix.py", 0.5, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = run_side_effect

    def load_side_effect(name):
        if "step9" in name:
            return "Tests: {step5_reproduction_tests} Issue: {issue_number}"
        return "Template for {issue_number}"

    mock_load.side_effect = load_side_effect

    success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is True
    step9_instruction = captured_instructions.get("step9", "")
    assert step9_instruction, "Step 9 was never called"
    # The placeholder should resolve to empty string, not remain as literal
    assert "{step5_reproduction_tests}" not in step9_instruction, (
        "step5_reproduction_tests placeholder was not resolved in Step 9's prompt — "
        "the key is missing from the initial context dict (issue #928)"
    )


def test_step5_repro_file_missing_on_disk(mock_dependencies, tmp_path):
    """Verifies graceful handling when Step 5 emits REPRO_FILES_CREATED but
    the file doesn't actually exist on disk.

    The orchestrator should not crash — step5_reproduction_tests should
    remain empty.
    """
    mock_load, mock_run, mock_wt = mock_dependencies

    # Do NOT create the file on disk — simulate Step 5 claiming it wrote a file
    # that doesn't actually exist

    captured_instructions = {}

    def run_side_effect(instruction, **kwargs):
        label = kwargs.get("label", "")
        captured_instructions[label] = instruction
        if label == "step5":
            return (True, "REPRO_FILES_CREATED: tests/test_issue_123_reproduction.py", 0.1, "gpt-4")
        if label == "step9":
            return (True, "FILES_CREATED: tests/test_issue_123_fix.py", 0.5, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = run_side_effect

    def load_side_effect(name):
        if "step9" in name:
            return "Tests: {step5_reproduction_tests} Issue: {issue_number}"
        return "Template for {issue_number}"

    mock_load.side_effect = load_side_effect

    # Should not crash
    success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(
        issue_url="url", issue_content="content", repo_owner="owner",
        repo_name="name", issue_number=123, issue_author="author",
        issue_title="title", cwd=tmp_path, quiet=True
    )

    assert success is True
    step9_instruction = captured_instructions.get("step9", "")
    # File doesn't exist, so content should be empty (not crash)
    assert "test_issue_123_reproduction" not in step9_instruction, (
        "Nonexistent file path was somehow read and passed to Step 9"
    )


def test_step5_repro_content_re_extracted_on_resume(mock_dependencies, tmp_path):
    """Verifies that when resuming from saved state, Step 5's REPRO_FILES_CREATED
    output is re-parsed and the file content populates step5_reproduction_tests.

    Bug: The re-extraction block (lines 562-586) parses step5.5, step7, and step9
    outputs but skips step5_output entirely.
    """
    mock_load, mock_run, mock_wt = mock_dependencies

    # Create the reproduction test file in cwd (it persists across resume)
    repro_file = tmp_path / "tests" / "test_issue_456_reproduction.py"
    repro_file.parent.mkdir(parents=True, exist_ok=True)
    repro_file.write_text(
        "def test_resume_repro():\n    assert True  # proves bug on resume\n"
    )

    # Simulate a resume: load_workflow_state returns previous step outputs
    saved_state = {
        "step_outputs": {
            "1": "No duplicates",
            "2": "Not user error",
            "3": "Proceed",
            "4": "No API issues",
            "5": "Reproduced.\nREPRO_FILES_CREATED: tests/test_issue_456_reproduction.py",
            "6": "Root cause found",
            "7": "DEFECT_TYPE: code\nClassification done",
            "8": "Test plan ready",
            "9": "FILES_CREATED: tests/test_issue_456_fix.py",
        },
        "last_completed_step": 9,
        "total_cost": 1.0,
        "model_used": "gpt-4",
        "worktree_path": str(tmp_path),
    }

    captured_instructions = {}

    with patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(saved_state, None)):
        def run_side_effect(instruction, **kwargs):
            label = kwargs.get("label", "")
            captured_instructions[label] = instruction
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = run_side_effect

        def load_side_effect(name):
            if "step12" in name:
                return "Repro tests: {step5_reproduction_tests} Issue: {issue_number}"
            return "Template for {issue_number}"

        mock_load.side_effect = load_side_effect

        success, msg, cost, model, changed_files = run_agentic_bug_orchestrator(
            issue_url="url", issue_content="content", repo_owner="owner",
            repo_name="name", issue_number=456, issue_author="author",
            issue_title="title", cwd=tmp_path, quiet=True
        )

    # The re-extraction block should have read the file and populated context
    step12_instruction = captured_instructions.get("step12", "")
    assert "test_resume_repro" in step12_instruction, (
        "Step 5 REPRO_FILES_CREATED was not re-extracted on resume — "
        "reproduction test content is lost when the workflow resumes (issue #928)"
    )
