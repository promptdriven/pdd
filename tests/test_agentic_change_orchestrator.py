# TEST PLAN
#
# 1. Unit Tests (Pytest):
#    - test_orchestrator_happy_path: Verifies the complete 1-13 step flow with successful execution.
#      Checks that cost accumulates, files are parsed at step 9/10, and PR URL is extracted at step 13.
#    - test_orchestrator_hard_stop_early: Verifies that the orchestrator stops immediately if a hard stop
#      condition is met (e.g., "Duplicate of #" in Step 1).
#    - test_orchestrator_resume_from_state: Verifies that if a state file exists, previously completed
#      steps are skipped and execution resumes from the correct step.
#    - test_orchestrator_worktree_failure: Verifies behavior when git worktree setup fails (should return False).
#    - test_orchestrator_step9_failure_no_files: Verifies failure at Step 9 if no files are parsed from output.
#    - test_orchestrator_review_loop_logic: Verifies the interaction between Step 11 and 12.
#      Scenario: Step 11 finds issues -> Step 12 fixes -> Step 11 finds no issues -> Proceed.
#    - test_orchestrator_review_loop_max_iterations: Verifies that the loop breaks after MAX_REVIEW_ITERATIONS
#      even if issues persist.
#
# 2. Z3 Formal Verification:
#    - test_z3_review_loop_termination: Models the review loop logic (Steps 11-12) as a state machine
#      to formally prove that the loop is guaranteed to terminate either by finding no issues or hitting
#      the iteration limit.

import json
import os
import sys
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch, mock_open

import pytest
from z3 import Solver, Int, Bool, Implies, And, Or, Not, unsat

# Adjust import path to ensure we can import the module under test
from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator, _parse_changed_files

# -----------------------------------------------------------------------------
# Fixtures
# -----------------------------------------------------------------------------

@pytest.fixture
def temp_cwd(tmp_path):
    """Returns a temporary directory path to use as cwd."""
    return tmp_path

@pytest.fixture
def mock_dependencies(temp_cwd):
    """
    Mocks the external dependencies: run_agentic_task, load_prompt_template,
    load_workflow_state, save_workflow_state, clear_workflow_state,
    and subprocess (for git operations).
    """
    with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_template_loader, \
         patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_change_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_change_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_subprocess, \
         patch("pdd.agentic_change_orchestrator.console") as mock_console:
        
        # Default mock behaviors
        mock_run.return_value = (True, "Default Agent Output", 0.1, "gpt-4")
        
        mock_template = MagicMock()
        mock_template.format.return_value = "Formatted Prompt"
        mock_template_loader.return_value = mock_template
        
        # Default state: No existing state
        mock_load_state.return_value = (None, None)
        
        # Mock git rev-parse to return the temp_cwd as root
        # This ensures mkdir operations on the root succeed
        mock_subprocess.return_value.stdout = str(temp_cwd)
        mock_subprocess.return_value.returncode = 0
        
        yield {
            "run": mock_run,
            "template_loader": mock_template_loader,
            "load_state": mock_load_state,
            "save_state": mock_save_state,
            "clear_state": mock_clear_state,
            "subprocess": mock_subprocess,
            "console": mock_console
        }

# -----------------------------------------------------------------------------
# Unit Tests
# -----------------------------------------------------------------------------

def test_orchestrator_happy_path(mock_dependencies, temp_cwd):
    """
    Test the full successful execution of the orchestrator (Steps 1-13).
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    # Setup specific outputs for key steps
    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "Implementation done. FILES_MODIFIED: file_a.py, file_b.py", 0.5, "gpt-4")
        if label == "step10":
            return (True, "Architecture updated. ARCHITECTURE_FILES_MODIFIED: arch.json", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/123", 0.2, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="Fix bug",
        repo_owner="owner",
        repo_name="repo",
        issue_number=1,
        issue_author="me",
        issue_title="Bug fix",
        cwd=temp_cwd,
        verbose=True
    )

    assert success is True
    assert "PR Created: https://github.com/owner/repo/pull/123" in msg
    assert "file_a.py" in files
    assert "file_b.py" in files
    assert "arch.json" in files
    # Cost calculation: 
    # Steps 1-8 (8 * 0.1) + Step 9 (0.5) + Step 10 (0.1) + Step 11 (0.1) + Step 13 (0.2) 
    # = 0.8 + 0.5 + 0.1 + 0.1 + 0.2 = 1.7
    assert cost == pytest.approx(1.7)
    
    # Verify state was cleared
    mocks["clear_state"].assert_called_once()

def test_orchestrator_hard_stop_early(mock_dependencies, temp_cwd):
    """
    Test that the orchestrator stops immediately if a hard stop condition is met.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    # Step 1 returns "Duplicate of #"
    mock_run.return_value = (True, "This is a Duplicate of #42", 0.1, "gpt-4")

    success, msg, cost, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="Fix bug",
        repo_owner="owner",
        repo_name="repo",
        issue_number=2,
        issue_author="me",
        issue_title="Duplicate",
        cwd=temp_cwd
    )

    assert success is False
    assert "Stopped at step 1" in msg
    assert "Issue is a duplicate" in msg
    assert cost == 0.1
    
    # Verify state was saved but not cleared
    mocks["save_state"].assert_called()
    mocks["clear_state"].assert_not_called()

def test_orchestrator_resume_from_state(mock_dependencies, temp_cwd):
    """
    Test resumption from a saved state file.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_load_state = mocks["load_state"]

    # Simulate existing state
    initial_state = {
        "issue_number": 3,
        "last_completed_step": 4,
        "step_outputs": {
            "1": "out1", "2": "out2", "3": "out3", "4": "out4"
        },
        "total_cost": 1.0,
        "model_used": "gpt-3.5"
    }
    mock_load_state.return_value = (initial_state, 12345)

    # Mock subsequent steps
    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: new.py", 0.5, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, _, cost, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=3,
        issue_author="me",
        issue_title="Resume",
        cwd=temp_cwd
    )

    assert success is True
    # Verify steps 1-4 were NOT called
    labels_called = [call.kwargs.get('label') for call in mock_run.call_args_list]
    assert "step1" not in labels_called
    assert "step4" not in labels_called
    assert "step5" in labels_called

    # Initial cost 1.0 + steps 5,6,7,8 (0.4) + step 9 (0.5) + step 10 (0.1) + step 11 (0.1) + step 13 (0.1) = 2.2
    assert cost == pytest.approx(2.2)

def test_orchestrator_worktree_failure(mock_dependencies, temp_cwd):
    """
    Test failure when setting up the git worktree.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_subprocess = mocks["subprocess"]

    def side_effect_subprocess(args, **kwargs):
        # Simulate failure for worktree add
        if "worktree" in args and "add" in args:
            raise subprocess.CalledProcessError(1, args, stderr="Worktree creation failed")
        
        # Simulate success for rev-parse (returning temp_cwd as root)
        mock_ret = MagicMock()
        mock_ret.returncode = 0
        mock_ret.stdout = str(temp_cwd)
        return mock_ret

    mock_subprocess.side_effect = side_effect_subprocess

    # Mock steps 1-8 to pass
    mock_run.return_value = (True, "ok", 0.1, "gpt-4")

    success, msg, _, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=4,
        issue_author="me",
        issue_title="Worktree Fail",
        cwd=temp_cwd
    )

    assert success is False
    assert "Failed to create worktree" in msg

def test_orchestrator_step9_failure_no_files(mock_dependencies, temp_cwd):
    """
    Test failure at Step 9 if no files are detected in the output.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "I implemented it but forgot to list files.", 0.5, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, _, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=5,
        issue_author="me",
        issue_title="Step 9 Fail",
        cwd=temp_cwd
    )

    assert success is False
    assert "Stopped at step 9" in msg
    assert "no file changes" in msg

def test_orchestrator_step9_failure_preserves_completed_steps(mock_dependencies, temp_cwd):
    """
    Test that when step 9 fails, state correctly shows steps 6-8 as completed.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_load_state = mocks["load_state"]
    mock_save_state = mocks["save_state"]

    # Initial state: steps 1-5 completed
    initial_state = {
        "issue_number": 99,
        "last_completed_step": 5,
        "step_outputs": {"1": "o1", "2": "o2", "3": "o3", "4": "o4", "5": "o5"},
        "total_cost": 0.5,
        "model_used": "gpt-4"
    }
    mock_load_state.return_value = (initial_state, 123)

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            # Return output WITHOUT FILES markers - triggers failure
            return (True, "I did the work but no FILES_CREATED marker", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, _, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=99,
        issue_author="me",
        issue_title="State Bug",
        cwd=temp_cwd
    )

    assert success is False
    assert "step 9" in msg.lower()

    # Verify the last call to save_workflow_state had the correct state
    # We expect steps 6, 7, 8 to be completed
    assert mock_save_state.called
    final_call_args = mock_save_state.call_args
    saved_state = final_call_args[0][3] # state is the 4th arg
    
    assert saved_state["last_completed_step"] == 8
    assert "6" in saved_state["step_outputs"]
    assert "7" in saved_state["step_outputs"]
    assert "8" in saved_state["step_outputs"]

def test_orchestrator_review_loop_logic(mock_dependencies, temp_cwd):
    """
    Test the review loop: Step 11 finds issues -> Step 12 fixes -> Step 11 finds no issues.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    step11_calls = 0

    def side_effect_run(**kwargs):
        nonlocal step11_calls
        label = kwargs.get("label", "")

        if label == "step9":
            return (True, "FILES_MODIFIED: a.py", 0.1, "gpt-4")
        elif label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        elif label.startswith("step11"):
            step11_calls += 1
            if step11_calls == 1:
                return (True, "Issues Found: Bad style", 0.1, "gpt-4")
            else:
                return (True, "No Issues Found", 0.1, "gpt-4")
        elif label.startswith("step12"):
            return (True, "Fixed style", 0.1, "gpt-4")
        elif label == "step13":
            return (True, "PR Created", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, _, _, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=6,
        issue_author="me",
        issue_title="Review Loop",
        cwd=temp_cwd
    )

    assert success is True
    assert step11_calls == 2

    step12_calls = [call for call in mock_run.call_args_list if call.kwargs.get('label', '').startswith('step12')]
    assert len(step12_calls) == 1

def test_orchestrator_review_loop_max_iterations(mock_dependencies, temp_cwd):
    """
    Test that the review loop terminates after max iterations even if issues persist.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_MODIFIED: a.py", 0.1, "gpt-4")
        elif label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        elif label.startswith("step11"):
            return (True, "Issues Found: Still broken", 0.1, "gpt-4")
        elif label.startswith("step12"):
            return (True, "Attempted fix", 0.1, "gpt-4")
        elif label == "step13":
            return (True, "PR Created", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, _, _, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=7,
        issue_author="me",
        issue_title="Max Iterations",
        cwd=temp_cwd
    )

    assert success is True
    step11_calls = [call for call in mock_run.call_args_list if call.kwargs.get('label', '').startswith('step11')]
    assert len(step11_calls) == 5

    step12_calls = [call for call in mock_run.call_args_list if call.kwargs.get('label', '').startswith('step12')]
    assert len(step12_calls) == 5

# -----------------------------------------------------------------------------
# Step 7 Stop Condition Tests (TDD)
# -----------------------------------------------------------------------------

def test_step7_stop_with_stop_condition_marker(mock_dependencies, temp_cwd):
    """
    Test that Step 7 stops when explicit stop condition is present.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    def side_effect(**kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "Posted to GitHub.\nArchitectural Decision Needed", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="Feature request",
        repo_owner="owner",
        repo_name="repo",
        issue_number=777,
        issue_author="user",
        issue_title="Feature",
        cwd=temp_cwd
    )

    assert success is False, "Workflow should have stopped at step 7"
    assert "Stopped at step 7" in msg
    assert "Architectural decision needed" in msg


def test_step7_prompt_has_stop_condition_marker():
    """
    Verify Step 7 prompt documents the exact STOP_CONDITION marker.
    """
    prompt_path = Path(__file__).parent.parent / "prompts" / "agentic_change_step7_architecture_LLM.prompt"
    prompt_content = prompt_path.read_text()

    assert "% CRITICAL" in prompt_content, "Step 7 prompt missing CRITICAL section"
    assert "STOP_CONDITION: Architectural decision needed" in prompt_content

# -----------------------------------------------------------------------------
# Scope Enforcement Tests (TDD for PDD Methodology)
# -----------------------------------------------------------------------------

def test_step9_prompt_has_scope_critical_section():
    """
    Verify Step 9 prompt has CRITICAL scope section prominently placed.
    """
    prompt_path = Path(__file__).parent.parent / "prompts" / "agentic_change_step9_implement_LLM.prompt"
    prompt_content = prompt_path.read_text()

    assert "% CRITICAL: Scope" in prompt_content
    assert "FORBIDDEN" in prompt_content
    assert "Code files" in prompt_content or "code files" in prompt_content
    assert "Example files" in prompt_content or "example files" in prompt_content

def test_step8_prompt_has_scope_section():
    """
    Verify Step 8 prompt has scope constraints.
    """
    prompt_path = Path(__file__).parent.parent / "prompts" / "agentic_change_step8_analyze_LLM.prompt"
    prompt_content = prompt_path.read_text()

    assert "% Scope" in prompt_content
    assert "Do NOT" in prompt_content
    assert "Code files" in prompt_content or "code files" in prompt_content

def test_step6_prompt_clarifies_change_scope():
    """
    Verify Step 6 clarifies that pdd change only modifies prompts.
    """
    prompt_path = Path(__file__).parent.parent / "prompts" / "agentic_change_step6_devunits_LLM.prompt"
    prompt_content = prompt_path.read_text()

    assert "pdd change" in prompt_content and "ONLY" in prompt_content
    assert "GENERATED" in prompt_content

# -----------------------------------------------------------------------------
# Z3 Formal Verification
# -----------------------------------------------------------------------------

def test_z3_review_loop_termination():
    """
    Formally verify that the review loop logic terminates.
    """
    s = Solver()
    MAX_ITERATIONS = 5
    
    def get_state(k):
        iteration = Int(f"iter_{k}")
        terminated = Bool(f"term_{k}")
        issues_found = Bool(f"issues_{k}") 
        return iteration, terminated, issues_found

    iter_0, term_0, _ = get_state(0)
    s.add(iter_0 == 0)
    s.add(term_0 == False)
    
    for k in range(MAX_ITERATIONS):
        iter_k, term_k, issues_found_k = get_state(k)
        iter_next, term_next, _ = get_state(k + 1)
        
        new_iter = iter_k + 1
        
        transition = Implies(
            Not(term_k),
            And(
                iter_next == new_iter,
                term_next == Or(
                    Not(issues_found_k),
                    new_iter >= MAX_ITERATIONS
                )
            )
        )
        
        persist = Implies(
            term_k,
            And(iter_next == iter_k, term_next == True)
        )
        
        s.add(And(transition, persist))

    _, term_final, _ = get_state(MAX_ITERATIONS)
    s.add(Not(term_final))

    result = s.check()
    assert result == unsat

# -----------------------------------------------------------------------------
# Prompt Template Tests
# -----------------------------------------------------------------------------

def test_step9_prompt_template_includes_step5_output():
    """
    Verify Step 9 prompt template references step5_output.
    """
    prompt_path = Path(__file__).parent.parent / "prompts" / "agentic_change_step9_implement_LLM.prompt"
    template_content = prompt_path.read_text()
    assert "{step5_output}" in template_content

# -----------------------------------------------------------------------------
# Sync Order Context Tests (Requirement #11)
# -----------------------------------------------------------------------------

def test_sync_order_context_populated_before_step12(mock_dependencies, temp_cwd):
    """
    Test that sync_order_script and sync_order_list are added to context
    before Step 13 template formatting.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Step 9 reports modified prompt files
    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_MODIFIED: prompts/foo_python.prompt", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        return (True, "Default", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Capture context passed to template.format()
    last_context = {}
    def capture_format(**kwargs):
        last_context.clear()
        last_context.update(kwargs)
        return "Formatted"

    mock_template = MagicMock()
    mock_template.format.side_effect = capture_format
    mock_template_loader.return_value = mock_template

    # Create worktree directory with prompt files
    issue_number = 999
    worktree_path = temp_cwd / ".pdd" / "worktrees" / f"change-issue-{issue_number}"
    prompts_dir = worktree_path / "prompts"
    prompts_dir.mkdir(parents=True)
    (prompts_dir / "foo_python.prompt").write_text("% foo module")

    run_agentic_change_orchestrator(
        issue_url="http://test",
        issue_content="Test",
        repo_owner="o",
        repo_name="r",
        issue_number=issue_number,
        issue_author="a",
        issue_title="T",
        cwd=temp_cwd,
    )

    assert "sync_order_script" in last_context
    assert "sync_order_list" in last_context

def test_sync_order_defaults_when_no_prompts_modified(mock_dependencies, temp_cwd):
    """
    Test sync_order has default values when no prompt files are modified.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Step 9 reports only non-prompt files
    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_MODIFIED: src/main.py", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        return (True, "Default", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    last_context = {}
    def capture_format(**kwargs):
        last_context.clear()
        last_context.update(kwargs)
        return "Formatted"

    mock_template = MagicMock()
    mock_template.format.side_effect = capture_format
    mock_template_loader.return_value = mock_template

    run_agentic_change_orchestrator(
        issue_url="http://test",
        issue_content="Test",
        repo_owner="o",
        repo_name="r",
        issue_number=888,
        issue_author="a",
        issue_title="T",
        cwd=temp_cwd,
    )

    assert last_context.get("sync_order_script") == ""
    assert last_context.get("sync_order_list") == "No modules to sync"

def test_worktree_path_in_context_when_resuming(mock_dependencies, temp_cwd):
    """
    Test that worktree_path is added to context when resuming after Step 9.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_load_state = mocks["load_state"]
    mock_template_loader = mocks["template_loader"]

    worktree_path = temp_cwd / ".pdd" / "worktrees" / "change-issue-777"
    worktree_path.mkdir(parents=True)

    initial_state = {
        "issue_number": 777,
        "last_completed_step": 9,
        "step_outputs": {str(i): f"out{i}" for i in range(1, 10)},
        "total_cost": 1.0,
        "model_used": "gpt-4",
        "worktree_path": str(worktree_path),
        "review_iteration": 0,
        "previous_fixes": "",
    }
    mock_load_state.return_value = (initial_state, 123)

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        return (True, "Default", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    last_context = {}
    def capture_format(**kwargs):
        last_context.clear()
        last_context.update(kwargs)
        return "Formatted"

    mock_template = MagicMock()
    mock_template.format.side_effect = capture_format
    mock_template_loader.return_value = mock_template

    run_agentic_change_orchestrator(
        issue_url="http://test",
        issue_content="Test",
        repo_owner="o",
        repo_name="r",
        issue_number=777,
        issue_author="a",
        issue_title="T",
        cwd=temp_cwd,
    )

    assert "worktree_path" in last_context
    assert last_context["worktree_path"] == str(worktree_path)

def test_parse_changed_files_strips_markdown_formatting():
    """
    Test that _parse_changed_files strips markdown bold formatting from paths.
    """
    output = """
    FILES_MODIFIED: ** prompts/foo_python.prompt, docs/README.md, **prompts/bar_LLM.prompt**
    FILES_CREATED: **prompts/new_python.prompt**
    """
    files = _parse_changed_files(output)
    assert "prompts/foo_python.prompt" in files
    assert "prompts/bar_LLM.prompt" in files
    assert "prompts/new_python.prompt" in files
    assert "docs/README.md" in files
    for f in files:
        assert "**" not in f
        assert not f.startswith("*")
    prompt_files = [f for f in files if f.startswith("prompts/") and f.endswith(".prompt")]
    assert len(prompt_files) == 3

@pytest.fixture
def mock_dependencies_dict():
    with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_load, \
         patch("pdd.agentic_change_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_change_orchestrator.clear_workflow_state") as mock_clear, \
         patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_template, \
         patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_subprocess, \
         patch("pdd.agentic_change_orchestrator.build_dependency_graph") as mock_build_graph, \
         patch("pdd.agentic_change_orchestrator.topological_sort") as mock_topo_sort, \
         patch("pdd.agentic_change_orchestrator.get_affected_modules") as mock_get_affected, \
         patch("pdd.agentic_change_orchestrator.generate_sync_order_script") as mock_gen_script, \
         patch("pdd.agentic_change_orchestrator.extract_module_from_include") as mock_extract_mod:
        
        mock_load.return_value = (None, None)
        mock_save.return_value = 12345
        mock_template.return_value = MagicMock(format=lambda **kwargs: "Formatted Prompt")
        # Mock subprocess to return a valid path for git root
        mock_subprocess.return_value.stdout = "/tmp/git/root"
        mock_subprocess.return_value.returncode = 0
        mock_topo_sort.return_value = ([], [])
        mock_get_affected.return_value = []
        
        yield {
            "run": mock_run,
            "load": mock_load,
            "save": mock_save,
            "clear": mock_clear,
            "template": mock_template,
            "subprocess": mock_subprocess,
            "build_graph": mock_build_graph,
            "topo_sort": mock_topo_sort,
            "get_affected": mock_get_affected,
            "gen_script": mock_gen_script,
            "extract_mod": mock_extract_mod
        }

def test_happy_path_full_execution(mock_dependencies_dict, tmp_path):
    mocks = mock_dependencies_dict
    def side_effect_run(instruction, **kwargs):
        label = kwargs.get('label', '')
        if "step9" in label: return True, "FILES_CREATED: test.py", 0.1, "gpt-4"
        if "step10" in label: return True, "Arch updated", 0.1, "gpt-4"
        if "step11" in label: return True, "No Issues Found", 0.1, "gpt-4"
        if "step13" in label: return True, "PR Created: https://github.com/owner/repo/pull/1", 0.1, "gpt-4"
        return True, f"Output for {label}", 0.1, "gpt-4"
    mocks["run"].side_effect = side_effect_run
    mocks["subprocess"].return_value.stdout = str(tmp_path)
    success, msg, cost, model, files = run_agentic_change_orchestrator(issue_url="http://issue", issue_content="Fix bug", repo_owner="owner", repo_name="repo", issue_number=1, issue_author="me", issue_title="Bug Fix", cwd=tmp_path, quiet=True)
    assert success is True
    assert "PR Created" in msg
    assert files == ["test.py"]
    assert mocks["run"].call_count >= 12
    worktree_calls = [c for c in mocks["subprocess"].call_args_list if "worktree" in c[0][0] and "add" in c[0][0]]
    assert len(worktree_calls) == 1
    mocks["clear"].assert_called_once()

def test_hard_stop_duplicate_dict(mock_dependencies_dict, tmp_path):
    mocks = mock_dependencies_dict
    mocks["run"].return_value = (True, "Duplicate of #999", 0.1, "gpt-4")
    success, msg, cost, model, files = run_agentic_change_orchestrator(issue_url="http://issue", issue_content="Fix bug", repo_owner="owner", repo_name="repo", issue_number=1, issue_author="me", issue_title="Bug Fix", cwd=tmp_path, quiet=True)
    assert success is False
    assert "Stopped at step 1" in msg
    assert "Issue is a duplicate" in msg
    mocks["save"].assert_called()
    mocks["clear"].assert_not_called()
    assert mocks["run"].call_count == 1

def test_resumption_from_state_dict(mock_dependencies_dict, tmp_path):
    mocks = mock_dependencies_dict
    existing_state = {"last_completed_step": 4, "step_outputs": {"1": "out1", "2": "out2", "3": "out3", "4": "out4"}, "total_cost": 0.5, "model_used": "gpt-4", "worktree_path": str(tmp_path / ".pdd" / "worktrees" / "change-issue-1")}
    mocks["load"].return_value = (existing_state, 123)
    def side_effect_run(instruction, **kwargs):
        label = kwargs.get('label', '')
        if "step9" in label: return True, "FILES_MODIFIED: mod.py", 0.1, "gpt-4"
        if "step10" in label: return True, "Arch updated", 0.1, "gpt-4"
        if "step11" in label: return True, "No Issues Found", 0.1, "gpt-4"
        return True, "ok", 0.1, "gpt-4"
    mocks["run"].side_effect = side_effect_run
    
    # Ensure git root is mocked to tmp_path so mkdir works
    mocks["subprocess"].return_value.stdout = str(tmp_path)
    
    success, msg, cost, model, files = run_agentic_change_orchestrator(issue_url="http://issue", issue_content="Fix bug", repo_owner="owner", repo_name="repo", issue_number=1, issue_author="me", issue_title="Bug Fix", cwd=tmp_path, quiet=True)
    assert success is True
    labels = [c.kwargs.get('label') for c in mocks["run"].call_args_list]
    assert "step1" not in labels
    assert "step4" not in labels
    assert "step5" in labels

def test_review_loop_logic_dict(mock_dependencies_dict, tmp_path):
    mocks = mock_dependencies_dict
    existing_state = {"last_completed_step": 10, "step_outputs": {str(i): "out" for i in range(1, 11)}, "worktree_path": str(tmp_path / "wt")}
    existing_state["step_outputs"]["9"] = "FILES_CREATED: foo.py"
    mocks["load"].return_value = (existing_state, 123)
    responses = [(True, "Issues found: syntax error", 0.1, "gpt-4"), (True, "Fixed syntax error", 0.1, "gpt-4"), (True, "No Issues Found", 0.1, "gpt-4"), (True, "PR Created", 0.1, "gpt-4")]
    mocks["run"].side_effect = responses
    with patch("pathlib.Path.exists", return_value=True):
        success, msg, cost, model, files = run_agentic_change_orchestrator(issue_url="http://issue", issue_content="Fix bug", repo_owner="owner", repo_name="repo", issue_number=1, issue_author="me", issue_title="Bug Fix", cwd=tmp_path, quiet=True)
    assert success is True
    assert mocks["run"].call_count == 4
    labels = [c.kwargs.get('label') for c in mocks["run"].call_args_list]
    assert "step11_iter1" in labels
    assert "step12_iter1" in labels
    assert "step11_iter2" in labels
    assert "step13" in labels

def test_worktree_creation_failure_dict(mock_dependencies_dict, tmp_path):
    mocks = mock_dependencies_dict
    def side_effect_subprocess(cmd, **kwargs):
        cmd_str = " ".join(cmd) if isinstance(cmd, list) else cmd
        if "worktree" in cmd_str and "add" in cmd_str: raise subprocess.CalledProcessError(1, cmd)
        m = MagicMock(); m.stdout = str(tmp_path); m.returncode = 0; return m
    mocks["subprocess"].side_effect = side_effect_subprocess
    existing_state = {"last_completed_step": 8, "step_outputs": {str(i): "out" for i in range(1, 9)}}
    mocks["load"].return_value = (existing_state, 123)
    success, msg, cost, model, files = run_agentic_change_orchestrator(issue_url="http://issue", issue_content="Fix bug", repo_owner="owner", repo_name="repo", issue_number=1, issue_author="me", issue_title="Bug Fix", cwd=tmp_path, quiet=True)
    assert success is False
    assert "Failed to restore worktree" in msg

def test_file_parsing_step9_and_10_dict(mock_dependencies_dict, tmp_path):
    mocks = mock_dependencies_dict
    existing_state = {"last_completed_step": 8, "step_outputs": {str(i): "out" for i in range(1, 9)}}
    mocks["load"].return_value = (existing_state, 123)
    def side_effect_run(instruction, **kwargs):
        label = kwargs.get('label', '')
        if "step9" in label: return True, "FILES_CREATED: new.py\nFILES_MODIFIED: existing.py", 0.1, "gpt-4"
        if "step10" in label: return True, "ARCHITECTURE_FILES_MODIFIED: arch.json", 0.1, "gpt-4"
        if "step11" in label: return True, "No Issues Found", 0.1, "gpt-4"
        return True, "ok", 0.1, "gpt-4"
    mocks["run"].side_effect = side_effect_run
    mocks["subprocess"].return_value.stdout = str(tmp_path)
    success, msg, cost, model, files = run_agentic_change_orchestrator(issue_url="http://issue", issue_content="Fix bug", repo_owner="owner", repo_name="repo", issue_number=1, issue_author="me", issue_title="Bug Fix", cwd=tmp_path, quiet=True)
    assert success is True
    assert "new.py" in files
    assert "existing.py" in files
    assert "arch.json" in files
    assert len(files) == 3

def test_sync_order_generation_dict(mock_dependencies_dict, tmp_path):
    mocks = mock_dependencies_dict
    existing_state = {"last_completed_step": 12, "step_outputs": {str(i): "out" for i in range(1, 13)}, "worktree_path": str(tmp_path / "wt")}
    existing_state["step_outputs"]["9"] = "FILES_MODIFIED: prompts/foo.prompt"
    mocks["load"].return_value = (existing_state, 123)
    mocks["extract_mod"].return_value = "foo"
    mocks["get_affected"].return_value = ["foo", "bar"]
    mocks["gen_script"].return_value = "echo sync"
    mocks["run"].return_value = (True, "PR Created", 0.1, "gpt-4")
    with patch("pathlib.Path.exists", return_value=True):
        run_agentic_change_orchestrator(issue_url="http://issue", issue_content="Fix bug", repo_owner="owner", repo_name="repo", issue_number=1, issue_author="me", issue_title="Bug Fix", cwd=tmp_path, quiet=True)
    mocks["extract_mod"].assert_called()
    mocks["build_graph"].assert_called()
    mocks["get_affected"].assert_called()
    mocks["gen_script"].assert_called()