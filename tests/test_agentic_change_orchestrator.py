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
from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator, _parse_changed_files, _detect_worktree_changes, _parse_direct_edit_candidates

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


def test_sync_order_script_written_to_cwd(mock_dependencies, temp_cwd):
    """
    After generating sync order, a sync_order.sh should be written to the
    user's original CWD (not just the worktree temp directory).
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    issue_number = 555
    worktree_path = temp_cwd / ".pdd" / "worktrees" / f"change-issue-{issue_number}"

    # Step 9 reports modified prompt files
    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_MODIFIED: prompts/foo_python.prompt", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "Default", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    mock_template = MagicMock()
    mock_template.format.return_value = "Formatted"
    mock_template_loader.return_value = mock_template

    # Patch _setup_worktree to return our worktree path and create prompt files
    # after the mock setup (avoiding the rmtree in real _setup_worktree)
    def mock_setup_worktree(cwd, issue_num, quiet):
        prompts_dir = worktree_path / "prompts"
        prompts_dir.mkdir(parents=True, exist_ok=True)
        (prompts_dir / "foo_python.prompt").write_text(
            "<include>prompts/bar_python.prompt</include>", encoding="utf-8"
        )
        (prompts_dir / "bar_python.prompt").write_text("% bar module", encoding="utf-8")
        return worktree_path, None

    with patch("pdd.agentic_change_orchestrator._setup_worktree", side_effect=mock_setup_worktree):
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

    # sync_order.sh should exist in the user's CWD
    user_script = temp_cwd / "sync_order.sh"
    assert user_script.exists(), "sync_order.sh not written to user's CWD"
    content = user_script.read_text()
    assert "pdd sync" in content
    # Should NOT contain absolute temp directory paths
    assert "/var/folders" not in content
    assert ".pdd/worktrees" not in content


def test_sync_order_list_context_is_clean_commands(mock_dependencies, temp_cwd):
    """
    context['sync_order_list'] should contain clean 'pdd sync X' commands,
    not the full bash script with shebang/comments/set -e.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

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

    last_context = {}
    def capture_format(**kwargs):
        last_context.clear()
        last_context.update(kwargs)
        return "Formatted"

    mock_template = MagicMock()
    mock_template.format.side_effect = capture_format
    mock_template_loader.return_value = mock_template

    issue_number = 556
    worktree_path = temp_cwd / ".pdd" / "worktrees" / f"change-issue-{issue_number}"
    prompts_dir = worktree_path / "prompts"
    prompts_dir.mkdir(parents=True)
    (prompts_dir / "foo_python.prompt").write_text("% foo", encoding="utf-8")

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

    sync_list = last_context.get("sync_order_list", "")
    if sync_list and sync_list != "No modules to sync":
        # Should be clean commands, not a full bash script
        assert not sync_list.startswith("#!/bin/bash"), "sync_order_list should not contain shebang"
        assert "set -e" not in sync_list, "sync_order_list should not contain set -e"
        assert "pdd sync" in sync_list


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

def test_parse_direct_edit_candidates():
    """
    Test that _parse_direct_edit_candidates extracts file paths from the Direct Edit Candidates table.
    """
    # Test case 1: Standard table format
    output = """
## Step 6: Dev Units Identified

### Direct Edit Candidates (No Prompt)
| File | Edit Type | Markers Found |
|------|-----------|---------------|
| `frontend/src/components/billing/AutoBuySettings.tsx` | uncomment | TODO marker at line 203 |
| `frontend/src/pages/Settings.tsx` | remove placeholder | "coming soon" text |

### Files Explored
- prompts/
"""
    candidates = _parse_direct_edit_candidates(output)
    assert len(candidates) == 2
    assert "frontend/src/components/billing/AutoBuySettings.tsx" in candidates
    assert "frontend/src/pages/Settings.tsx" in candidates

    # Test case 2: No table present
    output_no_table = """
## Step 6: Dev Units Identified

### Dev Units to MODIFY
| Prompt | Code |
|--------|------|
| prompts/foo.prompt | src/foo.py |
"""
    candidates_empty = _parse_direct_edit_candidates(output_no_table)
    assert len(candidates_empty) == 0

    # Test case 3: Table with varying formatting
    output_varied = """
### Direct Edit Candidates
| File | Edit Type | Markers Found |
|------|-----------|---------------|
| frontend/src/App.tsx | uncomment | TODO |
"""
    candidates_varied = _parse_direct_edit_candidates(output_varied)
    assert len(candidates_varied) == 1
    assert "frontend/src/App.tsx" in candidates_varied

def test_parse_changed_files_includes_direct_edits():
    """
    Test that _parse_changed_files also extracts files from DIRECT_EDITS line.
    """
    output = """
FILES_MODIFIED: prompts/foo_python.prompt
FILES_CREATED: prompts/bar_python.prompt
DIRECT_EDITS: frontend/src/components/Settings.tsx, frontend/src/App.tsx
"""
    files = _parse_changed_files(output)
    assert "prompts/foo_python.prompt" in files
    assert "prompts/bar_python.prompt" in files
    assert "frontend/src/components/Settings.tsx" in files
    assert "frontend/src/App.tsx" in files

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
         patch("pdd.agentic_change_orchestrator.generate_sync_order_script") as mock_gen_script:
        
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
            "gen_script": mock_gen_script
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
    
    # Create real directories so .exists() checks pass
    worktree_dir = tmp_path / "wt"
    prompts_dir = worktree_dir / "prompts"
    prompts_dir.mkdir(parents=True)
    
    # Create the prompt file matching the pattern that works in other tests
    (prompts_dir / "foo_python.prompt").write_text("% foo module")

    existing_state = {
        "last_completed_step": 12, 
        "step_outputs": {str(i): "out" for i in range(1, 13)}, 
        "worktree_path": str(worktree_dir)
    }
    # Update state to reference the file we created
    existing_state["step_outputs"]["9"] = "FILES_MODIFIED: prompts/foo_python.prompt"
    mocks["load"].return_value = (existing_state, 123)
    
    mocks["get_affected"].return_value = ["foo", "bar"]
    mocks["gen_script"].return_value = "echo sync"
    mocks["run"].return_value = (True, "PR Created", 0.1, "gpt-4")
    
    run_agentic_change_orchestrator(
        issue_url="http://issue", issue_content="Fix bug", repo_owner="owner", 
        repo_name="repo", issue_number=1, issue_author="me", issue_title="Bug Fix", 
        cwd=tmp_path, quiet=True
    )
    
    mocks["build_graph"].assert_called()
    mocks["get_affected"].assert_called()
    mocks["gen_script"].assert_called()


def test_sync_order_sh_included_in_changed_files(mock_dependencies_dict, tmp_path):
    """sync_order.sh must appear in changed_files when sync order is generated."""
    mocks = mock_dependencies_dict

    worktree_dir = tmp_path / "wt"
    prompts_dir = worktree_dir / "prompts"
    prompts_dir.mkdir(parents=True)
    (prompts_dir / "foo_python.prompt").write_text("% foo module")

    existing_state = {
        "last_completed_step": 12,
        "step_outputs": {str(i): "out" for i in range(1, 13)},
        "worktree_path": str(worktree_dir)
    }
    existing_state["step_outputs"]["9"] = "FILES_MODIFIED: prompts/foo_python.prompt"
    mocks["load"].return_value = (existing_state, 123)

    mocks["get_affected"].return_value = ["foo", "bar"]
    mocks["gen_script"].return_value = "echo sync"
    mocks["run"].return_value = (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://issue", issue_content="Fix", repo_owner="o",
        repo_name="r", issue_number=1, issue_author="me",
        issue_title="Fix", cwd=tmp_path, quiet=True
    )

    assert "sync_order.sh" in files


# -----------------------------------------------------------------------------
# .pddrc Context Key Tests (TDD for Issue #221 bug fix)
# -----------------------------------------------------------------------------

def test_orchestrator_populates_pddrc_context_keys_before_step6(mock_dependencies, temp_cwd):
    """
    Context must include language, source_dir, test_dir, example_dir, ext, lang from .pddrc.

    This test verifies that the orchestrator loads .pddrc configuration from the
    target repo and populates context keys required by step 6's prompt template:
    - language: default programming language (e.g., "python")
    - source_dir: where source code lives (e.g., "pdd/")
    - test_dir: where tests live (e.g., "tests/")
    - example_dir: where examples live (e.g., "context/")
    - ext: file extension (e.g., "py")
    - lang: language suffix (e.g., "_python")

    Without these, step 6 template.format() raises KeyError.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Create a .pddrc file in the temp directory
    pddrc_content = (
        "contexts:\n"
        "  default:\n"
        "    defaults:\n"
        "      default_language: python\n"
        "      generate_output_path: src/\n"
        "      test_output_path: tests/\n"
        "      example_output_path: examples/\n"
    )
    pddrc_path = temp_cwd / ".pddrc"
    pddrc_path.write_text(pddrc_content)

    # Track what context is passed to template.format()
    captured_contexts = []
    def capture_format(**kwargs):
        captured_contexts.append(kwargs.copy())
        return "Formatted Prompt"

    mock_template = MagicMock()
    mock_template.format.side_effect = capture_format
    mock_template_loader.return_value = mock_template

    # Run through step 6
    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step6":
            return (True, "Found 3 dev units", 0.1, "gpt-4")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/1", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Mock the config loading functions to ensure deterministic behavior
    with patch("pdd.agentic_change_orchestrator._find_pddrc_file") as mock_find, \
         patch("pdd.agentic_change_orchestrator._load_pddrc_config") as mock_load_config, \
         patch("pdd.agentic_change_orchestrator._detect_context") as mock_detect:
        
        mock_find.return_value = Path("/path/to/.pddrc")
        mock_load_config.return_value = {
            "contexts": {
                "default": {
                    "defaults": {
                        "default_language": "python",
                        "generate_output_path": "src/",
                        "test_output_path": "tests/",
                        "example_output_path": "examples/"
                    }
                }
            }
        }
        mock_detect.return_value = "default"

        success, msg, cost, model, files = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="Add new feature",
            repo_owner="owner",
            repo_name="repo",
            issue_number=221,
            issue_author="me",
            issue_title="New Feature",
            cwd=temp_cwd,
            quiet=True
        )

    # Find the context used for step 6 (6th template.format call, 0-indexed = 5)
    assert len(captured_contexts) >= 6, f"Expected at least 6 template formats, got {len(captured_contexts)}"
    step6_context = captured_contexts[5]  # Step 6 is the 6th step

    # Verify required .pddrc-derived context keys are present
    assert "language" in step6_context, "Context missing 'language' from .pddrc"
    assert "source_dir" in step6_context, "Context missing 'source_dir' from .pddrc"
    assert "test_dir" in step6_context, "Context missing 'test_dir' from .pddrc"
    assert "example_dir" in step6_context, "Context missing 'example_dir' from .pddrc"
    assert "ext" in step6_context, "Context missing 'ext' derived from language"
    assert "lang" in step6_context, "Context missing 'lang' suffix derived from language"

    # Verify values match .pddrc
    assert step6_context["language"] == "python"
    assert step6_context["source_dir"] == "src/"
    assert step6_context["test_dir"] == "tests/"
    assert step6_context["example_dir"] == "examples/"
    assert step6_context["ext"] == "py"
    assert step6_context["lang"] == "_python"


def test_orchestrator_uses_defaults_when_no_pddrc(mock_dependencies, temp_cwd):
    """
    When no .pddrc exists, orchestrator should use sensible defaults for context keys.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # No .pddrc file - temp_cwd is empty

    captured_contexts = []
    def capture_format(**kwargs):
        captured_contexts.append(kwargs.copy())
        return "Formatted Prompt"

    mock_template = MagicMock()
    mock_template.format.side_effect = capture_format
    mock_template_loader.return_value = mock_template

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="Add feature",
        repo_owner="owner",
        repo_name="repo",
        issue_number=222,
        issue_author="me",
        issue_title="Feature",
        cwd=temp_cwd,
        quiet=True
    )

    # Even without .pddrc, context keys should have defaults
    assert len(captured_contexts) >= 6
    step6_context = captured_contexts[5]

    # Should have defaults (actual values may vary based on implementation)
    assert "language" in step6_context, "Context missing 'language' default"
    assert "source_dir" in step6_context, "Context missing 'source_dir' default"
    assert "test_dir" in step6_context, "Context missing 'test_dir' default"
    assert "example_dir" in step6_context, "Context missing 'example_dir' default"
    assert "ext" in step6_context, "Context missing 'ext' default"
    assert "lang" in step6_context, "Context missing 'lang' default"

"""
Test plan for agentic_change_orchestrator.py

1. Unit Tests:
    - test_happy_path_full_run: Mock all steps succeeding, verify final success tuple.
    - test_resumption_from_state: Mock state existing at step 4, verify steps 1-4 skipped.
    - test_hard_stop_duplicate: Mock step 1 returning "Duplicate of #123", verify early exit.
    - test_hard_stop_implementation_fail: Mock step 9 returning "FAIL:", verify early exit.
    - test_review_loop_logic: Mock step 11 finding issues twice then passing, verify iteration count.
    - test_worktree_creation_failure: Mock git failure, verify graceful exit.
    - test_file_parsing_step_9_10: Verify context accumulation of changed files.

2. Z3 Formal Verification:
    - test_z3_stop_conditions: Verify the logic mapping (step_num, output) -> action (stop/continue).
"""

import sys
import pytest
from unittest.mock import MagicMock, patch, ANY
from pathlib import Path
import z3

# Import the module under test
# Adjust path if necessary based on where this test file is located relative to the source
try:
    from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
except ImportError:
    # Fallback for environment where package structure might differ
    run_agentic_change_orchestrator = MagicMock()

# Mock constants for testing
MOCK_ISSUE_URL = "https://github.com/owner/repo/issues/1"
MOCK_ISSUE_CONTENT = "Fix the bug"
MOCK_REPO_OWNER = "owner"
MOCK_REPO_NAME = "repo"
MOCK_ISSUE_NUMBER = 1
MOCK_ISSUE_AUTHOR = "user"
MOCK_ISSUE_TITLE = "Bug fix"

@pytest.fixture
def mock_dependencies_v2():
    """Mock external dependencies to isolate the orchestrator logic."""
    with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_load, \
         patch("pdd.agentic_change_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_change_orchestrator.clear_workflow_state") as mock_clear, \
         patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_template, \
         patch("pdd.agentic_change_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_subprocess, \
         patch("pdd.agentic_change_orchestrator.build_dependency_graph") as mock_build_graph, \
         patch("pdd.agentic_change_orchestrator.topological_sort") as mock_topo_sort, \
         patch("pdd.agentic_change_orchestrator.get_affected_modules") as mock_affected, \
         patch("pdd.agentic_change_orchestrator.generate_sync_order_script") as mock_gen_script:
        
        # Default behaviors
        mock_load.return_value = (None, None) # No existing state
        mock_save.return_value = 12345 # Mock comment ID
        mock_template.return_value = MagicMock(format=lambda **kwargs: "Formatted Prompt")
        mock_worktree.return_value = (Path("/tmp/worktree"), None)
        
        # Default run_agentic_task behavior: success
        # Returns (success, output, cost, model)
        mock_run.return_value = (True, "Step Output", 0.1, "gpt-4")
        
        yield {
            "run": mock_run,
            "load": mock_load,
            "save": mock_save,
            "clear": mock_clear,
            "template": mock_template,
            "worktree": mock_worktree,
            "subprocess": mock_subprocess,
            "build_graph": mock_build_graph
        }

def test_happy_path_full_run(mock_dependencies_v2, tmp_path):
    """Test a complete run from step 1 to 13 with no issues."""
    mocks = mock_dependencies_v2
    
    # Setup specific step outputs
    def side_effect_run(instruction, **kwargs):
        label = kwargs.get("label", "")
        if "step9" in label:
            return (True, "FILES_CREATED: file1.py, file2.py", 0.5, "gpt-4")
        if "step11" in label:
            return (True, "No Issues Found", 0.1, "gpt-4")
        if "step13" in label:
            return (True, "PR Created: https://github.com/owner/repo/pull/2", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")
    
    mocks["run"].side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        MOCK_ISSUE_URL, MOCK_ISSUE_CONTENT, MOCK_REPO_OWNER, MOCK_REPO_NAME, 
        MOCK_ISSUE_NUMBER, MOCK_ISSUE_AUTHOR, MOCK_ISSUE_TITLE, cwd=tmp_path
    )

    assert success is True
    assert "PR Created" in msg
    assert "file1.py" in files
    assert "file2.py" in files
    
    # Verify step 13 was called (PR creation)
    # Steps 1-10, 11, 13 = 12 calls (Step 12 skipped)
    assert mocks["run"].call_count >= 12
    # Verify state was cleared at the end
    mocks["clear"].assert_called_once()

def test_resumption_from_state(mock_dependencies_v2, tmp_path):
    """Test resuming from a saved state (e.g., step 4 completed)."""
    mocks = mock_dependencies_v2
    
    # Mock existing state
    existing_state = {
        "last_completed_step": 4,
        "step_outputs": {
            "1": "out1", "2": "out2", "3": "out3", "4": "out4"
        },
        "total_cost": 1.0,
        "model_used": "gpt-4"
    }
    mocks["load"].return_value = (existing_state, 999)

    # Setup run side effect for remaining steps
    def side_effect_run(instruction, **kwargs):
        label = kwargs.get("label", "")
        if "step9" in label:
            return (True, "FILES_MODIFIED: file1.py", 0.5, "gpt-4")
        if "step11" in label:
            return (True, "No Issues Found", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")
    mocks["run"].side_effect = side_effect_run

    success, _, cost, _, _ = run_agentic_change_orchestrator(
        MOCK_ISSUE_URL, MOCK_ISSUE_CONTENT, MOCK_REPO_OWNER, MOCK_REPO_NAME, 
        MOCK_ISSUE_NUMBER, MOCK_ISSUE_AUTHOR, MOCK_ISSUE_TITLE, cwd=tmp_path
    )

    assert success is True
    # Should start running from step 5.
    # Steps 5, 6, 7, 8, 9, 10, 11, 13 = 8 calls
    # Plus potentially step 12 if loop triggers (it shouldn't here)
    # We just check that step 1 was NOT called.
    
    # Get all labels passed to run
    calls = [c.kwargs.get("label") for c in mocks["run"].call_args_list]
    assert "step1" not in calls
    assert "step4" not in calls
    assert "step5" in calls
    
    # Cost should include previous cost (1.0) + new costs
    assert cost > 1.0

def test_hard_stop_duplicate(mock_dependencies_v2, tmp_path):
    """Test hard stop at Step 1 (Duplicate)."""
    mocks = mock_dependencies_v2
    
    # Step 1 returns duplicate
    mocks["run"].return_value = (True, "Duplicate of #42", 0.1, "gpt-4")

    success, msg, _, _, _ = run_agentic_change_orchestrator(
        MOCK_ISSUE_URL, MOCK_ISSUE_CONTENT, MOCK_REPO_OWNER, MOCK_REPO_NAME, 
        MOCK_ISSUE_NUMBER, MOCK_ISSUE_AUTHOR, MOCK_ISSUE_TITLE, cwd=tmp_path
    )

    assert success is False
    assert "Stopped at step 1" in msg
    assert "Issue is a duplicate" in msg
    
    # Should save state before exiting
    mocks["save"].assert_called()
    # Should NOT clear state
    mocks["clear"].assert_not_called()

def test_hard_stop_implementation_fail(mock_dependencies_v2, tmp_path):
    """Test hard stop at Step 9 (Implementation Failed)."""
    mocks = mock_dependencies_v2
    
    # Mock state up to step 8
    existing_state = {"last_completed_step": 8, "step_outputs": {str(i): "ok" for i in range(1,9)}}
    mocks["load"].return_value = (existing_state, 888)
    
    # Step 9 fails
    mocks["run"].return_value = (False, "FAIL: Syntax error", 0.5, "gpt-4")

    success, msg, _, _, _ = run_agentic_change_orchestrator(
        MOCK_ISSUE_URL, MOCK_ISSUE_CONTENT, MOCK_REPO_OWNER, MOCK_REPO_NAME, 
        MOCK_ISSUE_NUMBER, MOCK_ISSUE_AUTHOR, MOCK_ISSUE_TITLE, cwd=tmp_path
    )

    assert success is False
    assert "Stopped at step 9" in msg
    assert "Implementation failed" in msg

def test_review_loop_logic(mock_dependencies_v2, tmp_path):
    """Test that steps 11 and 12 loop correctly."""
    mocks = mock_dependencies_v2
    
    # Mock state up to step 10
    existing_state = {"last_completed_step": 10, "step_outputs": {str(i): "ok" for i in range(1,11)}}
    mocks["load"].return_value = (existing_state, 777)
    
    # Sequence:
    # 1. Step 11 (Iter 1): Issues Found
    # 2. Step 12 (Iter 1): Fixes applied
    # 3. Step 11 (Iter 2): No Issues Found -> Break
    # 4. Step 13: Create PR
    
    def side_effect_run(instruction, **kwargs):
        label = kwargs.get("label", "")
        if label == "step11_iter1":
            return (True, "Issues found: Typo in docstring", 0.1, "gpt-4")
        if label == "step12_iter1":
            return (True, "Fixed typo", 0.2, "gpt-4")
        if label == "step11_iter2":
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created", 0.1, "gpt-4")
        return (True, "Unexpected", 0.0, "gpt-4")
        
    mocks["run"].side_effect = side_effect_run

    success, _, _, _, _ = run_agentic_change_orchestrator(
        MOCK_ISSUE_URL, MOCK_ISSUE_CONTENT, MOCK_REPO_OWNER, MOCK_REPO_NAME, 
        MOCK_ISSUE_NUMBER, MOCK_ISSUE_AUTHOR, MOCK_ISSUE_TITLE, cwd=tmp_path
    )

    assert success is True
    
    # Verify call sequence
    calls = [c.kwargs.get("label") for c in mocks["run"].call_args_list]
    assert "step11_iter1" in calls
    assert "step12_iter1" in calls
    assert "step11_iter2" in calls
    assert "step13" in calls

def test_worktree_creation_failure(mock_dependencies_v2, tmp_path):
    """Test handling of worktree creation failure."""
    mocks = mock_dependencies_v2
    
    # Mock worktree failure
    mocks["worktree"].return_value = (None, "Git error: cannot create worktree")
    
    # Start at step 9 (where worktree is created)
    existing_state = {"last_completed_step": 8, "step_outputs": {str(i): "ok" for i in range(1,9)}}
    mocks["load"].return_value = (existing_state, 111)

    success, msg, _, _, _ = run_agentic_change_orchestrator(
        MOCK_ISSUE_URL, MOCK_ISSUE_CONTENT, MOCK_REPO_OWNER, MOCK_REPO_NAME, 
        MOCK_ISSUE_NUMBER, MOCK_ISSUE_AUTHOR, MOCK_ISSUE_TITLE, cwd=tmp_path
    )

    assert success is False
    # The error message might be "Failed to restore worktree" or "Failed to create worktree"
    # depending on whether it's resumption or not. Since we start at step 9, it's resumption logic.
    assert "worktree" in msg and ("Failed to" in msg)

def test_file_parsing_step_9_10(mock_dependencies_v2, tmp_path):
    """Test that files are correctly parsed from Step 9 and 10 outputs."""
    mocks = mock_dependencies_v2
    
    # Start at step 9
    existing_state = {"last_completed_step": 8, "step_outputs": {str(i): "ok" for i in range(1,9)}}
    mocks["load"].return_value = (existing_state, 222)
    
    def side_effect_run(instruction, **kwargs):
        label = kwargs.get("label", "")
        if "step9" in label:
            return (True, "FILES_CREATED: src/new.py\nFILES_MODIFIED: src/old.py", 0.1, "gpt-4")
        if "step10" in label:
            return (True, "ARCHITECTURE_FILES_MODIFIED: docs/arch.md", 0.1, "gpt-4")
        if "step11" in label:
            return (True, "No Issues Found", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")
        
    mocks["run"].side_effect = side_effect_run

    success, _, _, _, files = run_agentic_change_orchestrator(
        MOCK_ISSUE_URL, MOCK_ISSUE_CONTENT, MOCK_REPO_OWNER, MOCK_REPO_NAME, 
        MOCK_ISSUE_NUMBER, MOCK_ISSUE_AUTHOR, MOCK_ISSUE_TITLE, cwd=tmp_path
    )

    assert success is True
    assert "src/new.py" in files
    assert "src/old.py" in files
    assert "docs/arch.md" in files

def test_z3_stop_conditions():
    """
    Formal verification of the stop condition logic using Z3.
    We model the _check_hard_stop function logic.
    """
    s = z3.Solver()

    # Inputs
    step_num = z3.Int('step_num')
    # We model the presence of substrings as boolean flags
    has_duplicate = z3.Bool('has_duplicate')
    has_already_impl = z3.Bool('has_already_impl')
    has_clarification = z3.Bool('has_clarification')
    has_no_dev_units = z3.Bool('has_no_dev_units')
    has_arch_decision = z3.Bool('has_arch_decision')
    has_no_changes = z3.Bool('has_no_changes')
    has_fail = z3.Bool('has_fail')

    # Output: Stop Reason (0 = None/Continue, >0 = Stop Reason ID)
    stop_reason = z3.Int('stop_reason')

    # Logic from _check_hard_stop
    # 1: "Issue is a duplicate"
    # 2: "Already implemented"
    # 3: "Clarification needed"
    # 4: "No dev units found"
    # 5: "Architectural decision needed"
    # 6: "No changes needed"
    # 7: "Implementation failed"
    
    # Constraints defining the function logic
    logic = z3.If(z3.And(step_num == 1, has_duplicate), stop_reason == 1,
            z3.If(z3.And(step_num == 2, has_already_impl), stop_reason == 2,
            z3.If(z3.And(step_num == 4, has_clarification), stop_reason == 3,
            z3.If(z3.And(step_num == 6, has_no_dev_units), stop_reason == 4,
            z3.If(z3.And(step_num == 7, has_arch_decision), stop_reason == 5,
            z3.If(z3.And(step_num == 8, has_no_changes), stop_reason == 6,
            z3.If(z3.And(step_num == 9, has_fail), stop_reason == 7,
            stop_reason == 0)))))))
    
    s.add(logic)

    # Verification Case 1: Step 1 with "Duplicate of #" MUST stop
    s.push()
    s.add(step_num == 1)
    s.add(has_duplicate == True)
    s.add(stop_reason == 0) # Assert it continues (contradiction expected)
    assert s.check() == z3.unsat, "Step 1 with duplicate string should imply stop_reason != 0"
    s.pop()

    # Verification Case 2: Step 3 (Research) should NEVER hard stop based on these flags
    s.push()
    s.add(step_num == 3)
    s.add(has_duplicate == True) 
    s.add(stop_reason != 0) # Assert it stops (contradiction expected)
    assert s.check() == z3.unsat, "Step 3 should not stop even if duplicate string is present"
    s.pop()

    # Verification Case 3: Step 9 with "FAIL:" MUST stop
    s.push()
    s.add(step_num == 9)
    s.add(has_fail == True)
    s.add(stop_reason == 0)
    assert s.check() == z3.unsat, "Step 9 with FAIL should stop"
    s.pop()

    # Verification Case 4: Step 9 WITHOUT "FAIL:" should continue
    s.push()
    s.add(step_num == 9)
    s.add(has_fail == False)
    s.add(stop_reason != 0)
    assert s.check() == z3.unsat, "Step 9 without FAIL should continue"
    s.pop()


# -----------------------------------------------------------------------------
# Step 9 Worktree Fallback Tests
# -----------------------------------------------------------------------------

def test_step9_fallback_detects_worktree_changes(mock_dependencies, temp_cwd):
    """
    If LLM output lacks FILES_CREATED/FILES_MODIFIED markers but the
    worktree has actual file changes, orchestrator should use those
    and NOT fail at step 9.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            # LLM wrote files but forgot markers in final response
            return (True, "I've implemented the changes and posted to the issue.", 5.0, "anthropic")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "anthropic")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/99", 0.2, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mock_run.side_effect = side_effect_run

    # Mock _detect_worktree_changes to return files (simulating real worktree changes)
    with patch("pdd.agentic_change_orchestrator._detect_worktree_changes",
               return_value=["prompts/backend/sales_dashboard_python.prompt"]):
        success, msg, cost, model, files = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="Show sold examples on dashboard",
            repo_owner="owner",
            repo_name="repo",
            issue_number=237,
            issue_author="me",
            issue_title="Show sold examples",
            cwd=temp_cwd
        )

    # Should NOT fail at step 9
    assert "no file changes" not in (msg or "")
    # The worktree-detected file should be in the changed files
    assert "prompts/backend/sales_dashboard_python.prompt" in files


def test_step9_worktree_fallback_filters_prompt_files(tmp_path):
    """
    _detect_worktree_changes only picks up .prompt and .md files,
    not .py, .txt, or .agentic_prompt_* temp files.
    """
    # Create a real git repo with tracked prompts/ directory (like pdd_cloud)
    subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=tmp_path, capture_output=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=tmp_path, capture_output=True)

    # Create initial tracked files (simulating existing repo structure)
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts" / "existing.prompt").write_text("existing")
    (tmp_path / "main.py").write_text("existing code")
    subprocess.run(["git", "add", "."], cwd=tmp_path, capture_output=True)
    subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path, capture_output=True)

    # Now simulate LLM changes: new files (untracked) and modified files
    (tmp_path / "prompts" / "foo_python.prompt").write_text("new prompt")
    (tmp_path / "prompts" / "existing.prompt").write_text("modified prompt")
    (tmp_path / "README.md").write_text("docs")
    (tmp_path / "random.py").write_text("code")
    (tmp_path / ".agentic_prompt_abc12345.txt").write_text("temp")
    (tmp_path / "notes.txt").write_text("notes")

    files = _detect_worktree_changes(tmp_path)

    assert "prompts/foo_python.prompt" in files
    assert "prompts/existing.prompt" in files
    assert "README.md" in files
    assert "random.py" not in files
    assert ".agentic_prompt_abc12345.txt" not in files
    assert "notes.txt" not in files


def test_step9_output_saved_on_failure(mock_dependencies, temp_cwd):
    """
    When step 9 fails (no files from either regex or worktree fallback),
    the step output is still saved to state for debugging.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_save_state = mocks["save_state"]

    step9_output_text = "I analyzed the codebase but couldn't determine what prompts to change."

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, step9_output_text, 5.0, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mock_run.side_effect = side_effect_run

    with patch("pdd.agentic_change_orchestrator._detect_worktree_changes", return_value=[]):
        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=237,
            issue_author="me",
            issue_title="Show sold examples",
            cwd=temp_cwd
        )

    assert success is False
    assert "no file changes" in msg

    # Verify save_workflow_state was called with the step 9 output in state
    assert mock_save_state.called
    # Find the call that contains step 9 output
    found_step9_output = False
    for call_args in mock_save_state.call_args_list:
        args, kwargs_call = call_args
        # state is the 4th positional arg
        if len(args) >= 4:
            state_arg = args[3]
            if isinstance(state_arg, dict) and "step_outputs" in state_arg:
                if state_arg["step_outputs"].get("9") == step9_output_text:
                    found_step9_output = True
                    break
    assert found_step9_output, "Step 9 output should be saved to state on failure"


def test_stale_state_detection_clears_and_restarts(mock_dependencies, temp_cwd):
    """
    Test that when issue_updated_at differs from stored state, the stale state
    is cleared and workflow starts fresh from step 1.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_load_state = mocks["load_state"]
    mock_clear_state = mocks["clear_state"]

    # Simulate existing state with OLD issue_updated_at
    old_timestamp = "2024-01-01T10:00:00Z"
    initial_state = {
        "issue_number": 999,
        "last_completed_step": 4,
        "step_outputs": {
            "1": "out1", "2": "out2", "3": "out3", "4": "out4"
        },
        "total_cost": 1.0,
        "model_used": "gpt-4",
        "issue_updated_at": old_timestamp
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
            return (True, "PR Created https://github.com/test/repo/pull/123", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Call with NEWER issue_updated_at - should detect staleness
    new_timestamp = "2024-01-02T12:00:00Z"
    success, _, cost, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=999,
        issue_author="me",
        issue_title="Stale Test",
        issue_updated_at=new_timestamp,
        cwd=temp_cwd
    )

    assert success is True

    # Verify clear_workflow_state was called (stale state was cleared)
    assert mock_clear_state.called, "clear_workflow_state should be called for stale state"

    # Verify ALL steps 1-10 were called (not resumed from step 5)
    labels_called = [call.kwargs.get('label') for call in mock_run.call_args_list]
    assert "step1" in labels_called, "Step 1 should be called after stale state cleared"
    assert "step2" in labels_called, "Step 2 should be called after stale state cleared"
    assert "step3" in labels_called, "Step 3 should be called after stale state cleared"
    assert "step4" in labels_called, "Step 4 should be called after stale state cleared"
    assert "step5" in labels_called, "Step 5 should be called"


def test_valid_resume_when_issue_unchanged(mock_dependencies, temp_cwd):
    """
    Test that when issue_updated_at matches stored state, workflow resumes
    from the cached step (not cleared due to staleness).
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_load_state = mocks["load_state"]
    mock_clear_state = mocks["clear_state"]

    # Simulate existing state with SAME issue_updated_at
    timestamp = "2024-01-01T10:00:00Z"
    initial_state = {
        "issue_number": 888,
        "last_completed_step": 4,
        "step_outputs": {
            "1": "out1", "2": "out2", "3": "out3", "4": "out4"
        },
        "total_cost": 1.0,
        "model_used": "gpt-4",
        "issue_updated_at": timestamp
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
            return (True, "PR Created https://github.com/test/repo/pull/456", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Call with SAME issue_updated_at - should resume normally
    success, _, cost, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=888,
        issue_author="me",
        issue_title="Resume Test",
        issue_updated_at=timestamp,
        cwd=temp_cwd
    )

    assert success is True

    # Verify steps 1-4 were NOT called (resumed from step 5, not cleared for staleness)
    labels_called = [call.kwargs.get('label') for call in mock_run.call_args_list]
    assert "step1" not in labels_called, "Step 1 should be skipped when resuming"
    assert "step4" not in labels_called, "Step 4 should be skipped when resuming"
    assert "step5" in labels_called, "Step 5 should be called when resuming from step 4"

    # clear_workflow_state is called once at the END of successful completion (line 796),
    # but NOT called for stale state detection at the start.
    # The key indicator is that steps 1-4 were skipped (workflow resumed, not restarted).


def test_backward_compat_state_without_issue_updated_at(mock_dependencies, temp_cwd):
    """
    Test that old state without issue_updated_at field still works
    (backward compatibility) - should resume normally without clearing for staleness.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_load_state = mocks["load_state"]

    # Simulate OLD state without issue_updated_at field
    initial_state = {
        "issue_number": 777,
        "last_completed_step": 4,
        "step_outputs": {
            "1": "out1", "2": "out2", "3": "out3", "4": "out4"
        },
        "total_cost": 1.0,
        "model_used": "gpt-4"
        # Note: no issue_updated_at field
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
            return (True, "PR Created https://github.com/test/repo/pull/789", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Call with a new issue_updated_at - should NOT clear because old state has no field
    success, _, cost, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=777,
        issue_author="me",
        issue_title="Backward Compat Test",
        issue_updated_at="2024-01-15T09:00:00Z",
        cwd=temp_cwd
    )

    assert success is True

    # Verify steps 1-4 were NOT called (resumed from step 5, backward compat works)
    labels_called = [call.kwargs.get('label') for call in mock_run.call_args_list]
    assert "step1" not in labels_called, "Step 1 should be skipped (backward compat)"
    assert "step4" not in labels_called, "Step 4 should be skipped (backward compat)"
    assert "step5" in labels_called, "Step 5 should be called when resuming"


# -----------------------------------------------------------------------------
# Bug #448: JSON in step output causes KeyError in subsequent step formatting
# -----------------------------------------------------------------------------

def test_step_output_with_json_does_not_cause_keyerror(mock_dependencies, temp_cwd):
    """
    Bug #448: When LLM output contains JSON objects like {"url": "..."},
    Python's str.format() interprets the curly braces as format placeholders.

    This test reproduces the bug where step 4 output contains JSON like:
        {"url": "https://example.com", "description": "API docs"}

    When step 5's template is formatted, the {step4_output} is replaced with
    this text, but then str.format() tries to find a key called '"url"'
    (with quotes as part of the key name), causing KeyError.

    The fix should escape curly braces in step outputs before embedding them
    in subsequent prompt templates.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Simulate step 4 output containing JSON (this triggers the bug)
    json_in_step4_output = '''
## Step 4: Requirements Clarity Check

**Status:** Requirements Clear

I researched the following resources:
- {"url": "https://example.com/api", "purpose": "API documentation"}
- {"url": "https://docs.example.com", "purpose": "SDK reference"}

The feature implementation is well-defined.

---
*Proceeding to Step 5: Documentation Changes*
'''

    call_count = [0]

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step4":
            return (True, json_in_step4_output, 0.1, "gpt-4")
        if label == "step9":
            return (True, "FILES_CREATED: new.py", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/123", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Return a real string template that mimics the actual prompts
    # Step 5 template includes {step4_output} placeholder
    step5_template = """Step 5 prompt.
Previous step output:
{step4_output}
Issue URL: {issue_url}
"""

    def return_template(template_name):
        call_count[0] += 1
        if "step5" in template_name:
            return step5_template
        # Return a simple template for other steps
        return "{issue_url}"

    mock_template_loader.side_effect = return_template

    # This should NOT raise KeyError
    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="Add new feature",
        repo_owner="owner",
        repo_name="repo",
        issue_number=448,
        issue_author="me",
        issue_title="Feature with JSON in output",
        cwd=temp_cwd,
        quiet=True
    )

    # If the bug is fixed, step 5 formatting should not raise KeyError
    # The error message contains "Context missing key for step 5" when the bug exists
    assert "Context missing key for step 5" not in msg, f"Bug #448 not fixed: {msg}"


def test_step_output_with_curly_braces_escaped(mock_dependencies, temp_cwd):
    """
    Test that step outputs containing curly braces are properly escaped
    so they don't interfere with str.format() in subsequent steps.

    Various patterns that could cause issues:
    - {"key": "value"} - JSON objects
    - {variable_name} - Looks like a format placeholder
    - {{already_escaped}} - Should remain as-is after unescaping
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    problematic_output = '''
This output has various curly brace patterns:
1. JSON: {"name": "test", "value": 123}
2. Template placeholder lookalike: {some_variable}
3. Already escaped: {{escaped_braces}}
4. Complex nested: {"outer": {"inner": "value"}}
'''

    call_count = [0]

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step3":
            return (True, problematic_output, 0.1, "gpt-4")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Step 4 template includes {step3_output} placeholder
    step4_template = """Step 4 prompt.
Previous step output:
{step3_output}
Issue URL: {issue_url}
"""

    def return_template(template_name):
        call_count[0] += 1
        if "step4" in template_name:
            return step4_template
        return "{issue_url}"

    mock_template_loader.side_effect = return_template

    # This should not raise KeyError for any of the problematic patterns
    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="Test curly brace handling",
        repo_owner="owner",
        repo_name="repo",
        issue_number=449,
        issue_author="me",
        issue_title="Curly brace test",
        cwd=temp_cwd,
        quiet=True
    )

    # Should not fail due to format key errors
    assert "Context missing key for step 4" not in msg, f"Curly brace escaping failed: {msg}"