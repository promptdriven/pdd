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
# Template preprocessing fix: Preprocessing and Error Handling Tests
# -----------------------------------------------------------------------------

def test_template_preprocessing_include_directives_are_preprocessed(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify that <include> directives in templates are preprocessed
    before format() is called.

    Bug: Templates containing <include> directives were being passed directly
    to format(), causing the LLM to receive unexpanded directives instead of
    the included content.

    Fix: preprocess() is called on each template before format() to expand
    <include> directives.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Track the preprocessed templates
    preprocessed_templates = []

    # Return a template with an <include> directive
    mock_template_loader.return_value = "Template with <include>some_file.txt</include> directive and {issue_number}"

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        # Capture the instruction that was passed (after preprocessing and formatting)
        instruction = kwargs.get("instruction", "")
        preprocessed_templates.append(instruction)
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Patch preprocess to verify it's being called
    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        # Make preprocess return a modified template that shows it was called
        mock_preprocess.return_value = "PREPROCESSED: Template content and {issue_number}"

        run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=123,
            issue_author="author",
            issue_title="Test",
            cwd=temp_cwd,
            quiet=True
        )

        # Verify preprocess was called for each step
        assert mock_preprocess.call_count >= 10, (
            f"preprocess should be called for each step, but was only called "
            f"{mock_preprocess.call_count} times"
        )

        # Verify preprocess was called with correct parameters
        for call in mock_preprocess.call_args_list:
            args, kwargs = call
            assert "recursive" in kwargs and kwargs["recursive"] == False
            assert "double_curly_brackets" in kwargs and kwargs["double_curly_brackets"] == True
            assert "exclude_keys" in kwargs and isinstance(kwargs["exclude_keys"], list)


def test_template_preprocessing_curly_braces_in_included_content_are_escaped(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify that curly braces in included content don't break format().

    Bug: When <include> directives expand content containing curly braces
    (e.g., JSON, shell variables like ${VAR}), the subsequent format() call
    would fail with ValueError because those braces are interpreted as
    format placeholders.

    Fix: preprocess() with double_curly_brackets=True escapes braces in
    included content, converting { to {{ and } to }}.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Template that includes JSON with curly braces
    template_with_json = '''Step template for {issue_number}
Included JSON: {"key": "value", "nested": {"inner": true}}
Shell var: ${HOME}
End template'''

    mock_template_loader.return_value = template_with_json

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Patch preprocess to escape curly braces as the real implementation would
    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        # Simulate what preprocess does: escape braces in non-placeholder content
        def escape_braces(template, **kwargs):
            exclude_keys = kwargs.get("exclude_keys", [])
            # Escape JSON braces but not the {issue_number} placeholder
            escaped = template.replace('{"key"', '{{"key"')
            escaped = escaped.replace('{"inner"', '{{"inner"')
            escaped = escaped.replace('${HOME}', '${{HOME}}')
            return escaped

        mock_preprocess.side_effect = escape_braces

        # This should NOT raise ValueError from format()
        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=456,
            issue_author="author",
            issue_title="Test with JSON",
            cwd=temp_cwd,
            quiet=True
        )

        # Should succeed without format errors
        assert success is True
        assert "PR Created:" in msg


def test_template_preprocessing_valueerror_from_format_is_caught(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify that ValueError from format() is properly caught.

    Bug: Only KeyError was caught, but format() can also raise ValueError
    for invalid format strings (e.g., unclosed braces, invalid conversion
    specifiers).

    Fix: Catch ValueError in addition to KeyError and return a descriptive
    error message.
    """
    mocks = mock_dependencies
    mock_template_loader = mocks["template_loader"]

    # Create a mock template whose format() raises ValueError
    mock_template = MagicMock()
    mock_template_loader.return_value = mock_template

    # Patch preprocess to return the template unchanged
    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        # Return a malformed format string that will cause ValueError
        mock_preprocess.return_value = "Template with {invalid format specifier!x}"

        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=789,
            issue_author="author",
            issue_title="Test ValueError",
            cwd=temp_cwd,
            quiet=True
        )

        # Should fail gracefully with a descriptive message
        assert success is False
        assert "Prompt formatting error" in msg
        assert "step 1" in msg
        # Should mention invalid format string
        assert "invalid format" in msg.lower() or "ValueError" in msg


def test_template_preprocessing_generic_exception_from_format_is_caught(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify that generic exceptions from format() are caught.

    Bug: Only KeyError was caught, but format() could raise other exceptions
    in edge cases (e.g., custom __format__ methods raising exceptions).

    Fix: Catch Exception as a fallback and return a descriptive error message
    that includes the exception type.

    Note: This test verifies that the generic Exception handler exists by
    testing ValueError (which is caught with a specific message), since
    we can verify the except blocks are structured properly.
    """
    mocks = mock_dependencies
    mock_template_loader = mocks["template_loader"]

    # Use a template that will cause an IndexError via positional placeholder
    # This is hard to trigger in practice, so we use ValueError test as proxy
    # The key is that the code structure catches Exception as fallback

    # Patch preprocess to return a template with invalid format specifier
    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        # Using an invalid conversion specifier !z that will raise ValueError
        mock_preprocess.return_value = "Template for {issue_number!z}"

        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=101,
            issue_author="author",
            issue_title="Test Generic Exception",
            cwd=temp_cwd,
            quiet=True
        )

        # Should fail gracefully with ValueError (caught by either ValueError or Exception handler)
        assert success is False
        assert "Prompt formatting error" in msg
        assert "step 1" in msg


def test_template_preprocessing_preprocessing_failure_is_non_fatal(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify that preprocessing failures are logged but don't halt.

    Bug: If preprocess() fails, the entire orchestrator would crash.

    Fix: Preprocessing failures are caught and logged as warnings, then the
    orchestrator continues with the original (unprocessed) template. This
    allows the workflow to proceed even if preprocessing has issues.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]
    mock_console = mocks["console"]

    # Return a simple template that doesn't require preprocessing
    mock_template_loader.return_value = "Simple template for {issue_number}"

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Patch preprocess to raise an exception
    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = Exception("Preprocessing failed: file not found")

        # Run with quiet=False so we can verify the warning is logged
        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=202,
            issue_author="author",
            issue_title="Test Preprocessing Failure",
            cwd=temp_cwd,
            quiet=False  # Enable console output to test warning
        )

        # Should still succeed (preprocessing failure is non-fatal)
        assert success is True
        assert "PR Created:" in msg or "PR" in msg

        # Verify warning was logged
        warning_calls = [
            call for call in mock_console.print.call_args_list
            if "Warning" in str(call) and "Preprocessing failed" in str(call)
        ]
        assert len(warning_calls) >= 1, "Warning about preprocessing failure should be logged"


def test_template_preprocessing_preprocess_called_for_step11_and_step12(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify preprocess is called for review loop steps (11 and 12).

    Bug: The fix might only apply to the main step loop but miss the review
    loop steps 11 and 12 which also use format().

    Fix: Preprocessing is applied to all format() calls including steps 11-12.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]
    mock_load_state = mocks["load_state"]

    # Start from step 10 to reach the review loop
    initial_state = {
        "issue_number": 303,
        "last_completed_step": 10,
        "step_outputs": {str(i): f"out{i}" for i in range(1, 11)},
        "total_cost": 1.0,
        "model_used": "gpt-4",
        "worktree_path": str(temp_cwd / ".pdd" / "worktrees" / "change-issue-303"),
        "review_iteration": 0,
        "previous_fixes": ""
    }
    initial_state["step_outputs"]["9"] = "FILES_CREATED: test.py"
    mock_load_state.return_value = (initial_state, 12345)

    mock_template_loader.return_value = "Template for {issue_number}"

    # Track steps 11 and 12 calls
    step11_called = False
    step12_called = False

    def side_effect_run(**kwargs):
        nonlocal step11_called, step12_called
        label = kwargs.get("label", "")
        if "step11" in label:
            step11_called = True
            return (True, "Issues found: need fix", 0.1, "gpt-4")
        if "step12" in label:
            step12_called = True
            return (True, "Fixed issues", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "No Issues Found", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Create worktree directory so it exists
    worktree_path = temp_cwd / ".pdd" / "worktrees" / "change-issue-303"
    worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.return_value = "Preprocessed template for {issue_number}"

        run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=303,
            issue_author="author",
            issue_title="Test Review Loop",
            cwd=temp_cwd,
            quiet=True
        )

        # Verify steps 11 and 12 were called
        assert step11_called, "Step 11 should have been called"
        assert step12_called, "Step 12 should have been called"

        # Verify preprocess was called for all steps including 11, 12, and 13
        # Minimum: step 11 (iter 1) + step 12 (iter 1) + step 11 (iter 2) + step 13 = 4
        assert mock_preprocess.call_count >= 4, (
            f"preprocess should be called for review loop steps, "
            f"but was only called {mock_preprocess.call_count} times"
        )


def test_template_preprocessing_preprocess_called_for_step13(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify preprocess is called for step 13 (PR creation).

    Bug: Step 13 also uses format() and needs preprocessing.

    Fix: Preprocessing is applied to step 13's template as well.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]
    mock_load_state = mocks["load_state"]

    # Start from step 12 to go directly to step 13
    initial_state = {
        "issue_number": 404,
        "last_completed_step": 12,
        "step_outputs": {str(i): f"out{i}" for i in range(1, 13)},
        "total_cost": 1.2,
        "model_used": "gpt-4",
        "worktree_path": str(temp_cwd / ".pdd" / "worktrees" / "change-issue-404"),
        "review_iteration": 1,
        "previous_fixes": "prev fixes"
    }
    initial_state["step_outputs"]["9"] = "FILES_CREATED: test.py"
    mock_load_state.return_value = (initial_state, 12345)

    mock_template_loader.return_value = "PR template for {issue_number} with {files_to_stage}"

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Create worktree directory
    worktree_path = temp_cwd / ".pdd" / "worktrees" / "change-issue-404"
    worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.return_value = "Preprocessed PR template for {issue_number} with {files_to_stage}"

        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=404,
            issue_author="author",
            issue_title="Test Step 13",
            cwd=temp_cwd,
            quiet=True
        )

        assert success is True
        assert "PR Created:" in msg

        # Verify preprocess was called (at least once for step 13)
        assert mock_preprocess.call_count >= 1, "preprocess should be called for step 13"

        # Verify the last call was for step 13 template
        last_call = mock_preprocess.call_args_list[-1]
        args, kwargs = last_call
        assert "exclude_keys" in kwargs
        # Step 13 context should have issue_number and files_to_stage
        assert "issue_number" in kwargs["exclude_keys"]


def test_template_preprocessing_keyerror_still_handled_correctly(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Regression test to verify KeyError is still handled.

    The original code only caught KeyError. After adding ValueError and Exception
    handlers, KeyError should still be caught and return a descriptive message.
    """
    mocks = mock_dependencies
    mock_template_loader = mocks["template_loader"]

    # Template referencing a key that won't be in context
    mock_template_loader.return_value = "Template needs {nonexistent_key} which is missing"

    # Patch preprocess to return template unchanged (so format() will fail on missing key)
    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = lambda t, **kw: t  # passthrough

        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=500,
            issue_author="author",
            issue_title="Test KeyError",
            cwd=temp_cwd,
            quiet=True
        )

        # Should fail with KeyError-specific message
        assert success is False
        assert "Prompt formatting error" in msg
        assert "missing key" in msg
        assert "nonexistent_key" in msg


def test_template_preprocessing_exclude_keys_contains_all_context_keys(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify exclude_keys contains all context keys.

    Critical: If a context key is missing from exclude_keys, preprocess() will
    double-escape its placeholder (e.g., {issue_number} -> {{issue_number}}),
    causing format() to output literal braces instead of substituting the value.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    mock_template_loader.return_value = "Template for {issue_number} by {issue_author}"

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Track exclude_keys passed to preprocess
    exclude_keys_per_call = []

    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        def capture_exclude_keys(template, **kwargs):
            exclude_keys_per_call.append(kwargs.get("exclude_keys", []))
            return template  # passthrough
        mock_preprocess.side_effect = capture_exclude_keys

        run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=501,
            issue_author="testauthor",
            issue_title="Test exclude_keys",
            cwd=temp_cwd,
            quiet=True
        )

        # Verify each call had the expected context keys in exclude_keys
        for i, exclude_keys in enumerate(exclude_keys_per_call):
            # Core context keys that should always be present
            assert "issue_number" in exclude_keys, f"Call {i}: issue_number missing from exclude_keys"
            assert "issue_author" in exclude_keys, f"Call {i}: issue_author missing from exclude_keys"
            assert "issue_title" in exclude_keys, f"Call {i}: issue_title missing from exclude_keys"
            assert "repo_owner" in exclude_keys, f"Call {i}: repo_owner missing from exclude_keys"
            assert "repo_name" in exclude_keys, f"Call {i}: repo_name missing from exclude_keys"


def test_template_preprocessing_formatted_prompt_contains_substituted_values(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify the instruction passed to run_agentic_task
    contains correctly substituted values, not raw placeholders or double-braces.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Template with placeholders
    mock_template_loader.return_value = "Process issue {issue_number} titled '{issue_title}' by {issue_author}"

    # Capture the instructions passed to run_agentic_task
    captured_instructions = []

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured_instructions.append((label, instruction))
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Use real-ish preprocess behavior: passthrough (no includes to expand)
    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = lambda t, **kw: t

        run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=502,
            issue_author="alice",
            issue_title="Fix the bug",
            cwd=temp_cwd,
            quiet=True
        )

        # Verify at least one instruction contains the substituted values
        assert len(captured_instructions) > 0, "No instructions were captured"

        # Check first step's instruction
        label, instruction = captured_instructions[0]
        assert "502" in instruction, f"issue_number not substituted in {label}: {instruction[:100]}"
        assert "alice" in instruction, f"issue_author not substituted in {label}: {instruction[:100]}"
        assert "Fix the bug" in instruction, f"issue_title not substituted in {label}: {instruction[:100]}"

        # Verify no raw placeholders remain
        assert "{issue_number}" not in instruction, "Raw placeholder {issue_number} found in instruction"
        assert "{{issue_number}}" not in instruction, "Double-escaped {{issue_number}} found in instruction"


def test_template_preprocessing_quiet_mode_suppresses_warnings(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify that quiet=True suppresses preprocessing warnings.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]
    mock_console = mocks["console"]

    mock_template_loader.return_value = "Simple template for {issue_number}"

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Patch preprocess to raise an exception
    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = Exception("Preprocessing failed")

        # Run with quiet=True
        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=503,
            issue_author="author",
            issue_title="Test Quiet Mode",
            cwd=temp_cwd,
            quiet=True  # Quiet mode
        )

        # Should still succeed (preprocessing failure is non-fatal)
        assert success is True

        # Verify NO warning was printed (quiet mode)
        warning_calls = [
            call for call in mock_console.print.call_args_list
            if "Warning" in str(call) and "Preprocessing failed" in str(call)
        ]
        assert len(warning_calls) == 0, "Warnings should be suppressed in quiet mode"


def test_template_preprocessing_context_grows_across_steps(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify exclude_keys is recalculated as context grows.

    The context dictionary grows as steps complete (e.g., step1_output, step2_output
    are added). The exclude_keys must be recalculated for each step to include
    these new keys.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    mock_template_loader.return_value = "Template for {issue_number}"

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Track exclude_keys length for each step
    exclude_keys_counts = []

    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        def capture_exclude_keys(template, **kwargs):
            exclude_keys = kwargs.get("exclude_keys", [])
            exclude_keys_counts.append(len(exclude_keys))
            return template
        mock_preprocess.side_effect = capture_exclude_keys

        run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=504,
            issue_author="author",
            issue_title="Test Context Growth",
            cwd=temp_cwd,
            quiet=True
        )

        # Verify context grows (later steps should have more keys due to step outputs)
        assert len(exclude_keys_counts) >= 10, "Should have multiple preprocess calls"

        # The count should generally increase as steps complete and add outputs to context
        # At minimum, later calls should have at least as many keys as earlier calls
        # (context doesn't shrink)
        for i in range(1, len(exclude_keys_counts)):
            assert exclude_keys_counts[i] >= exclude_keys_counts[0], (
                f"exclude_keys count should not decrease: step 0 had {exclude_keys_counts[0]}, "
                f"step {i} had {exclude_keys_counts[i]}"
            )


def test_template_preprocessing_error_message_contains_step_number(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify error messages include the step number.

    This helps users identify which step's template has the formatting issue.
    """
    mocks = mock_dependencies
    mock_template_loader = mocks["template_loader"]
    mock_load_state = mocks["load_state"]

    # Start from step 4 to test a specific step number in error
    initial_state = {
        "issue_number": 505,
        "last_completed_step": 4,
        "step_outputs": {str(i): f"out{i}" for i in range(1, 5)},
        "total_cost": 0.5,
        "model_used": "gpt-4",
        "worktree_path": str(temp_cwd / ".pdd" / "worktrees" / "change-issue-505"),
    }
    mock_load_state.return_value = (initial_state, 12345)

    # Create worktree directory
    worktree_path = temp_cwd / ".pdd" / "worktrees" / "change-issue-505"
    worktree_path.mkdir(parents=True, exist_ok=True)

    mock_template_loader.return_value = "Template for {missing_key}"

    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = lambda t, **kw: t

        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=505,
            issue_author="author",
            issue_title="Test Error Step Number",
            cwd=temp_cwd,
            quiet=True
        )

        assert success is False
        # Error should mention step 5 (next step after last_completed_step=4)
        assert "step 5" in msg, f"Error message should mention step number: {msg}"


def test_template_preprocessing_integration_with_real_preprocess(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Integration test using real preprocess function.

    This test doesn't mock preprocess() to verify the actual integration works.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Template without includes (preprocess should pass through cleanly)
    # Include some JSON-like content that would break without proper escaping
    template_with_json = '''Process issue {issue_number}
Here is some JSON context: {{"config": "value"}}
End of template'''

    mock_template_loader.return_value = template_with_json

    captured_instructions = []

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured_instructions.append((label, instruction))
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Don't mock preprocess - use real implementation
    # But we need to suppress its console output
    with patch("pdd.preprocess.console"):
        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=506,
            issue_author="author",
            issue_title="Integration Test",
            cwd=temp_cwd,
            quiet=True
        )

        # Should succeed
        assert success is True, f"Integration test failed: {msg}"

        # Verify instructions have substituted values and preserved JSON
        assert len(captured_instructions) > 0
        label, instruction = captured_instructions[0]
        assert "506" in instruction, "issue_number should be substituted"
        # The already-doubled braces should remain as single braces after format()
        assert '{"config": "value"}' in instruction, (
            f"JSON should be preserved in instruction: {instruction[:200]}"
        )


def test_template_preprocessing_valueerror_caught_for_step11(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify ValueError is caught for step 11.

    Steps 11, 12, and 13 have separate format() calls that also need
    proper error handling.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]
    mock_load_state = mocks["load_state"]

    # Start from step 10 to reach step 11
    initial_state = {
        "issue_number": 600,
        "last_completed_step": 10,
        "step_outputs": {str(i): f"out{i}" for i in range(1, 11)},
        "total_cost": 1.0,
        "model_used": "gpt-4",
        "worktree_path": str(temp_cwd / ".pdd" / "worktrees" / "change-issue-600"),
        "review_iteration": 0,
        "previous_fixes": ""
    }
    initial_state["step_outputs"]["9"] = "FILES_CREATED: test.py"
    mock_load_state.return_value = (initial_state, 12345)

    # Return a normal template for most calls
    mock_template_loader.return_value = "Template for {issue_number}"

    # Create worktree directory
    worktree_path = temp_cwd / ".pdd" / "worktrees" / "change-issue-600"
    worktree_path.mkdir(parents=True, exist_ok=True)

    call_count = [0]

    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        def preprocess_side_effect(template, **kwargs):
            call_count[0] += 1
            # Return invalid format string on the call for step 11 template
            # Step 11 is loaded after step 10 completes
            if call_count[0] >= 1 and "step11" in str(mock_template_loader.call_args):
                return "Template with {invalid!z} specifier"
            # Check if this is likely the step 11 call by looking at context
            if call_count[0] == 1:  # First call after resuming at step 10
                return "Template with {invalid!z} specifier for {issue_number}"
            return template
        mock_preprocess.side_effect = preprocess_side_effect

        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=600,
            issue_author="author",
            issue_title="Test Step 11 ValueError",
            cwd=temp_cwd,
            quiet=True
        )

        # Should fail gracefully with error message mentioning step 11
        assert success is False
        assert "Prompt formatting error" in msg
        assert "step 11" in msg


def test_template_preprocessing_step_output_keys_in_exclude_keys(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify step output keys are in exclude_keys.

    As steps complete, their outputs (step1_output, step2_output, etc.) are
    added to context. These must be in exclude_keys to prevent double-escaping.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    mock_template_loader.return_value = "Template for {issue_number}"

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Track exclude_keys for later steps
    exclude_keys_by_call = []

    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        def capture_exclude_keys(template, **kwargs):
            exclude_keys_by_call.append(kwargs.get("exclude_keys", []))
            return template
        mock_preprocess.side_effect = capture_exclude_keys

        run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=601,
            issue_author="author",
            issue_title="Test Step Output Keys",
            cwd=temp_cwd,
            quiet=True
        )

        # Verify step output keys appear in exclude_keys for later steps
        # By the time we reach step 5, step1_output through step4_output should exist
        assert len(exclude_keys_by_call) >= 5, "Should have at least 5 preprocess calls"

        # Check that later calls include step output keys
        # Call index 4 is for step 5 (0-indexed), should have step1-4 outputs
        later_call_exclude_keys = exclude_keys_by_call[4]
        assert "step1_output" in later_call_exclude_keys, (
            f"step1_output should be in exclude_keys by step 5: {later_call_exclude_keys}"
        )
        assert "step2_output" in later_call_exclude_keys, (
            f"step2_output should be in exclude_keys by step 5: {later_call_exclude_keys}"
        )


def test_template_preprocessing_shell_variable_syntax_handled(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Verify shell variable syntax ${VAR} is handled.

    Templates may contain shell-style variables like ${HOME} which should not
    break the format() call.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Template with shell variable syntax
    mock_template_loader.return_value = "Process {issue_number} in ${HOME}/projects"

    captured_instructions = []

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured_instructions.append((label, instruction))
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    # Use a preprocess mock that handles ${VAR} like the real implementation
    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        def handle_shell_vars(template, **kwargs):
            # Real preprocess converts ${VAR} to ${{VAR}} to escape it
            return template.replace("${HOME}", "${{HOME}}")
        mock_preprocess.side_effect = handle_shell_vars

        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=602,
            issue_author="author",
            issue_title="Test Shell Variables",
            cwd=temp_cwd,
            quiet=True
        )

        # Should succeed without format errors
        assert success is True, f"Should handle shell variables: {msg}"

        # Verify instruction has substituted issue_number and preserved ${HOME}
        assert len(captured_instructions) > 0
        label, instruction = captured_instructions[0]
        assert "602" in instruction, "issue_number should be substituted"
        # After format(), ${{HOME}} becomes ${HOME}
        assert "${HOME}" in instruction, f"Shell variable should be preserved: {instruction}"


def test_template_preprocessing_no_unexpanded_include_tags(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Core bug test - verify <include> tags are expanded.

    This is the core bug: templates with <include> directives were passed
    directly to format() without expansion. The instruction sent to the LLM
    should NOT contain raw <include> tags.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Template with an include directive
    mock_template_loader.return_value = "Process {issue_number}\n<include>some_file.txt</include>\nEnd"

    captured_instructions = []

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured_instructions.append((label, instruction))
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        # Simulate preprocess expanding the include directive
        def expand_includes(template, **kwargs):
            return template.replace(
                "<include>some_file.txt</include>",
                "INCLUDED CONTENT FROM FILE"
            )
        mock_preprocess.side_effect = expand_includes

        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=603,
            issue_author="author",
            issue_title="Test Include Expansion",
            cwd=temp_cwd,
            quiet=True
        )

        assert success is True

        # Verify NO instruction contains unexpanded <include> tags
        for label, instruction in captured_instructions:
            assert "<include>" not in instruction, (
                f"Raw <include> tag found in {label} instruction: {instruction[:200]}"
            )
            assert "</include>" not in instruction, (
                f"Raw </include> tag found in {label} instruction: {instruction[:200]}"
            )

        # Verify the included content IS present
        label, instruction = captured_instructions[0]
        assert "INCLUDED CONTENT FROM FILE" in instruction, (
            f"Included content should be in instruction: {instruction[:200]}"
        )


def test_template_preprocessing_mixed_placeholders_and_json(mock_dependencies, temp_cwd):
    """
    Template preprocessing fix: Real-world scenario with placeholders and JSON.

    Templates often contain both format placeholders like {issue_number} and
    literal JSON with braces. Both must work correctly.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Real-world template with placeholders and JSON
    template = '''Process issue {issue_number} by {issue_author}

Configuration:
```json
{
    "repo": "example",
    "settings": {"debug": true, "verbose": false}
}
```

Please implement the changes.'''

    mock_template_loader.return_value = template

    captured_instructions = []

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured_instructions.append((label, instruction))
        if label == "step9":
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    with patch("pdd.agentic_change_orchestrator.preprocess") as mock_preprocess:
        # Simulate preprocess escaping JSON braces but preserving placeholders
        def escape_json_braces(template, **kwargs):
            exclude_keys = kwargs.get("exclude_keys", [])
            # Escape braces in JSON but not in placeholders
            result = template
            # Simple simulation: escape the JSON block's braces
            result = result.replace('{\n    "repo"', '{{\n    "repo"')
            result = result.replace('"settings": {', '"settings": {{')
            result = result.replace('false}\n}', 'false}}\n}}')
            return result
        mock_preprocess.side_effect = escape_json_braces

        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=604,
            issue_author="bob",
            issue_title="Test Mixed Content",
            cwd=temp_cwd,
            quiet=True
        )

        assert success is True, f"Should handle mixed content: {msg}"

        # Verify placeholders were substituted
        assert len(captured_instructions) > 0
        label, instruction = captured_instructions[0]
        assert "604" in instruction, "issue_number should be substituted"
        assert "bob" in instruction, "issue_author should be substituted"

        # Verify JSON structure is present (braces should be unescaped after format())
        assert '"repo"' in instruction, "JSON content should be present"
        assert '"settings"' in instruction, "Nested JSON should be present"
