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
from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator, _parse_changed_files, _detect_worktree_changes, _parse_direct_edit_candidates, _check_existing_pr, _review_loop_no_issues, _scope_architecture_to_changed_files

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
         patch("pdd.agentic_change_orchestrator.post_step_comment") as mock_post_comment, \
         patch("pdd.agentic_change_orchestrator.console") as mock_console, \
         patch("pdd.agentic_change_orchestrator.preprocess", side_effect=lambda prompt, **kw: prompt) as mock_preprocess, \
         patch("pdd.agentic_change_orchestrator._check_existing_pr", return_value=None) as mock_check_pr:

        # Default mock behaviors
        mock_run.return_value = (True, "Default Agent Output", 0.1, "gpt-4")

        # Return a string template (orchestrator now uses preprocess + string replacement, not .format())
        mock_template_loader.return_value = "Mocked Prompt Template"

        # Default state: No existing state
        mock_load_state.return_value = (None, None)

        # Mock git rev-parse to return the temp_cwd as root
        # This ensures mkdir operations on the root succeed
        mock_subprocess.return_value.stdout = str(temp_cwd)
        mock_subprocess.return_value.returncode = 0

        # Default: post_step_comment succeeds
        mock_post_comment.return_value = True

        yield {
            "run": mock_run,
            "template_loader": mock_template_loader,
            "load_state": mock_load_state,
            "save_state": mock_save_state,
            "clear_state": mock_clear_state,
            "subprocess": mock_subprocess,
            "post_comment": mock_post_comment,
            "console": mock_console,
            "check_pr": mock_check_pr,
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
            return (True, "Posted to GitHub.\nSTOP_CONDITION: Architectural Decision Needed", 0.1, "gpt-4")
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
    assert "architectural decision needed" in msg.lower()


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

    # Template with placeholders so we can verify context keys are substituted
    mock_template_loader.return_value = "SYNC_SCRIPT:{sync_order_script}:SYNC_LIST:{sync_order_list}:END"

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

    # Find the step 13 call and verify context keys were substituted
    step13_calls = [c for c in mock_run.call_args_list if c.kwargs.get("label") == "step13"]
    assert step13_calls, "step13 should have been called"
    instruction = step13_calls[-1].kwargs["instruction"]
    # If keys were in context, the placeholders would be replaced (not literal)
    assert "{sync_order_script}" not in instruction, "sync_order_script not substituted in context"
    assert "{sync_order_list}" not in instruction, "sync_order_list not substituted in context"

def test_sync_order_detects_pdd_prompts_prefix(mock_dependencies, temp_cwd):
    """
    Test that sync order detection works when files are reported with
    'pdd/prompts/' prefix (canonical path) instead of 'prompts/' (symlink).

    Git reports files via real paths (pdd/prompts/...) not symlink paths
    (prompts/...), so the filter must accept both prefixes.

    Regression test for issue #836 where pdd-sync failed because the
    startswith("prompts/") check missed pdd/prompts/ paths.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # Step 9 reports modified prompt files with pdd/prompts/ prefix
    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_MODIFIED: pdd/prompts/foo_python.prompt", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        return (True, "Default", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run
    mock_template_loader.return_value = "SYNC_SCRIPT:{sync_order_script}:SYNC_LIST:{sync_order_list}:END"

    # Create worktree directory with prompt files
    issue_number = 998
    worktree_path = temp_cwd / ".pdd" / "worktrees" / f"change-issue-{issue_number}"
    prompts_dir = worktree_path / "prompts"
    prompts_dir.mkdir(parents=True)
    (prompts_dir / "foo_python.prompt").write_text("% foo module")

    # Mock _setup_worktree to return the pre-created path without deleting it
    with patch("pdd.agentic_change_orchestrator._setup_worktree",
               return_value=(worktree_path, None)):
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

    # Find the step 13 call and verify sync_order was populated (not defaults)
    step13_calls = [c for c in mock_run.call_args_list if c.kwargs.get("label") == "step13"]
    assert step13_calls, "step13 should have been called"
    instruction = step13_calls[-1].kwargs["instruction"]
    assert "{sync_order_script}" not in instruction, "sync_order_script not substituted in context"
    assert "{sync_order_list}" not in instruction, "sync_order_list not substituted in context"
    # The sync_order_list should NOT be the default "No modules to sync"
    assert "No modules to sync" not in instruction, (
        "pdd/prompts/ prefix was not recognized — sync order was not generated"
    )


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

    # Template with placeholders for sync_order keys
    mock_template_loader.return_value = "SYNC_SCRIPT:{sync_order_script}:SYNC_LIST:{sync_order_list}:END"

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

    # Find the step 13 call and verify default values were substituted
    step13_calls = [c for c in mock_run.call_args_list if c.kwargs.get("label") == "step13"]
    assert step13_calls, "step13 should have been called"
    instruction = step13_calls[-1].kwargs["instruction"]
    # sync_order_script should be empty string (default when no prompts modified)
    assert "SYNC_SCRIPT::SYNC_LIST:" in instruction, f"Expected empty sync_order_script, got: {instruction}"
    assert "No modules to sync" in instruction


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

    mock_template_loader.return_value = "Mocked Prompt Template"

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

    # Change-specific sync script should be at .pdd/sync_order_change.sh (not sync_order.sh)
    user_script = temp_cwd / ".pdd" / "sync_order_change.sh"
    assert user_script.exists(), "sync_order_change.sh not written to user's .pdd/"
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

    # Template with placeholder for sync_order_list
    mock_template_loader.return_value = "SYNC_LIST:{sync_order_list}:END"

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

    # Extract sync_order_list from step 13 instruction
    step13_calls = [c for c in mock_run.call_args_list if c.kwargs.get("label") == "step13"]
    assert step13_calls, "step13 should have been called"
    instruction = step13_calls[-1].kwargs["instruction"]
    # Extract the sync_list value between markers
    import re
    m = re.search(r"SYNC_LIST:(.*?):END", instruction, re.DOTALL)
    sync_list = m.group(1) if m else ""
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

    # Template with worktree_path placeholder
    mock_template_loader.return_value = "WORKTREE:{worktree_path}:END"

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

    # Verify worktree_path was substituted in step 10 instruction (first step after resume)
    step10_calls = [c for c in mock_run.call_args_list if c.kwargs.get("label") == "step10"]
    assert step10_calls, "step10 should have been called"
    instruction = step10_calls[-1].kwargs["instruction"]
    assert "{worktree_path}" not in instruction, "worktree_path not substituted in context"
    assert str(worktree_path) in instruction, f"Expected worktree path in instruction, got: {instruction}"

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
         patch("pdd.agentic_change_orchestrator.generate_sync_order_script") as mock_gen_script, \
         patch("pdd.agentic_change_orchestrator._check_existing_pr", return_value=None) as mock_check_pr:

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
            "check_pr": mock_check_pr,
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


def test_sync_order_sh_not_included_in_changed_files(mock_dependencies_dict, tmp_path):
    """sync_order.sh must NOT appear in changed_files — committing it clobbers the repo-wide script (#571)."""
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

    assert "sync_order.sh" not in files


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

    # Template with pddrc-derived key placeholders
    mock_template_loader.return_value = (
        "LANG:{language}:SRC:{source_dir}:TEST:{test_dir}:"
        "EX:{example_dir}:EXT:{ext}:LANGSUFFIX:{lang}:END"
    )

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

    # Find the step 6 call and verify pddrc context keys were substituted
    step6_calls = [c for c in mock_run.call_args_list if c.kwargs.get("label") == "step6"]
    assert step6_calls, "step6 should have been called"
    instruction = step6_calls[-1].kwargs["instruction"]

    # Verify required .pddrc-derived context keys were substituted (not literal placeholders)
    assert "{language}" not in instruction, "Context missing 'language' from .pddrc"
    assert "{source_dir}" not in instruction, "Context missing 'source_dir' from .pddrc"
    assert "{test_dir}" not in instruction, "Context missing 'test_dir' from .pddrc"
    assert "{example_dir}" not in instruction, "Context missing 'example_dir' from .pddrc"
    assert "{ext}" not in instruction, "Context missing 'ext' derived from language"
    assert "{lang}" not in instruction, "Context missing 'lang' suffix derived from language"

    # Verify actual values match .pddrc
    assert "LANG:python:" in instruction
    assert "SRC:src/:" in instruction
    assert "TEST:tests/:" in instruction
    assert "EX:examples/:" in instruction
    assert "EXT:py:" in instruction
    assert "LANGSUFFIX:_python:" in instruction


def test_orchestrator_uses_defaults_when_no_pddrc(mock_dependencies, temp_cwd):
    """
    When no .pddrc exists, orchestrator should use sensible defaults for context keys.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    # No .pddrc file - temp_cwd is empty

    # Template with pddrc-derived key placeholders
    mock_template_loader.return_value = (
        "LANG:{language}:SRC:{source_dir}:TEST:{test_dir}:"
        "EX:{example_dir}:EXT:{ext}:LANGSUFFIX:{lang}:END"
    )

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

    # Find the step 6 call and verify default context keys were substituted
    step6_calls = [c for c in mock_run.call_args_list if c.kwargs.get("label") == "step6"]
    assert step6_calls, "step6 should have been called"
    instruction = step6_calls[-1].kwargs["instruction"]

    # Even without .pddrc, context keys should have defaults (not literal placeholders)
    assert "{language}" not in instruction, "Context missing 'language' default"
    assert "{source_dir}" not in instruction, "Context missing 'source_dir' default"
    assert "{test_dir}" not in instruction, "Context missing 'test_dir' default"
    assert "{example_dir}" not in instruction, "Context missing 'example_dir' default"
    assert "{ext}" not in instruction, "Context missing 'ext' default"
    assert "{lang}" not in instruction, "Context missing 'lang' default"

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
         patch("pdd.agentic_change_orchestrator.generate_sync_order_script") as mock_gen_script, \
         patch("pdd.agentic_change_orchestrator._check_existing_pr", return_value=None) as mock_check_pr:

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
            "build_graph": mock_build_graph,
            "check_pr": mock_check_pr,
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
                step9_val = state_arg["step_outputs"].get("9", "")
                # Issue #467: failed step outputs now have "FAILED:" prefix
                if step9_val == step9_output_text or step9_val == f"FAILED: {step9_output_text}":
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


# -----------------------------------------------------------------------------
# Issue #445: Worktree restoration fails when branch is checked out
# -----------------------------------------------------------------------------

def test_setup_worktree_branch_checked_out_fails_without_fallback(tmp_path):
    """
    Test that reproduces issue #445: _setup_worktree() fails when trying to
    create a worktree for a branch that already exists and is currently checked out.

    This test demonstrates the bug where:
    1. _delete_branch() returns (False, error) because the branch is checked out
    2. The return value is ignored (line 168 in agentic_change_orchestrator.py)
    3. git worktree add -b fails with exit code 255 because the branch still exists

    This test uses real git operations to reproduce the exact failure scenario.

    Expected behavior BEFORE fix: Test FAILS (demonstrates the bug)
    Expected behavior AFTER fix: Test PASSES (worktree created using existing branch)
    """
    # Import the function under test
    from pdd.agentic_change_orchestrator import _setup_worktree

    # Create a real git repository
    git_repo = tmp_path / "test_repo"
    git_repo.mkdir()

    # Initialize git repo
    subprocess.run(["git", "init"], cwd=git_repo, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=git_repo, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=git_repo, check=True, capture_output=True)

    # Create initial commit (required for git worktree operations)
    (git_repo / "README.md").write_text("Initial commit")
    subprocess.run(["git", "add", "README.md"], cwd=git_repo, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=git_repo, check=True, capture_output=True)

    # Create the branch that will cause the bug
    issue_number = 445
    branch_name = f"change/issue-{issue_number}"
    subprocess.run(["git", "checkout", "-b", branch_name], cwd=git_repo, check=True, capture_output=True)

    # Verify we're on the branch (this is the critical condition for the bug)
    result = subprocess.run(
        ["git", "rev-parse", "--abbrev-ref", "HEAD"],
        cwd=git_repo,
        capture_output=True,
        text=True,
        check=True
    )
    current_branch = result.stdout.strip()
    assert current_branch == branch_name, f"Expected to be on {branch_name}, but on {current_branch}"

    # Call _setup_worktree() - this should fail with the current buggy code
    # because:
    # 1. Branch exists and is checked out
    # 2. _delete_branch() will fail (can't delete checked-out branch)
    # 3. Return value from _delete_branch() is ignored (bug on line 168)
    # 4. git worktree add -b will fail with exit code 255 (branch exists)
    worktree_path, error = _setup_worktree(git_repo, issue_number, quiet=True)

    # BEFORE FIX: This assertion will FAIL because worktree_path is None and error is set
    # The error message will be: "Git worktree creation failed: Command ... returned non-zero exit status 255"
    #
    # AFTER FIX: This assertion will PASS because:
    # - _setup_worktree() will detect that _delete_branch() returned (False, ...)
    # - It will fall back to: git worktree add <path> change/issue-445 (without -b)
    # - The worktree will be created successfully using the existing branch
    assert worktree_path is not None, f"Expected worktree to be created, but got error: {error}"
    assert error is None, f"Expected no error, but got: {error}"

    # Verify the worktree was actually created
    assert worktree_path.exists(), f"Worktree path {worktree_path} should exist"
    assert (worktree_path / ".git").exists(), f"Worktree should have .git file at {worktree_path}"

    # Verify the worktree is on the correct branch
    result = subprocess.run(
        ["git", "rev-parse", "--abbrev-ref", "HEAD"],
        cwd=worktree_path,
        capture_output=True,
        text=True,
        check=True
    )
    worktree_branch = result.stdout.strip()
    assert worktree_branch == branch_name, f"Worktree should be on {branch_name}, but is on {worktree_branch}"


# -----------------------------------------------------------------------------
# Issue #289: Fallback comments + consecutive failure abort + conditional state clearing
# -----------------------------------------------------------------------------

def test_fallback_comment_on_step_failure(mock_dependencies, temp_cwd):
    """
    Soft failures (single provider failure) do NOT trigger post_step_comment.
    Only hard stops and consecutive provider aborts post comments.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_post_comment = mocks["post_comment"]

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step1":
            return (False, "All agent providers failed: anthropic: Exit code 1", 0.0, "")
        if label == "step9":
            return (True, "FILES_CREATED: new.py", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/1", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=289,
        issue_author="me",
        issue_title="Fallback comment test",
        cwd=temp_cwd,
        quiet=True,
    )

    # Soft failures no longer trigger post_step_comment (prevents GitHub App re-trigger loops)
    assert mock_post_comment.call_count == 0


def test_abort_after_consecutive_provider_failures(mock_dependencies, temp_cwd):
    """
    When 3 consecutive steps fail with 'All agent providers failed',
    the workflow should abort early.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_post_comment = mocks["post_comment"]

    # All steps fail with provider failure
    mock_run.return_value = (False, "All agent providers failed: anthropic: rate limited", 0.0, "")

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=289,
        issue_author="me",
        issue_title="Abort test",
        cwd=temp_cwd,
        quiet=True,
    )

    assert success is False
    assert "Aborting" in msg
    assert "consecutive" in msg.lower() or "3" in msg
    # post_step_comment called once (on the 3rd consecutive failure that triggers abort)
    assert mock_post_comment.call_count == 1
    # Only 3 steps should have been attempted
    assert mock_run.call_count == 3


def test_consecutive_failure_counter_resets(mock_dependencies, temp_cwd):
    """
    The consecutive provider failure counter resets when a step succeeds.
    Steps 1-2 fail, step 3 succeeds, steps 4-5 fail — should NOT abort.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_post_comment = mocks["post_comment"]

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label in ("step1", "step2"):
            return (False, "All agent providers failed: anthropic: rate limited", 0.0, "")
        if label in ("step4", "step5"):
            return (False, "All agent providers failed: anthropic: timeout", 0.0, "")
        if label == "step9":
            return (True, "FILES_CREATED: new.py", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/1", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=289,
        issue_author="me",
        issue_title="Counter reset test",
        cwd=temp_cwd,
        quiet=True,
    )

    # Should NOT have aborted (counter reset at step 3 success)
    assert "Aborting" not in msg
    # Soft failures no longer trigger post_step_comment (prevents re-trigger loops)
    assert mock_post_comment.call_count == 0


def test_state_preserved_when_steps_failed(mock_dependencies, temp_cwd):
    """
    When some steps failed but the workflow still completes,
    clear_workflow_state should NOT be called (to preserve debugging info).

    Steps 1 and 2 fail (provider failures), step 3 succeeds (resets counter),
    remaining steps succeed. The workflow completes but state is preserved
    because step_outputs contain FAILED: entries.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_clear_state = mocks["clear_state"]

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        # Steps 1-2 fail (below the 3-consecutive abort threshold)
        if label in ("step1", "step2"):
            return (False, "All agent providers failed: anthropic: error", 0.0, "")
        if label == "step9":
            return (True, "FILES_CREATED: new.py", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/1", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=289,
        issue_author="me",
        issue_title="State preserve test",
        cwd=temp_cwd,
        quiet=True,
    )

    assert success is True
    # State should NOT be cleared because some steps have FAILED: prefix
    mock_clear_state.assert_not_called()


# ============================================================================
# Issue #467: Blind Resume + step_num - 1 fix
# ============================================================================


def test_resume_from_all_failed_state_reruns_from_step_1(mock_dependencies, temp_cwd):
    """
    Issue #467: When resuming from a state where all steps failed,
    the workflow should re-run from step 1, not skip past them.
    """
    mocks = mock_dependencies

    corrupted_state = {
        "last_completed_step": 6,
        "step_outputs": {
            "1": "FAILED: All agent providers failed",
            "2": "FAILED: All agent providers failed",
            "3": "FAILED: All agent providers failed",
            "4": "FAILED: All agent providers failed",
            "5": "FAILED: All agent providers failed",
            "6": "FAILED: All agent providers failed",
        },
        "total_cost": 0.0,
        "model_used": "unknown",
    }
    mocks["load_state"].return_value = (corrupted_state, None)

    executed_labels = []

    def track_run(**kwargs):
        label = kwargs.get("label", "")
        executed_labels.append(label)
        if label == "step9":
            return (True, "FILES_MODIFIED: file.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/1", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = track_run

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=467,
        issue_author="user",
        issue_title="Blind resume test",
        cwd=temp_cwd,
        quiet=True,
        use_github_state=False,
    )

    assert "step1" in executed_labels, (
        f"Step 1 should be re-executed when its cached output is FAILED, "
        f"but executed steps were: {executed_labels}. "
        f"This is the 'blind resume' bug from issue #467."
    )


def test_resume_from_partial_failure_reruns_failed_steps(mock_dependencies, temp_cwd):
    """
    Issue #467: When resuming from state where steps 1-4 succeeded but 5-6 failed,
    resume should re-run from step 5, not step 7.
    """
    mocks = mock_dependencies

    corrupted_state = {
        "last_completed_step": 6,
        "step_outputs": {
            "1": "No duplicates",
            "2": "Not implemented yet",
            "3": "Research done",
            "4": "Requirements clear",
            "5": "FAILED: All agent providers failed",
            "6": "FAILED: All agent providers failed",
        },
        "total_cost": 0.4,
        "model_used": "gpt-4",
    }
    mocks["load_state"].return_value = (corrupted_state, None)

    executed_labels = []

    def track_run(**kwargs):
        label = kwargs.get("label", "")
        executed_labels.append(label)
        if label == "step9":
            return (True, "FILES_MODIFIED: file.py", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/1", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = track_run

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=467,
        issue_author="user",
        issue_title="Partial failure test",
        cwd=temp_cwd,
        quiet=True,
        use_github_state=False,
    )

    # Steps 1-4 should be skipped
    assert "step1" not in executed_labels, "Step 1 succeeded and should not be re-run"
    assert "step2" not in executed_labels, "Step 2 succeeded and should not be re-run"
    assert "step3" not in executed_labels, "Step 3 succeeded and should not be re-run"
    assert "step4" not in executed_labels, "Step 4 succeeded and should not be re-run"
    # Step 5 should be re-run
    assert "step5" in executed_labels, (
        f"Step 5 should be re-executed because its cached output is FAILED, "
        f"but executed steps were: {executed_labels}."
    )


def test_step9_no_files_marks_failed_not_step_num_minus_1(mock_dependencies, temp_cwd):
    """
    Issue #467: Step 9 with no changed files should mark the step as FAILED
    and NOT use the step_num - 1 formula for last_completed_step.
    """
    mocks = mock_dependencies
    mock_save = mocks["save_state"]

    saved_states = []

    def capture_save(cwd, issue_number, wf_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        saved_states.append(dict(state))
        return None

    mock_save.side_effect = capture_save

    def run_side_effect(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            # Step 9 succeeds but reports no FILES_CREATED/MODIFIED
            return (True, "No files changed", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = run_side_effect

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=467,
        issue_author="user",
        issue_title="No files test",
        cwd=temp_cwd,
        quiet=True,
        use_github_state=False,
    )

    assert not success
    assert "no file changes" in msg.lower()

    # Find the state saved when step 9 early-returns
    step9_states = [s for s in saved_states if "9" in s.get("step_outputs", {})]
    if step9_states:
        last = step9_states[-1]
        assert last["step_outputs"]["9"].startswith("FAILED:"), (
            "Step 9 with no files should be marked as FAILED, not stored as raw output"
        )
        # last_completed_step should be 8 (last successful step), NOT step_num - 1 = 8
        # which happens to be the same value but for the right reason (step 8 succeeded)
        assert last["last_completed_step"] == 8, (
            f"last_completed_step should be 8 (last success), got {last['last_completed_step']}"
        )


# =============================================================================
# Issue #756: Existing-PR Guard + post_step_comment Restriction
# =============================================================================

def test_check_existing_pr_returns_url_when_pr_exists():
    """_check_existing_pr returns the PR URL when an open PR exists."""
    with patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_sub:
        mock_sub.return_value.returncode = 0
        mock_sub.return_value.stdout = json.dumps([
            {"url": "https://github.com/owner/repo/pull/42"}
        ])
        result = _check_existing_pr("owner", "repo", 10)
    assert result == "https://github.com/owner/repo/pull/42"


def test_check_existing_pr_returns_none_when_no_pr():
    """_check_existing_pr returns None when no open PR exists."""
    with patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_sub:
        mock_sub.return_value.returncode = 0
        mock_sub.return_value.stdout = "[]"
        result = _check_existing_pr("owner", "repo", 10)
    assert result is None


def test_check_existing_pr_returns_none_on_subprocess_error():
    """_check_existing_pr returns None when gh CLI fails."""
    with patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_sub:
        mock_sub.return_value.returncode = 1
        mock_sub.return_value.stdout = ""
        result = _check_existing_pr("owner", "repo", 10)
    assert result is None


def test_check_existing_pr_returns_none_on_timeout():
    """_check_existing_pr returns None on subprocess timeout."""
    with patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_sub:
        mock_sub.side_effect = subprocess.TimeoutExpired("gh", 30)
        result = _check_existing_pr("owner", "repo", 10)
    assert result is None


def test_orchestrator_returns_early_when_pr_exists(mock_dependencies, temp_cwd):
    """Orchestrator returns early without running any steps when PR already exists."""
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_check_pr = mocks["check_pr"]

    mock_check_pr.return_value = "https://github.com/owner/repo/pull/99"

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=756,
        issue_author="me",
        issue_title="Existing PR",
        cwd=temp_cwd,
        quiet=True,
    )

    assert success is True
    assert "PR already exists" in msg
    assert "https://github.com/owner/repo/pull/99" in msg
    assert cost == 0.0
    # No steps should have been executed
    mock_run.assert_not_called()


def test_post_step_comment_called_on_hard_stop(mock_dependencies, temp_cwd):
    """post_step_comment IS called when a hard stop condition is triggered."""
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_post_comment = mocks["post_comment"]

    # Step 1 triggers a hard stop (duplicate)
    mock_run.return_value = (False, "This is a Duplicate of #42", 0.1, "gpt-4")

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=756,
        issue_author="me",
        issue_title="Hard stop test",
        cwd=temp_cwd,
        quiet=True,
    )

    assert success is False
    assert "duplicate" in msg.lower()
    # Hard stop should trigger a comment
    assert mock_post_comment.call_count == 1


def test_post_step_comment_not_called_on_soft_failure(mock_dependencies, temp_cwd):
    """post_step_comment is NOT called on soft failures (prevents GitHub App re-trigger)."""
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_post_comment = mocks["post_comment"]

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step3":
            return (False, "Some transient failure", 0.0, "gpt-4")
        if label == "step9":
            return (True, "FILES_CREATED: new.py", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Arch updated", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/1", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=756,
        issue_author="me",
        issue_title="Soft failure test",
        cwd=temp_cwd,
        quiet=True,
    )

    # Soft failure should NOT post a comment
    assert mock_post_comment.call_count == 0


def test_post_step_comment_called_on_provider_abort(mock_dependencies, temp_cwd):
    """post_step_comment IS called when consecutive provider failures trigger abort."""
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_post_comment = mocks["post_comment"]

    mock_run.return_value = (False, "All agent providers failed: timeout", 0.0, "")

    success, msg, cost, model, files = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=756,
        issue_author="me",
        issue_title="Provider abort test",
        cwd=temp_cwd,
        quiet=True,
    )

    assert success is False
    assert "Aborting" in msg
    # Comment posted once (on the 3rd consecutive failure)
    assert mock_post_comment.call_count == 1


def test_step4_clarification_hard_stop_with_stop_condition_tag(mock_dependencies, temp_cwd):
    """
    Test that Step 4 hard stop uses STOP_CONDITION tag, not loose string matching.
    A casual mention of 'Clarification Needed' without the tag should NOT stop the workflow.
    The strict 'STOP_CONDITION: Clarification Needed' tag SHOULD stop it.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    # 1. Test casual mention (should NOT stop)
    def side_effect_run_loose(**kwargs):
        label = kwargs.get("label", "")
        if label == "step4":
            return (True, "Just mentioning Clarification Needed casually.", 0.1, "gpt-4")
        if label == "step9":
            return (True, "Implementation done. FILES_MODIFIED: file_a.py", 0.5, "gpt-4")
        if label == "step10":
            return (True, "Architecture updated. ARCHITECTURE_FILES_MODIFIED: arch.json", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/123", 0.2, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run_loose
    success, msg, cost, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url", issue_content="content", repo_owner="owner", repo_name="repo",
        issue_number=773, issue_author="me", issue_title="title", cwd=temp_cwd, verbose=False
    )
    assert success is True, "Failed: Workflow improperly stopped on casual mention without STOP_CONDITION tag"

    # 2. Test strict tag (should STOP)
    mocks["save_state"].reset_mock()
    mocks["console"].print.reset_mock()
    mocks["post_comment"].reset_mock()
    mock_run.reset_mock()

    def side_effect_run_strict(**kwargs):
        label = kwargs.get("label", "")
        if label == "step4":
            return (True, "STOP_CONDITION: Clarification Needed", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run_strict
    success, msg, cost, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url", issue_content="content", repo_owner="owner", repo_name="repo",
        issue_number=773, issue_author="me", issue_title="title", cwd=temp_cwd, verbose=False
    )

    assert success is False
    assert "Stopped at step 4" in msg
    assert mock_run.call_count == 4
    mocks["save_state"].assert_called()
    assert mocks["save_state"].call_args[0][3]["last_completed_step"] == 3
    mocks["console"].print.assert_any_call("[yellow]Investigation stopped at Step 4: Clarification needed[/yellow]")


def test_step7_architectural_decision_hard_stop_with_stop_condition_tag(mock_dependencies, temp_cwd):
    """
    Test that Step 7 hard stop uses STOP_CONDITION tag, not loose string matching.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    # 1. Test casual mention (should NOT stop)
    def side_effect_run_loose(**kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "Mentioning Architectural Decision Needed casually.", 0.1, "gpt-4")
        if label == "step9":
            return (True, "Implementation done. FILES_MODIFIED: file_a.py", 0.5, "gpt-4")
        if label == "step10":
            return (True, "Architecture updated. ARCHITECTURE_FILES_MODIFIED: arch.json", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/123", 0.2, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run_loose
    success, msg, cost, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url", issue_content="content", repo_owner="owner", repo_name="repo",
        issue_number=773, issue_author="me", issue_title="title", cwd=temp_cwd, verbose=False
    )
    assert success is True, "Failed: Workflow improperly stopped on casual mention without STOP_CONDITION tag"

    # 2. Test strict tag
    mocks["save_state"].reset_mock()
    mock_run.reset_mock()
    mocks["console"].print.reset_mock()

    def side_effect_run_strict(**kwargs):
        label = kwargs.get("label", "")
        if label == "step7":
            return (True, "STOP_CONDITION: Architectural Decision Needed", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run_strict
    success, msg, cost, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url", issue_content="content", repo_owner="owner", repo_name="repo",
        issue_number=773, issue_author="me", issue_title="title", cwd=temp_cwd, verbose=False
    )

    assert success is False
    assert "Stopped at step 7" in msg
    assert mock_run.call_count == 7
    mocks["save_state"].assert_called()


def test_step10_postcheck_preserves_existing_architecture_params(mock_dependencies, temp_cwd):
    """Step 10 direct architecture edits should not be able to silently drop params."""
    mocks = mock_dependencies
    mock_run = mocks["run"]

    issue_number = 825
    worktree_path = temp_cwd / ".pdd" / "worktrees" / f"change-issue-{issue_number}"

    original_architecture = [
        {
            "filename": "orchestrator_python.prompt",
            "filepath": "pdd/orchestrator.py",
            "reason": "Orchestrates e2e fix",
            "dependencies": [],
            "priority": 1,
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {
                            "name": "run_agentic_e2e_fix_orchestrator",
                            "signature": "(issue_url, issue_content, use_github_state, protect_tests)",
                            "returns": "Dict",
                        }
                    ]
                },
            },
        }
    ]

    def mock_setup_worktree(cwd, issue_num, quiet):
        prompts_dir = worktree_path / "prompts"
        prompts_dir.mkdir(parents=True, exist_ok=True)
        (prompts_dir / "orchestrator_python.prompt").write_text(
            "% orchestrator prompt",
            encoding="utf-8",
        )
        (worktree_path / "architecture.json").write_text(
            json.dumps(original_architecture, indent=2),
            encoding="utf-8",
        )
        return worktree_path, None

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        cwd = kwargs.get("cwd")
        if label == "step9":
            return (
                True,
                "FILES_MODIFIED: prompts/orchestrator_python.prompt",
                0.1,
                "gpt-4",
            )
        if label == "step10":
            broken_architecture = [
                {
                    "filename": "orchestrator_python.prompt",
                    "filepath": "pdd/orchestrator.py",
                    "reason": "Orchestrates e2e fix",
                    "dependencies": [],
                    "priority": 1,
                    "interface": {
                        "type": "module",
                        "module": {
                            "functions": [
                                {
                                    "name": "run_agentic_e2e_fix_orchestrator",
                                    "signature": "(issue_url, issue_content, use_github_state, ci_retries = 3, skip_ci = False)",
                                    "returns": "Dict",
                                }
                            ]
                        },
                    },
                }
            ]
            (Path(cwd) / "architecture.json").write_text(
                json.dumps(broken_architecture, indent=2),
                encoding="utf-8",
            )
            return (
                True,
                "Architecture updated. ARCHITECTURE_FILES_MODIFIED: prompts/orchestrator_python.prompt, architecture.json",
                0.1,
                "gpt-4",
            )
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, "PR Created: https://github.com/owner/repo/pull/123", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    with patch("pdd.agentic_change_orchestrator._setup_worktree", side_effect=mock_setup_worktree):
        success, msg, cost, model, files = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="content",
            repo_owner="owner",
            repo_name="repo",
            issue_number=issue_number,
            issue_author="me",
            issue_title="Preserve params",
            cwd=temp_cwd,
            quiet=True,
        )

    assert success is True
    repaired = json.loads((worktree_path / "architecture.json").read_text(encoding="utf-8"))
    signature = repaired[0]["interface"]["module"]["functions"][0]["signature"]
    assert "protect_tests" in signature
    assert "ci_retries" in signature
    assert "skip_ci" in signature
    saved_step10_outputs = [
        call.args[3]["step_outputs"].get("10", "")
        for call in mocks["save_state"].call_args_list
        if "step_outputs" in call.args[3]
    ]
    assert any(
        "ORCHESTRATOR_POSTCHECK_WARNINGS:" in output
        and "protect_tests" in output
        for output in saved_step10_outputs
    )


def test_hard_stop_configuration_quiet_mode(mock_dependencies, temp_cwd):
    """
    Test that hard stop works correctly in quiet mode (no console output).
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    def side_effect_run_strict(**kwargs):
        label = kwargs.get("label", "")
        if label == "step4":
            return (True, "STOP_CONDITION: Clarification Needed", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run_strict
    success, msg, cost, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url", issue_content="content", repo_owner="owner", repo_name="repo",
        issue_number=773, issue_author="me", issue_title="title", cwd=temp_cwd, quiet=True
    )

    assert success is False
    assert "Stopped at step 4" in msg
    assert mock_run.call_count == 4
    mocks["save_state"].assert_called()
    assert mocks["save_state"].call_args[0][3]["last_completed_step"] == 3

    for call in mocks["console"].print.mock_calls:
        assert "[yellow]Investigation stopped at step 4" not in str(call.args)


# -----------------------------------------------------------------------------
# Unit Tests for _check_hard_stop (Issue #773)
# -----------------------------------------------------------------------------

def test_check_hard_stop_step4_requires_stop_condition_tag():
    """
    _check_hard_stop should only trigger for Step 4 when the output contains
    'STOP_CONDITION: Clarification Needed', not a casual mention.
    """
    from pdd.agentic_change_orchestrator import _check_hard_stop

    # Casual mention should NOT trigger hard stop
    result = _check_hard_stop(4, "Just mentioning Clarification Needed casually.")
    assert result is None, (
        "Bug #773: _check_hard_stop falsely triggers on casual mention of "
        "'Clarification Needed' without STOP_CONDITION tag"
    )

    # Strict tag SHOULD trigger hard stop
    result = _check_hard_stop(4, "I posted the comment. STOP_CONDITION: Clarification Needed")
    assert result is not None, (
        "_check_hard_stop should trigger when STOP_CONDITION: Clarification Needed is present"
    )


def test_check_hard_stop_step7_requires_stop_condition_tag():
    """
    _check_hard_stop should only trigger for Step 7 when the output contains
    'STOP_CONDITION: Architectural Decision Needed', not a casual mention.
    """
    from pdd.agentic_change_orchestrator import _check_hard_stop

    # Casual mention should NOT trigger hard stop
    result = _check_hard_stop(7, "Mentioning Architectural Decision Needed in passing.")
    assert result is None, (
        "Bug #773: _check_hard_stop falsely triggers on casual mention of "
        "'Architectural Decision Needed' without STOP_CONDITION tag"
    )

    # Strict tag SHOULD trigger hard stop
    result = _check_hard_stop(7, "STOP_CONDITION: Architectural Decision Needed")
    assert result is not None, (
        "_check_hard_stop should trigger when STOP_CONDITION: Architectural Decision Needed is present"
    )


# -----------------------------------------------------------------------------
# Bug #784: _check_hard_stop improvements
# -----------------------------------------------------------------------------

def test_check_hard_stop_case_insensitive_substring_matching():
    """Non-clarification steps use case-insensitive substring matching."""
    from pdd.agentic_change_orchestrator import _check_hard_stop

    # Step 2: "Already Implemented" (case-insensitive)
    assert _check_hard_stop(2, "already implemented") is not None
    assert _check_hard_stop(2, "ALREADY IMPLEMENTED") is not None
    assert _check_hard_stop(2, "Already Implemented") is not None

    # Step 6: "No Dev Units Found" (case-insensitive)
    assert _check_hard_stop(6, "no dev units found") is not None
    assert _check_hard_stop(6, "NO DEV UNITS FOUND") is not None

    # Step 8: "No Changes Required" (case-insensitive)
    assert _check_hard_stop(8, "no changes required") is not None
    assert _check_hard_stop(8, "NO CHANGES REQUIRED") is not None


def test_check_hard_stop_universal_stop_condition_tag():
    """Any step can trigger via STOP_CONDITION: tag as a universal fallback."""
    from pdd.agentic_change_orchestrator import _check_hard_stop

    # Step 3 has no specific handler — universal fallback should catch it
    result = _check_hard_stop(3, "STOP_CONDITION: Custom reason for stopping")
    assert result == "Custom reason for stopping"

    # Step 5 has no specific handler either
    result = _check_hard_stop(5, "STOP_CONDITION: Unexpected issue found")
    assert result == "Unexpected issue found"


def test_check_hard_stop_empty_and_none_output():
    """_check_hard_stop handles empty and None output without error."""
    from pdd.agentic_change_orchestrator import _check_hard_stop

    assert _check_hard_stop(1, "") is None
    assert _check_hard_stop(1, None) is None
    assert _check_hard_stop(4, "") is None
    assert _check_hard_stop(4, None) is None


def test_check_hard_stop_case_insensitive_fallbacks():
    """Substring fallbacks for steps 1, 2, 6, 8, 9 are case-insensitive."""
    from pdd.agentic_change_orchestrator import _check_hard_stop

    assert _check_hard_stop(1, "DUPLICATE OF #42") is not None
    assert _check_hard_stop(1, "duplicate of #42") is not None
    assert _check_hard_stop(2, "ALREADY IMPLEMENTED") is not None
    assert _check_hard_stop(6, "NO DEV UNITS FOUND") is not None
    assert _check_hard_stop(8, "NO CHANGES REQUIRED") is not None
    assert _check_hard_stop(9, "FAIL: build error") is not None


def test_step4_prompt_has_stop_condition_instruction():
    """Step 4 prompt must instruct LLM to output STOP_CONDITION line prefix."""
    prompt_path = Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_change_step4_clarify_LLM.prompt"
    prompt_content = prompt_path.read_text()
    assert "STOP_CONDITION: Clarification needed" in prompt_content
    assert "CRITICAL" in prompt_content


def test_step4_stop_with_stop_condition_prefix(mock_dependencies, temp_cwd):
    """Orchestrator should stop at step 4 when STOP_CONDITION line is in output."""
    mocks = mock_dependencies

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step4":
            return (True, "I posted clarification questions.\nSTOP_CONDITION: Clarification needed", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_change_orchestrator(
        issue_url="https://github.com/o/r/issues/900",
        issue_content="Vague feature request",
        repo_owner="o",
        repo_name="r",
        issue_number=900,
        issue_author="user",
        issue_title="Feature",
        cwd=temp_cwd,
        quiet=True,
    )

    assert success is False
    assert "Stopped at step 4" in msg
    assert mocks["run"].call_count == 4


def test_step4_clarification_saves_step_minus_one(mock_dependencies, temp_cwd):
    """When step 4 stops for clarification, last_completed_step should be 3 (step-1)."""
    mocks = mock_dependencies

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step4":
            return (True, "STOP_CONDITION: Clarification needed", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    with patch("pdd.agentic_change_orchestrator._fetch_issue_updated_at", return_value="2025-01-01T00:00:00Z"):
        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="https://github.com/o/r/issues/900",
            issue_content="Feature",
            repo_owner="o",
            repo_name="r",
            issue_number=900,
            issue_author="user",
            issue_title="Feature",
            cwd=temp_cwd,
            quiet=True,
        )

    assert success is False
    # save_workflow_state(cwd, issue_number, workflow_type, state, ...)
    final_state = mocks["save_state"].call_args[0][3]
    assert final_state["last_completed_step"] == 3, (
        "Clarification stop at step 4 should save last_completed_step=3 for resume"
    )


def test_fetch_issue_updated_at_called_on_clarification(mock_dependencies, temp_cwd):
    """Bug #784: issue_updated_at is refreshed after clarification stops."""
    mocks = mock_dependencies
    mock_run = mocks["run"]

    def side_effect(**kwargs):
        label = kwargs.get("label", "")
        if label == "step4":
            return (True, "STOP_CONDITION: Clarification Needed", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    with patch("pdd.agentic_change_orchestrator._fetch_issue_updated_at",
               return_value="2026-03-08T12:00:00Z") as mock_fetch:
        success, msg, _, _, _ = run_agentic_change_orchestrator(
            issue_url="http://url", issue_content="content", repo_owner="owner", repo_name="repo",
            issue_number=784, issue_author="me", issue_title="title",
            issue_updated_at="2026-03-08T10:00:00Z",
            cwd=temp_cwd, verbose=False
        )
        assert success is False
        mock_fetch.assert_called_once_with("owner", "repo", 784)
        saved_state = mocks["save_state"].call_args[0][3]
        assert saved_state["issue_updated_at"] == "2026-03-08T12:00:00Z", (
            "Bug #784: issue_updated_at should be refreshed after clarification"
        )


# -----------------------------------------------------------------------------
# Bug #571: sync_order.sh clobber prevention
# -----------------------------------------------------------------------------

def test_sync_order_does_not_clobber_existing_sync_order_sh(mock_dependencies, temp_cwd):
    """
    Bug #571: The orchestrator must NOT overwrite an existing sync_order.sh in
    the user's CWD. The repo-wide sync_order.sh may contain the full module list
    (e.g. 94 modules). Writing only affected modules (e.g. 1 module) into that
    file destroys the original.

    The fix: write to .pdd/sync_order_change.sh instead.
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]
    mock_template_loader = mocks["template_loader"]

    issue_number = 571
    worktree_path = temp_cwd / ".pdd" / "worktrees" / f"change-issue-{issue_number}"

    # Pre-populate a repo-wide sync_order.sh with 94 modules
    original_content = "#!/bin/bash\n# Full repo sync order (94 modules)\npdd sync module_1\npdd sync module_2\n"
    existing_script = temp_cwd / "sync_order.sh"
    existing_script.write_text(original_content, encoding="utf-8")

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
    mock_template_loader.return_value = "Mocked Prompt Template"

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

    # The original sync_order.sh must be UNTOUCHED
    assert existing_script.read_text(encoding="utf-8") == original_content, (
        "Bug #571: orchestrator clobbered the repo-wide sync_order.sh with affected-only modules"
    )

    # The change-specific script should be at .pdd/sync_order_change.sh
    change_script = temp_cwd / ".pdd" / "sync_order_change.sh"
    assert change_script.exists(), (
        "Bug #571: change-specific sync script should be at .pdd/sync_order_change.sh"
    )
    change_content = change_script.read_text(encoding="utf-8")
    assert "pdd sync" in change_content


def test_sync_order_sh_not_staged_into_pr(mock_dependencies_dict, tmp_path):
    """
    Bug #571: sync_order.sh must NOT appear in the PR's changed_files list.
    Committing it into the PR replaces the repo-wide script with an
    affected-only stub.
    """
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

    assert "sync_order.sh" not in files, (
        "Bug #571: sync_order.sh must not be staged into the PR — it clobbers the repo-wide script"
    )


# -----------------------------------------------------------------------------
# Review loop: case-insensitive / semantic "No Issues Found" detection
# (Same class of bug as #868 / #865: LLMs don't reliably emit exact tokens)
# -----------------------------------------------------------------------------

def test_review_loop_exits_on_lowercase_no_issues(mock_dependencies, temp_cwd):
    """
    The LLM may return 'no issues found' (lowercase) instead of the
    exact 'No Issues Found'. The loop should still exit.
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
            # LLM returns lowercase variant
            return (True, "**Status:** no issues found\n\nAll checks passed.", 0.1, "gpt-4")
        elif label == "step13":
            return (True, "PR Created", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, _, _, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=900,
        issue_author="me",
        issue_title="Case insensitive exit",
        cwd=temp_cwd
    )

    assert success is True
    step11_calls = [c for c in mock_run.call_args_list if c.kwargs.get('label', '').startswith('step11')]
    assert len(step11_calls) == 1, (
        f"Expected 1 step11 call (early exit), got {len(step11_calls)}"
    )
    step12_calls = [c for c in mock_run.call_args_list if c.kwargs.get('label', '').startswith('step12')]
    assert len(step12_calls) == 0, (
        f"Step 12 should not run when Step 11 found no issues, got {len(step12_calls)} calls"
    )


def test_review_loop_exits_on_status_no_issues_variant(mock_dependencies, temp_cwd):
    """
    LLM may embed the status in markdown like '**Status:** No Issues Found'
    but the raw output might only contain 'Status: No Issues Found'.
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
            return (True, "Review complete. Status: no issues found. All files validated.", 0.1, "gpt-4")
        elif label == "step13":
            return (True, "PR Created", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, _, _, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=901,
        issue_author="me",
        issue_title="Status variant exit",
        cwd=temp_cwd
    )

    assert success is True
    step11_calls = [c for c in mock_run.call_args_list if c.kwargs.get('label', '').startswith('step11')]
    assert len(step11_calls) == 1
    step12_calls = [c for c in mock_run.call_args_list if c.kwargs.get('label', '').startswith('step12')]
    assert len(step12_calls) == 0


# -----------------------------------------------------------------------------
# Impacted tests listed in PR body (#377 Bug B)
# -----------------------------------------------------------------------------

def test_orchestrator_populates_impacted_tests_context(mock_dependencies, temp_cwd):
    """
    After Step 10, the orchestrator should identify test files for
    affected modules and pass them to Step 13 via context['impacted_tests'].
    """
    mocks = mock_dependencies
    mock_run = mocks["run"]

    # Create a .pddrc so the orchestrator can find test dir
    pddrc = temp_cwd / ".pddrc"
    pddrc.write_text(
        "source_dir: pdd\ntest_dir: tests\nprompts_dir: prompts\n"
        "example_dir: context\nlanguage: python\n"
    )

    # Create test files that correspond to modified modules
    tests_dir = temp_cwd / "tests"
    tests_dir.mkdir()
    (tests_dir / "test_agentic_bug_orchestrator.py").write_text("# test")
    (tests_dir / "test_agentic_bug_step10_prompt.py").write_text("# test")

    # Create architecture.json with dependency info
    arch = temp_cwd / "architecture.json"
    arch.write_text(json.dumps([
        {
            "filename": "agentic_bug_orchestrator_python.prompt",
            "filepath": "pdd/agentic_bug_orchestrator.py",
            "reason": "Orchestrator",
            "description": "Bug orchestrator",
            "dependencies": ["agentic_common_python.prompt"],
            "priority": 1,
            "tags": ["module"],
        }
    ]))

    # Use a template with {impacted_tests} placeholder so substitution works
    def template_loader(name):
        if name == "agentic_change_step13_create_pr_LLM":
            return "Create PR. Impacted tests: {impacted_tests}"
        return "Mocked Prompt Template"

    mocks["template_loader"].side_effect = template_loader

    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "FILES_MODIFIED: pdd/prompts/agentic_bug_orchestrator_python.prompt", 0.1, "gpt-4")
        elif label == "step10":
            return (True, "ARCHITECTURE_FILES_MODIFIED: architecture.json", 0.1, "gpt-4")
        elif label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        elif label == "step13":
            return (True, "PR Created", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mock_run.side_effect = side_effect_run

    success, _, _, _, _ = run_agentic_change_orchestrator(
        issue_url="http://url",
        issue_content="content",
        repo_owner="owner",
        repo_name="repo",
        issue_number=902,
        issue_author="me",
        issue_title="Impacted tests",
        cwd=temp_cwd
    )

    assert success is True

    # Find the step13 call and check its prompt contains impacted test info
    step13_call = [c for c in mock_run.call_args_list if c.kwargs.get('label', '') == 'step13']
    assert len(step13_call) == 1
    step13_prompt = step13_call[0].kwargs.get('instruction', '')
    assert "test_agentic_bug_orchestrator" in step13_prompt, (
        f"Step 13 prompt should contain impacted test file paths. Got: {step13_prompt}"
    )

# ---------------------------------------------------------------------------
# BUG: _review_loop_no_issues doesn't exist yet — the review loop uses a
# brittle exact-match ("No Issues Found" in s11_output) that misses
# semantic variants the LLM commonly produces, causing 4 wasted iterations.
# These tests define the correct behavior for the function we need to create.
# ---------------------------------------------------------------------------

class TestReviewLoopNoIssues:
    """Tests for _review_loop_no_issues: must detect the exact phrase AND
    common semantic variants, case-insensitively."""

    def test_exact_phrase(self):
        assert _review_loop_no_issues("No Issues Found") is True

    def test_case_insensitive(self):
        assert _review_loop_no_issues("no issues found") is True
        assert _review_loop_no_issues("NO ISSUES FOUND") is True

    def test_embedded_in_markdown(self):
        output = "## Step 11: Issue Identification\n\n**Status:** No Issues Found\n\n### Review Summary"
        assert _review_loop_no_issues(output) is True

    def test_variant_no_issues_identified(self):
        assert _review_loop_no_issues("After review, no issues identified in the codebase.") is True

    def test_variant_no_issues_detected(self):
        assert _review_loop_no_issues("No issues detected during this iteration.") is True

    def test_variant_all_checks_passed(self):
        assert _review_loop_no_issues("All checks passed. The code looks correct.") is True

    def test_variant_everything_looks_good(self):
        assert _review_loop_no_issues("Everything looks good — no changes needed.") is True

    def test_variant_no_problems_found(self):
        assert _review_loop_no_issues("No problems found in the modified files.") is True

    def test_variant_no_issues_remain(self):
        assert _review_loop_no_issues("No issues remain after the previous fixes.") is True

    def test_variant_no_remaining_issues(self):
        assert _review_loop_no_issues("There are no remaining issues to address.") is True

    def test_variant_no_issues_to_fix(self):
        assert _review_loop_no_issues("No issues to fix in this iteration.") is True

    def test_issues_found_returns_false(self):
        assert _review_loop_no_issues("Issues Found: syntax error on line 42") is False

    def test_issues_present_returns_false(self):
        assert _review_loop_no_issues("There are 3 issues that need fixing.") is False

    def test_empty_output_returns_false(self):
        assert _review_loop_no_issues("") is False


class TestReviewLoopEarlyExit:
    """BUG: the review loop currently uses exact-match and misses variant
    phrases, running all 5 iterations. After the fix, a variant phrase like
    "no issues identified" must cause early exit (2 calls, not 10)."""

    def test_exits_on_variant_phrase(self, mock_dependencies_dict, tmp_path):
        mocks = mock_dependencies_dict
        existing_state = {
            "last_completed_step": 10,
            "step_outputs": {str(i): "out" for i in range(1, 11)},
            "worktree_path": str(tmp_path / "wt"),
        }
        existing_state["step_outputs"]["9"] = "FILES_CREATED: foo.prompt"
        mocks["load"].return_value = (existing_state, 123)

        # Step 11 returns a variant phrase — should trigger early exit
        responses = [
            (True, "After thorough review, no issues identified.", 0.1, "gpt-4"),  # step11_iter1
            (True, "PR Created", 0.1, "gpt-4"),  # step13
        ]
        mocks["run"].side_effect = responses

        with patch("pathlib.Path.exists", return_value=True):
            success, msg, cost, model, files = run_agentic_change_orchestrator(
                issue_url="http://issue", issue_content="Fix bug",
                repo_owner="owner", repo_name="repo", issue_number=1,
                issue_author="me", issue_title="Bug Fix", cwd=tmp_path, quiet=True,
            )

        assert success is True
        # Only 2 calls: step11_iter1 (no issues) + step13 (PR)
        assert mocks["run"].call_count == 2
        labels = [c.kwargs.get("label") for c in mocks["run"].call_args_list]
        assert "step11_iter1" in labels
        assert "step13" in labels
        assert "step12_iter1" not in labels


# ---------------------------------------------------------------------------
# BUG: _setup_worktree destroys the remote branch on re-runs, losing
# changes from prior runs that the current run doesn't rediscover.
# These tests define the correct behavior: fetch and reuse remote branch.
# ---------------------------------------------------------------------------

class TestSetupWorktreePreservesRemote:
    """Tests that _setup_worktree reuses remote branch content when available,
    instead of always creating a fresh branch from HEAD."""

    def test_creates_from_remote_when_available(self, tmp_path):
        from pdd.agentic_change_orchestrator import _setup_worktree

        calls = []

        def mock_subprocess_run(cmd, **kwargs):
            cmd_list = cmd if isinstance(cmd, list) else cmd.split()
            cmd_str = " ".join(cmd_list)
            calls.append(cmd_str)
            m = MagicMock()
            m.stdout = str(tmp_path)
            m.returncode = 0

            # git rev-parse --show-toplevel
            if "rev-parse" in cmd_str and "--show-toplevel" in cmd_str:
                m.stdout = str(tmp_path)
                return m
            # git fetch origin change/issue-99
            if "fetch" in cmd_str and "change/issue-99" in cmd_str:
                return m
            # git show-ref --verify refs/remotes/origin/change/issue-99
            if "show-ref" in cmd_str and "remotes" in cmd_str:
                return m  # remote exists
            # git show-ref --verify refs/heads/change/issue-99 (local branch check)
            if "show-ref" in cmd_str and "refs/heads" in cmd_str:
                raise subprocess.CalledProcessError(1, cmd)  # no local branch
            # git worktree add -b ... origin/change/issue-99
            if "worktree" in cmd_str and "add" in cmd_str:
                wt_dir = None
                for i, c in enumerate(cmd_list):
                    if c == "-b" and i + 2 < len(cmd_list):
                        wt_dir = cmd_list[i + 2]
                        break
                if wt_dir:
                    Path(wt_dir).mkdir(parents=True, exist_ok=True)
                return m
            return m

        with patch("subprocess.run", side_effect=mock_subprocess_run):
            wt_path, err = _setup_worktree(tmp_path, 99, quiet=True)

        assert err is None
        # Verify the worktree was created from the remote ref, not HEAD
        worktree_add_calls = [c for c in calls if "worktree" in c and "add" in c]
        assert len(worktree_add_calls) == 1
        assert "origin/change/issue-99" in worktree_add_calls[0]

    def test_creates_from_head_when_no_remote(self, tmp_path):
        from pdd.agentic_change_orchestrator import _setup_worktree

        calls = []

        def mock_subprocess_run(cmd, **kwargs):
            cmd_list = cmd if isinstance(cmd, list) else cmd.split()
            cmd_str = " ".join(cmd_list)
            calls.append(cmd_str)
            m = MagicMock()
            m.stdout = str(tmp_path)
            m.returncode = 0

            if "rev-parse" in cmd_str and "--show-toplevel" in cmd_str:
                m.stdout = str(tmp_path)
                return m
            # git fetch fails — no remote branch
            if "fetch" in cmd_str:
                raise subprocess.CalledProcessError(1, cmd)
            # No local branch either
            if "show-ref" in cmd_str and "refs/heads" in cmd_str:
                raise subprocess.CalledProcessError(1, cmd)
            if "worktree" in cmd_str and "add" in cmd_str:
                wt_dir = None
                for i, c in enumerate(cmd_list):
                    if c == "-b" and i + 2 < len(cmd_list):
                        wt_dir = cmd_list[i + 2]
                        break
                if wt_dir:
                    Path(wt_dir).mkdir(parents=True, exist_ok=True)
                return m
            return m

        with patch("subprocess.run", side_effect=mock_subprocess_run):
            wt_path, err = _setup_worktree(tmp_path, 99, quiet=True)

        assert err is None
        worktree_add_calls = [c for c in calls if "worktree" in c and "add" in c]
        assert len(worktree_add_calls) == 1
        # Must NOT use origin/change/issue-99 (no remote branch to reuse)
        assert "origin/change/issue-99" not in worktree_add_calls[0]

# -----------------------------------------------------------------------------
# _scope_architecture_to_changed_files Tests (TDD for Issue #922)
# -----------------------------------------------------------------------------

class TestScopeArchitectureToChangedFiles:
    """Tests for reverting out-of-scope architecture.json mutations after Step 10."""

    def test_out_of_scope_entries_reverted(self, tmp_path):
        """Entries for files NOT in changed_files must be reverted to previous state."""
        previous = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py",
             "reason": "Original reason", "interface": {"type": "module", "module": {"functions": [{"name": "foo", "signature": "(x: int)", "returns": "str"}]}}},
            {"filename": "bar_python.prompt", "filepath": "pdd/bar.py",
             "reason": "Bar original", "interface": {"type": "module", "module": {"functions": [{"name": "bar", "signature": "(a: str, b: int)", "returns": "bool"}]}}},
        ]
        # LLM mutated bar's reason and signature even though only foo was changed
        current = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py",
             "reason": "Updated reason for foo", "interface": {"type": "module", "module": {"functions": [{"name": "foo", "signature": "(x: int, y: int)", "returns": "str"}]}}},
            {"filename": "bar_python.prompt", "filepath": "pdd/bar.py",
             "reason": "LLM changed this", "interface": {"type": "module", "module": {"functions": [{"name": "bar", "signature": "(a: str)", "returns": "bool"}]}}},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(current, indent=2))

        changed_files = ["pdd/prompts/foo_python.prompt"]
        _scope_architecture_to_changed_files(tmp_path, previous, changed_files)

        result = json.loads(arch_path.read_text())
        # foo was in changed_files — its mutations should survive
        assert result[0]["reason"] == "Updated reason for foo"
        assert result[0]["interface"]["module"]["functions"][0]["signature"] == "(x: int, y: int)"
        # bar was NOT in changed_files — must be reverted to previous
        assert result[1]["reason"] == "Bar original"
        assert result[1]["interface"]["module"]["functions"][0]["signature"] == "(a: str, b: int)"

    def test_new_entries_for_changed_files_preserved(self, tmp_path):
        """Brand new architecture entries for changed files should be kept."""
        previous = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "Foo"},
        ]
        current = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "Foo"},
            {"filename": "embed_retrieve_python.prompt", "filepath": "pdd/embed_retrieve.py",
             "reason": "New module", "interface": {"type": "module"}},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(current, indent=2))

        changed_files = ["pdd/prompts/embed_retrieve_python.prompt"]
        _scope_architecture_to_changed_files(tmp_path, previous, changed_files)

        result = json.loads(arch_path.read_text())
        filenames = [e["filename"] for e in result]
        assert "embed_retrieve_python.prompt" in filenames

    def test_hallucinated_entries_removed(self, tmp_path):
        """New entries for files NOT in changed_files should be removed (hallucinations)."""
        previous = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "Foo"},
        ]
        current = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "Foo"},
            {"filename": "phantom_python.prompt", "filepath": "pdd/phantom.py",
             "reason": "LLM hallucinated this", "interface": {"type": "module"}},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(current, indent=2))

        changed_files = ["pdd/prompts/foo_python.prompt"]
        _scope_architecture_to_changed_files(tmp_path, previous, changed_files)

        result = json.loads(arch_path.read_text())
        filenames = [e["filename"] for e in result]
        assert "phantom_python.prompt" not in filenames

    def test_no_changed_files_reverts_all(self, tmp_path):
        """When changed_files is empty, all entries should match previous exactly."""
        previous = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "Original"},
        ]
        current = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "Mutated"},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(current, indent=2))

        _scope_architecture_to_changed_files(tmp_path, previous, [])

        result = json.loads(arch_path.read_text())
        assert result[0]["reason"] == "Original"

    def test_noop_when_no_previous(self, tmp_path):
        """Gracefully handles None previous_architecture."""
        current = [{"filename": "foo_python.prompt", "reason": "New"}]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(current, indent=2))

        _scope_architecture_to_changed_files(tmp_path, None, ["prompts/foo_python.prompt"])

        result = json.loads(arch_path.read_text())
        assert result[0]["reason"] == "New"  # unchanged

    def test_dependencies_field_reverted_for_out_of_scope(self, tmp_path):
        """Non-interface fields like dependencies must also be reverted."""
        previous = [
            {"filename": "bar_python.prompt", "filepath": "pdd/bar.py",
             "dependencies": ["a_python.prompt", "b_python.prompt"]},
        ]
        current = [
            {"filename": "bar_python.prompt", "filepath": "pdd/bar.py",
             "dependencies": ["a_python.prompt"]},  # LLM dropped b
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(current, indent=2))

        _scope_architecture_to_changed_files(tmp_path, previous, [])

        result = json.loads(arch_path.read_text())
        assert "b_python.prompt" in result[0]["dependencies"]

    def test_matches_by_filepath_when_filename_missing(self, tmp_path):
        """Should match entries by filepath if filename is absent."""
        previous = [
            {"filepath": "pdd/bar.py", "reason": "Original"},
        ]
        current = [
            {"filepath": "pdd/bar.py", "reason": "LLM mutated"},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(current, indent=2))

        _scope_architecture_to_changed_files(tmp_path, previous, [])

        result = json.loads(arch_path.read_text())
        assert result[0]["reason"] == "Original"

    def test_changed_files_with_various_path_formats(self, tmp_path):
        """changed_files may contain paths like pdd/prompts/X.prompt or prompts/X.prompt."""
        previous = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "Old"},
            {"filename": "bar_python.prompt", "filepath": "pdd/bar.py", "reason": "Old bar"},
        ]
        current = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "New foo"},
            {"filename": "bar_python.prompt", "filepath": "pdd/bar.py", "reason": "New bar"},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(current, indent=2))

        # Both path formats should work
        changed_files = ["pdd/prompts/foo_python.prompt", "prompts/bar_python.prompt"]
        _scope_architecture_to_changed_files(tmp_path, previous, changed_files)

        result = json.loads(arch_path.read_text())
        assert result[0]["reason"] == "New foo"  # in scope
        assert result[1]["reason"] == "New bar"  # in scope

    def test_subdirectory_prompts_in_scope(self, tmp_path):
        """Prompts in subdirectories (e.g. commands/maintenance_python.prompt)
        must be recognized as in-scope when changed_files has the full path."""
        previous = [
            {"filename": "commands/maintenance_python.prompt", "filepath": "pdd/commands/maintenance.py", "reason": "Old"},
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "Old foo"},
        ]
        current = [
            {"filename": "commands/maintenance_python.prompt", "filepath": "pdd/commands/maintenance.py", "reason": "New maintenance"},
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "LLM mutated foo"},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(current, indent=2))

        changed_files = ["pdd/prompts/commands/maintenance_python.prompt"]
        _scope_architecture_to_changed_files(tmp_path, previous, changed_files)

        result = json.loads(arch_path.read_text())
        # maintenance was in scope — keep LLM's update
        assert result[0]["reason"] == "New maintenance"
        # foo was NOT in scope — revert to previous
        assert result[1]["reason"] == "Old foo"


# -----------------------------------------------------------------------------
# Sync Order Path Prefix Tests (TDD for Issue #733 Bug #5)
# -----------------------------------------------------------------------------

class TestSyncOrderPddPromptsPath:
    """Tests that sync order detection works with pdd/prompts/ path prefix."""

    def test_pdd_prompts_path_detected_as_module(self, tmp_path):
        """FILES_MODIFIED with pdd/prompts/ prefix should be detected for sync order."""
        mocks = {}
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
            mock_subprocess.return_value.stdout = str(tmp_path)
            mock_subprocess.return_value.returncode = 0
            mock_topo_sort.return_value = (["embed_retrieve", "auto_include"], [])
            mock_get_affected.return_value = ["embed_retrieve", "auto_include"]

            worktree_dir = tmp_path / "wt"
            prompts_dir = worktree_dir / "prompts"
            prompts_dir.mkdir(parents=True)
            (prompts_dir / "embed_retrieve_python.prompt").write_text("% embed module")
            (prompts_dir / "auto_include_python.prompt").write_text("% auto include")

            # Step 9 reports files with pdd/prompts/ prefix (as git does with real paths)
            existing_state = {
                "last_completed_step": 12,
                "step_outputs": {str(i): "out" for i in range(1, 13)},
                "worktree_path": str(worktree_dir),
            }
            existing_state["step_outputs"]["9"] = (
                "FILES_CREATED: pdd/prompts/embed_retrieve_python.prompt\n"
                "FILES_MODIFIED: pdd/prompts/auto_include_python.prompt"
            )
            mock_load.return_value = (existing_state, 123)
            mock_run.return_value = (True, "PR Created", 0.1, "gpt-4")

            success, msg, cost, model, files = run_agentic_change_orchestrator(
                issue_url="http://issue", issue_content="Add embed retrieve",
                repo_owner="o", repo_name="r", issue_number=733,
                issue_author="bot", issue_title="Agentic auto deps",
                cwd=tmp_path, quiet=True,
            )

            # build_dependency_graph should have been called (modules were detected)
            mock_build_graph.assert_called()
            # get_affected_modules should have received the detected modules
            call_args = mock_get_affected.call_args
            detected_modules = call_args[0][1]  # second positional arg
            assert "embed_retrieve" in detected_modules, (
                f"embed_retrieve not detected from pdd/prompts/ path. Got: {detected_modules}"
            )
            assert "auto_include" in detected_modules

    def test_prompts_slash_path_still_works(self, tmp_path):
        """The original prompts/ prefix should continue to work."""
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
            mock_subprocess.return_value.stdout = str(tmp_path)
            mock_subprocess.return_value.returncode = 0
            mock_topo_sort.return_value = (["foo"], [])
            mock_get_affected.return_value = ["foo"]

            worktree_dir = tmp_path / "wt"
            prompts_dir = worktree_dir / "prompts"
            prompts_dir.mkdir(parents=True)
            (prompts_dir / "foo_python.prompt").write_text("% foo module")

            existing_state = {
                "last_completed_step": 12,
                "step_outputs": {str(i): "out" for i in range(1, 13)},
                "worktree_path": str(worktree_dir),
            }
            existing_state["step_outputs"]["9"] = "FILES_MODIFIED: prompts/foo_python.prompt"
            mock_load.return_value = (existing_state, 123)
            mock_run.return_value = (True, "PR Created", 0.1, "gpt-4")

            run_agentic_change_orchestrator(
                issue_url="http://issue", issue_content="Fix",
                repo_owner="o", repo_name="r", issue_number=1,
                issue_author="me", issue_title="Fix",
                cwd=tmp_path, quiet=True,
            )

            mock_build_graph.assert_called()
            call_args = mock_get_affected.call_args
            detected_modules = call_args[0][1]
            assert "foo" in detected_modules
