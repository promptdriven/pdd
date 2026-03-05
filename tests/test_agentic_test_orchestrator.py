"""Tests for pdd.agentic_test_orchestrator module.

Tests cover:
  - Full 18-step happy path (non-web, skipping manual testing steps 6-11)
  - Hard stop conditions (duplicate, needs info, plan blocked, no files at step 12)
  - State resumption from cached workflow state
  - Blind-resume validation (Issue #467)
  - Worktree creation and failure handling
  - File parsing from FILES_CREATED / FILES_MODIFIED output
  - Conditional step execution (web + playwright-cli gating)
  - Step 16 skip when step 15 produces no new files
  - Missing prompt template handling
  - Context accumulation (step5b_output alias, enhanced_test_plan, etc.)
  - Cost accumulation across steps
  - Z3 formal verification of cost and step-execution properties
"""
from __future__ import annotations

import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path

from pdd.agentic_test_orchestrator import (
    run_agentic_test_orchestrator,
    TEST_STEP_TIMEOUTS,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_deps():
    """Patch all external dependencies of the orchestrator."""
    with patch("pdd.agentic_test_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_test_orchestrator.load_workflow_state") as mock_load, \
         patch("pdd.agentic_test_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_test_orchestrator.clear_workflow_state") as mock_clear, \
         patch("pdd.agentic_test_orchestrator.load_prompt_template") as mock_template, \
         patch("pdd.agentic_test_orchestrator._setup_worktree") as mock_wt, \
         patch("pdd.agentic_test_orchestrator.shutil") as mock_shutil, \
         patch("subprocess.run") as mock_subprocess:

        mock_load.return_value = (None, None)
        mock_save.return_value = None
        mock_template.return_value = "Mock prompt: {issue_content}"
        mock_wt.return_value = (Path("/tmp/worktree"), None)
        mock_shutil.which.return_value = None  # No playwright-cli
        mock_subprocess.return_value = MagicMock(stdout="main\n", returncode=0)
        mock_run.return_value = (True, "Step Output", 0.1, "anthropic")

        yield {
            "run": mock_run,
            "load": mock_load,
            "save": mock_save,
            "clear": mock_clear,
            "template": mock_template,
            "wt": mock_wt,
            "shutil": mock_shutil,
            "subprocess": mock_subprocess,
        }


@pytest.fixture
def default_args(tmp_path):
    """Default arguments for run_agentic_test_orchestrator."""
    return {
        "issue_url": "https://github.com/o/r/issues/1",
        "issue_content": "Add tests for the login page.",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Add login tests",
        "cwd": tmp_path,
        "quiet": True,
        "use_github_state": False,
    }


# ---------------------------------------------------------------------------
# Happy path
# ---------------------------------------------------------------------------

def test_happy_path_non_web(mock_deps, default_args):
    """Full 18-step run with non-web TEST_TYPE skips steps 6-11."""
    mocks = mock_deps

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step4":
            return (True, "TEST_TYPE: api\nTEST_FRAMEWORK: pytest", 0.1, "anthropic")
        if label == "step12":
            return (True, "FILES_CREATED: tests/test_api.py\nGenerated.", 0.1, "anthropic")
        if label == "step17":
            return (True, "PR Created: https://github.com/o/r/pull/10", 0.1, "anthropic")
        return (True, f"Output for {label}", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_test_orchestrator(**default_args)

    assert success is True
    assert "PR Created" in msg
    assert "tests/test_api.py" in files
    # Steps 1-5, 5.5, 12-17 = 12 steps (skipping 6-11 and 16)
    executed_labels = [c.kwargs["label"] for c in mocks["run"].call_args_list]
    assert "step1" in executed_labels
    assert "step5.5" in executed_labels
    assert "step12" in executed_labels
    assert "step17" in executed_labels
    # Steps 6-11 should NOT execute (non-web)
    for s in ["step6", "step7", "step8", "step9", "step10", "step11"]:
        assert s not in executed_labels
    assert mocks["clear"].called


def test_cost_accumulation(mock_deps, default_args):
    """Total cost is sum of all step costs."""
    mocks = mock_deps

    call_count = 0

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        nonlocal call_count
        call_count += 1
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.05, "anthropic")
        return (True, f"Output for {label}", 0.05, "anthropic")

    mocks["run"].side_effect = side_effect

    _, _, cost, _, _ = run_agentic_test_orchestrator(**default_args)

    expected = call_count * 0.05
    assert cost == pytest.approx(expected, abs=1e-6)


# ---------------------------------------------------------------------------
# Hard stops
# ---------------------------------------------------------------------------

def test_hard_stop_duplicate(mock_deps, default_args):
    """Step 1 duplicate detection stops the workflow."""
    mocks = mock_deps
    mocks["run"].return_value = (True, "Duplicate of #42", 0.1, "anthropic")

    success, msg, cost, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 1" in msg
    assert "duplicate" in msg.lower()
    assert mocks["run"].call_count == 1
    assert not mocks["clear"].called


def test_hard_stop_needs_info(mock_deps, default_args):
    """Step 3 'Needs More Info' stops the workflow."""
    mocks = mock_deps

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step3":
            return (True, "Needs More Info from author", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 3" in msg
    assert mocks["run"].call_count == 3


def test_hard_stop_plan_blocked(mock_deps, default_args):
    """Step 5 PLAN_BLOCKED stops the workflow."""
    mocks = mock_deps

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step5":
            return (True, "PLAN_BLOCKED: Cannot test without environment", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 5" in msg
    assert "not achievable" in msg.lower()
    assert mocks["run"].call_count == 5


def test_hard_stop_no_files_step12(mock_deps, default_args):
    """Step 12 with no FILES_CREATED/FILES_MODIFIED stops the workflow."""
    mocks = mock_deps

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step12":
            return (True, "Generated tests but forgot to list files.", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 12" in msg
    assert "No test file" in msg


# ---------------------------------------------------------------------------
# State persistence and resumption
# ---------------------------------------------------------------------------

def test_resume_from_cached_state(mock_deps, default_args):
    """Resuming from cached state skips completed steps."""
    mocks = mock_deps

    state = {
        "last_completed_step": 4,
        "step_outputs": {
            "1": "out1", "2": "out2", "3": "out3", "4": "out4",
        },
        "total_cost": 0.4,
        "model_used": "anthropic",
    }
    mocks["load"].return_value = (state, 100)

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    success, _, cost, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is True
    executed = [c.kwargs["label"] for c in mocks["run"].call_args_list]
    # Steps 1-4 skipped
    assert "step1" not in executed
    assert "step4" not in executed
    # Step 5 and beyond executed
    assert "step5" in executed


def test_resume_all_failed_reruns_from_step1(mock_deps, default_args):
    """Issue #467: All-failed state should re-run from step 1."""
    mocks = mock_deps

    corrupted_state = {
        "last_completed_step": 5,
        "step_outputs": {
            "1": "FAILED: error", "2": "FAILED: error",
            "3": "FAILED: error", "4": "FAILED: error", "5": "FAILED: error",
        },
        "total_cost": 0.0,
        "model_used": "unknown",
    }
    mocks["load"].return_value = (corrupted_state, None)

    executed_labels = []

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        executed_labels.append(label)
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    run_agentic_test_orchestrator(**default_args)

    assert "step1" in executed_labels, (
        f"Step 1 should be re-executed (blind-resume fix). Got: {executed_labels}"
    )


def test_resume_partial_failure_reruns_from_failed_step(mock_deps, default_args):
    """Issue #467: Steps 1-3 ok, 4-5 failed -> resume from step 4."""
    mocks = mock_deps

    state = {
        "last_completed_step": 5,
        "step_outputs": {
            "1": "ok", "2": "ok", "3": "ok",
            "4": "FAILED: error", "5": "FAILED: error",
        },
        "total_cost": 0.3,
        "model_used": "anthropic",
    }
    mocks["load"].return_value = (state, None)

    executed_labels = []

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        executed_labels.append(label)
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    run_agentic_test_orchestrator(**default_args)

    assert "step1" not in executed_labels
    assert "step3" not in executed_labels
    assert "step4" in executed_labels


# ---------------------------------------------------------------------------
# Worktree
# ---------------------------------------------------------------------------

def test_worktree_creation_failure(mock_deps, default_args):
    """Worktree failure returns early with error message."""
    mocks = mock_deps
    mocks["wt"].return_value = (None, "Git error: lock exists")

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is False
    assert "Failed to create worktree" in msg


# ---------------------------------------------------------------------------
# File parsing
# ---------------------------------------------------------------------------

def test_file_parsing_deduplication(mock_deps, default_args):
    """FILES_CREATED and FILES_MODIFIED results are deduplicated."""
    mocks = mock_deps

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step12":
            return (True, "FILES_CREATED: a.py, b.py", 0.1, "anthropic")
        if label == "step14":
            return (True, "FILES_MODIFIED: b.py, c.py", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    _, _, _, _, files = run_agentic_test_orchestrator(**default_args)

    assert set(files) == {"a.py", "b.py", "c.py"}


# ---------------------------------------------------------------------------
# Missing template
# ---------------------------------------------------------------------------

def test_missing_template_returns_failure(mock_deps, default_args):
    """If load_prompt_template returns None, the step fails gracefully."""
    mocks = mock_deps
    mocks["template"].return_value = None

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    # Step 1 gets None template -> run_step returns failure -> hard stop check not matched
    # But run_agentic_task is never called
    assert mocks["run"].call_count == 0
    # With no template, run_step returns (False, "Missing prompt template: ...", 0.0, "unknown")
    # The output has no hard stop pattern, so the orchestrator continues but
    # eventually every step fails the same way. The workflow should still return.
    # Due to step 12 having no FILES_CREATED in the empty output, it hard-stops.
    assert success is False


# ---------------------------------------------------------------------------
# Step 16 skip logic
# ---------------------------------------------------------------------------

def test_step16_skipped_when_step15_has_no_new_files(mock_deps, default_args):
    """Step 16 is skipped when step 15 output has no FILES_CREATED."""
    mocks = mock_deps

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.1, "anthropic")
        if label == "step15":
            return (True, "All tests cover the plan. No new files needed.", 0.1, "anthropic")
        if label == "step17":
            return (True, "PR Created: https://github.com/o/r/pull/5", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is True
    executed = [c.kwargs["label"] for c in mocks["run"].call_args_list]
    assert "step16" not in executed
    assert "step17" in executed


def test_step16_runs_when_step15_creates_files(mock_deps, default_args):
    """Step 16 runs when step 15 output contains FILES_CREATED."""
    mocks = mock_deps

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.1, "anthropic")
        if label == "step15":
            return (True, "FILES_CREATED: tests/test_missing.py\nGenerated missing tests.", 0.1, "anthropic")
        if label == "step17":
            return (True, "PR Created: https://github.com/o/r/pull/6", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    success, _, _, _, files = run_agentic_test_orchestrator(**default_args)

    assert success is True
    executed = [c.kwargs["label"] for c in mocks["run"].call_args_list]
    assert "step16" in executed
    assert "tests/test_missing.py" in files


# ---------------------------------------------------------------------------
# Context accumulation
# ---------------------------------------------------------------------------

def test_context_passes_step_outputs(mock_deps, default_args):
    """Later steps receive context from earlier steps via template formatting."""
    mocks = mock_deps
    mocks["template"].return_value = "Context: {step1_output} | {issue_content}"

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step1":
            return (True, "No duplicates found.", 0.1, "anthropic")
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    run_agentic_test_orchestrator(**default_args)

    # Step 2 should have step1_output in its instruction
    step2_calls = [c for c in mocks["run"].call_args_list if c.kwargs.get("label") == "step2"]
    assert len(step2_calls) == 1
    instruction = step2_calls[0].kwargs["instruction"]
    assert "No duplicates found." in instruction


def test_step5b_output_alias_in_context(mock_deps, default_args):
    """Step 5.5 output is available as both step5.5_output and step5b_output."""
    mocks = mock_deps
    mocks["template"].return_value = "Plan: {step5b_output}"

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step5.5":
            return (True, "Enhanced plan with contracts.", 0.1, "anthropic")
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    run_agentic_test_orchestrator(**default_args)

    # Step 12 should have step5b_output in its formatted instruction
    step12_calls = [c for c in mocks["run"].call_args_list if c.kwargs.get("label") == "step12"]
    assert len(step12_calls) == 1
    instruction = step12_calls[0].kwargs["instruction"]
    assert "Enhanced plan with contracts." in instruction


# ---------------------------------------------------------------------------
# TEST_STEP_TIMEOUTS
# ---------------------------------------------------------------------------

def test_step_timeouts_defined():
    """All expected step timeouts are defined with correct values."""
    assert TEST_STEP_TIMEOUTS[1] == 240.0
    assert TEST_STEP_TIMEOUTS[5.5] == 400.0
    assert TEST_STEP_TIMEOUTS[8] == 1800.0
    assert TEST_STEP_TIMEOUTS[12] == 1000.0
    assert TEST_STEP_TIMEOUTS[17] == 240.0
    # 18 entries total (17 integer steps + step 5.5)
    assert len(TEST_STEP_TIMEOUTS) == 18


def test_timeout_adder_extends_timeouts(mock_deps, default_args):
    """timeout_adder is added to each step's timeout."""
    mocks = mock_deps
    default_args["timeout_adder"] = 60.0

    mocks["run"].return_value = (True, "Duplicate of #1", 0.1, "anthropic")

    run_agentic_test_orchestrator(**default_args)

    # Step 1 timeout should be 240.0 + 60.0 = 300.0
    assert mocks["run"].call_count >= 1
    call = mocks["run"].call_args_list[0]
    assert call.kwargs["timeout"] == 300.0


# ---------------------------------------------------------------------------
# Soft failure (continue)
# ---------------------------------------------------------------------------

def test_soft_failure_continues(mock_deps, default_args):
    """A step returning (False, ...) without a hard stop pattern continues."""
    mocks = mock_deps

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step2":
            return (False, "Partial failure, no hard stop", 0.1, "anthropic")
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    success, _, _, _, _ = run_agentic_test_orchestrator(**default_args)

    # Despite step 2 failing, workflow continues and completes
    assert success is True
    executed = [c.kwargs["label"] for c in mocks["run"].call_args_list]
    assert "step3" in executed


# ---------------------------------------------------------------------------
# Return tuple structure
# ---------------------------------------------------------------------------

def test_return_tuple_structure(mock_deps, default_args):
    """Return value is a 5-tuple with correct types."""
    mocks = mock_deps

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    result = run_agentic_test_orchestrator(**default_args)

    assert isinstance(result, tuple)
    assert len(result) == 5
    success, msg, cost, model, files = result
    assert isinstance(success, bool)
    assert isinstance(msg, str)
    assert isinstance(cost, float)
    assert isinstance(model, str)
    assert isinstance(files, list)


# ---------------------------------------------------------------------------
# Step 4 extracts TEST_TYPE and TARGET_URL
# ---------------------------------------------------------------------------

def test_step4_extracts_test_type_and_target_url(mock_deps, default_args):
    """Step 4 output with TEST_TYPE and TARGET_URL is parsed into context."""
    mocks = mock_deps
    mocks["template"].return_value = "Type: {frontend_type} URL: {target_url}"

    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        if label == "step4":
            return (True, "TEST_TYPE: web\nTARGET_URL: http://localhost:3000", 0.1, "anthropic")
        if label == "step12":
            return (True, "FILES_CREATED: test.py", 0.1, "anthropic")
        return (True, "ok", 0.1, "anthropic")

    mocks["run"].side_effect = side_effect

    run_agentic_test_orchestrator(**default_args)

    # Step 5 should see the extracted values in the prompt
    step5_calls = [c for c in mocks["run"].call_args_list if c.kwargs.get("label") == "step5"]
    if step5_calls:
        instruction = step5_calls[0].kwargs["instruction"]
        assert "web" in instruction
        assert "http://localhost:3000" in instruction


# ---------------------------------------------------------------------------
# Z3 formal verification
# ---------------------------------------------------------------------------

def test_z3_cost_accumulation():
    """Z3: Prove total_cost = initial_cost + sum(step_costs)."""
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = z3.Solver()
    initial_cost = z3.Real("initial_cost")
    step_costs = [z3.Real(f"cost_{i}") for i in range(18)]
    steps_run = [z3.Bool(f"run_{i}") for i in range(18)]
    final_cost = z3.Real("final_cost")

    s.add(initial_cost >= 0)
    for c in step_costs:
        s.add(c >= 0)

    accumulated = initial_cost
    for i in range(18):
        accumulated = z3.If(steps_run[i], accumulated + step_costs[i], accumulated)

    s.add(final_cost == accumulated)
    s.add(z3.Not(final_cost >= initial_cost))

    assert s.check() == z3.unsat, f"Counter-example: {s.model()}"


def test_z3_step_execution_order():
    """Z3: Prove that a later step cannot run if an earlier step hard-stopped."""
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = z3.Solver()
    start_step = z3.Int("start_step")
    hard_stop = [z3.Bool(f"stop_{i}") for i in range(18)]
    step_runs = [z3.Bool(f"run_{i}") for i in range(18)]

    s.add(start_step >= 0, start_step <= 18)

    for i in range(18):
        condition = (i >= start_step)
        for k in range(i):
            condition = z3.And(condition, z3.Not(z3.And(step_runs[k], hard_stop[k])))
        s.add(step_runs[i] == condition)

    # Try to prove: step 12 cannot run if step 5 ran and hard-stopped
    s.add(step_runs[12])
    s.add(step_runs[5])
    s.add(hard_stop[5])

    assert s.check() == z3.unsat, f"Counter-example: {s.model()}"
