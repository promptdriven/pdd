"""Tests for Issue #791: E2E test step times out on every cycle.

Verifies the fix for two bugs:
1. Pre-flight check: Step 2 (e2e_tests) is now skipped when the environment
   lacks playwright/browser/dev-server infrastructure.
2. Cross-cycle memory: skipped steps are remembered across cycles via
   skipped_steps dict, not retried identically.
"""
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock, call

from pdd.agentic_e2e_fix_orchestrator import (
    run_agentic_e2e_fix_orchestrator,
    STEP_NAMES,
)


def _make_mock_run_agentic_task(timeout_steps=None):
    """Create a mock that simulates timeout on specific steps.

    Args:
        timeout_steps: set of step numbers that should simulate timeout
    """
    if timeout_steps is None:
        timeout_steps = set()

    call_log = []

    def mock_fn(instruction, cwd, *, verbose=False, quiet=False,
                timeout=None, label="", max_retries=1, **kwargs):
        """Mock run_agentic_task that logs calls and simulates timeouts."""
        # Parse cycle and step from label like "cycle1_step2"
        parts = label.split("_")
        cycle = int(parts[0].replace("cycle", ""))
        step = int(parts[1].replace("step", ""))

        call_log.append({"cycle": cycle, "step": step, "label": label})

        if step in timeout_steps:
            return (
                False,
                "FAILED: All agent providers failed: anthropic: Timeout expired",
                0.50,
                "mock-model",
            )

        # Successful step — return minimal output
        if step == 9:
            return (True, "CONTINUE_CYCLE", 0.10, "mock-model")
        return (True, f"Step {step} completed successfully", 0.10, "mock-model")

    return mock_fn, call_log


@pytest.fixture
def tmp_git_repo(tmp_path):
    """Create a minimal git repo for the orchestrator."""
    import subprocess
    subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=tmp_path, capture_output=True, check=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=tmp_path, capture_output=True, check=True)
    (tmp_path / "dummy.txt").write_text("init")
    subprocess.run(["git", "add", "."], cwd=tmp_path, capture_output=True, check=True)
    subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path, capture_output=True, check=True)
    return tmp_path


class TestIssue791_EnvironmentPreflightCheck:
    """Fix 1: Step 2 (e2e_tests) is skipped when E2E infrastructure is missing."""

    @patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="mock prompt {issue_url}")
    @patch("pdd.agentic_e2e_fix_orchestrator.preprocess", side_effect=lambda t, **kw: t)
    @patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None))
    @patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", return_value=None)
    @patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state")
    def test_step2_skipped_when_environment_unavailable(
        self, mock_clear, mock_save, mock_load, mock_preprocess, mock_template,
        tmp_git_repo,
    ):
        """Verifies that Step 2 (e2e_tests) is skipped via pre-flight check when
        the environment lacks playwright/browser/dev-server infrastructure.

        The orchestrator's _check_e2e_environment detects missing E2E infrastructure
        and skips Step 2 instead of dispatching it to the LLM agent.
        """
        mock_fn, call_log = _make_mock_run_agentic_task(timeout_steps={2})

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=mock_fn), \
             patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output", return_value=None):
            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/1",
                issue_content="Test issue with E2E tests",
                repo_owner="test",
                repo_name="repo",
                issue_number=1,
                issue_author="tester",
                issue_title="Test issue",
                cwd=tmp_git_repo,
                max_cycles=1,
                resume=False,
                quiet=True,
                use_github_state=False,
            )

        # FIX VERIFICATION: Step 2 should NOT be called — pre-flight check skips it
        step2_calls = [c for c in call_log if c["step"] == 2]
        assert len(step2_calls) == 0, (
            f"Step 2 (e2e_tests) was called {len(step2_calls)} time(s) despite missing "
            "E2E infrastructure. The pre-flight check should have skipped it."
        )


class TestIssue791_CrossCycleLearning:
    """Fix 2: Skipped steps are remembered across cycles via skipped_steps."""

    @patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="mock prompt {issue_url}")
    @patch("pdd.agentic_e2e_fix_orchestrator.preprocess", side_effect=lambda t, **kw: t)
    @patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None))
    @patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", return_value=None)
    @patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state")
    def test_step2_not_retried_across_cycles(
        self, mock_clear, mock_save, mock_load, mock_preprocess, mock_template,
        tmp_git_repo,
    ):
        """Verifies that Step 2 is skipped on all cycles when the environment
        lacks E2E infrastructure — not just cycle 1, but cycles 2 and 3 too.

        The orchestrator's skipped_steps dict persists across cycles (not cleared
        with step_outputs), preventing identical retries of environment-impossible steps.
        """
        mock_fn, call_log = _make_mock_run_agentic_task(timeout_steps={2})

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=mock_fn), \
             patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output", return_value=None):
            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/1",
                issue_content="Test issue with E2E tests",
                repo_owner="test",
                repo_name="repo",
                issue_number=1,
                issue_author="tester",
                issue_title="Test issue",
                cwd=tmp_git_repo,
                max_cycles=3,
                resume=False,
                quiet=True,
                use_github_state=False,
            )

        # Count how many times Step 2 was called across all cycles
        step2_calls = [c for c in call_log if c["step"] == 2]

        # FIX VERIFICATION: Step 2 should NOT be called on any cycle
        assert len(step2_calls) == 0, (
            f"Step 2 (e2e_tests) was called {len(step2_calls)} time(s) across 3 cycles. "
            f"It should be skipped on every cycle due to missing E2E infrastructure. "
            f"Calls: {step2_calls}"
        )

    @patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="mock prompt {issue_url}")
    @patch("pdd.agentic_e2e_fix_orchestrator.preprocess", side_effect=lambda t, **kw: t)
    @patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None))
    @patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", return_value=None)
    @patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state")
    def test_step_outputs_cleared_between_cycles(
        self, mock_clear, mock_save, mock_load, mock_preprocess, mock_template,
        tmp_git_repo,
    ):
        """Confirms that step_outputs is wiped clean between cycles,
        destroying any memory of previous failures.

        See orchestrator line 859: `step_outputs = {} # Clear outputs for next cycle`
        """
        saved_states = []

        def capture_save(cwd, issue_number, workflow_name, state_data, state_dir,
                         repo_owner, repo_name, use_github_state, github_comment_id=None):
            """Capture state saves to inspect cross-cycle behavior."""
            saved_states.append({
                "cycle": state_data.get("current_cycle"),
                "step": state_data.get("last_completed_step"),
                "step_outputs": dict(state_data.get("step_outputs", {})),
            })
            return None

        mock_fn, call_log = _make_mock_run_agentic_task(timeout_steps={2})

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=mock_fn), \
             patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output", return_value=None):
            with patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", side_effect=capture_save):
                run_agentic_e2e_fix_orchestrator(
                    issue_url="https://github.com/test/repo/issues/1",
                    issue_content="Test issue",
                    repo_owner="test",
                    repo_name="repo",
                    issue_number=1,
                    issue_author="tester",
                    issue_title="Test issue",
                    cwd=tmp_git_repo,
                    max_cycles=2,
                    resume=False,
                    quiet=True,
                    use_github_state=False,
                )

        # Find the state saves at the start of cycle 2 (after cycle transition)
        cycle2_saves = [s for s in saved_states if s["cycle"] == 2]
        if cycle2_saves:
            first_cycle2_save = cycle2_saves[0]
            # BUG: The step_outputs from cycle 1 (including Step 2 failure info) are gone
            assert "2" not in first_cycle2_save["step_outputs"] or \
                "Timeout" not in first_cycle2_save["step_outputs"].get("2", ""), (
                "Step 2 failure information from Cycle 1 is not carried forward to Cycle 2. "
                "The orchestrator has no cross-cycle memory of environmental failures."
            )
