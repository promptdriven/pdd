"""
Tests for remaining issue #830 fixes:
1. os.killpg on TimeoutExpired in _run_with_provider
2. Step 1 timeout retry in orchestrator
3. final_message posted to GitHub on early exit
4. Skip redundant Steps 2-3 when pdd-bug analysis exists
"""
import json
import os
import re
import signal
import subprocess
from pathlib import Path
from typing import Dict, List, Optional
from unittest.mock import patch, MagicMock, call, ANY

import pytest

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_git_repo(tmp_path):
    """Create a minimal git repository for testing."""
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()
    subprocess.run(["git", "init", "-b", "main"], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=repo_path, check=True, capture_output=True)
    pdd_dir = repo_path / ".pdd"
    pdd_dir.mkdir()
    (repo_path / "README.md").write_text("# Test\n")
    subprocess.run(["git", "add", "."], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_path, check=True, capture_output=True)
    return repo_path


@pytest.fixture
def orchestrator_io_mocks():
    """Mock external I/O for the orchestrator."""
    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit, \
         patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check_e2e, \
         patch("pdd.agentic_e2e_fix_orchestrator.preprocess", side_effect=lambda t, **kw: t):

        mock_load.return_value = "Prompt for {issue_number}"
        mock_load_state.return_value = (None, None)
        mock_save_state.return_value = None
        mock_hashes.return_value = {}
        mock_commit.return_value = (True, "No changes to commit")
        mock_check_e2e.return_value = (True, "")

        yield {
            "run": mock_run,
            "load": mock_load,
            "console": mock_console,
            "load_state": mock_load_state,
            "save_state": mock_save_state,
            "clear_state": mock_clear_state,
            "check_e2e": mock_check_e2e,
            "commit": mock_commit,
        }


def _default_orchestrator_kwargs(cwd):
    return dict(
        issue_url="https://github.com/test/repo/issues/830",
        issue_content="Test issue for #830 remaining fixes",
        repo_owner="test",
        repo_name="repo",
        issue_number=830,
        issue_author="test-user",
        issue_title="Test issue",
        cwd=cwd,
        verbose=False,
        quiet=True,
        max_cycles=2,
        resume=False,
        use_github_state=False,
    )


# ===========================================================================
# 1. os.killpg on TimeoutExpired
# ===========================================================================

class TestBug2ProcessGroupKill:
    """_run_with_provider must kill the process group on timeout, not just return."""

    def test_timeout_calls_killpg(self, tmp_path):
        """When subprocess times out, os.killpg should be called to kill the
        process group via Popen's pid."""
        from pdd.agentic_common import _subprocess_run

        mock_proc = MagicMock()
        mock_proc.pid = 12345
        mock_proc.communicate.side_effect = subprocess.TimeoutExpired(cmd="test", timeout=10)
        mock_proc.kill.return_value = None
        mock_proc.wait.return_value = None

        with patch("pdd.agentic_common.subprocess.Popen", return_value=mock_proc), \
             patch("pdd.agentic_common.os.killpg") as mock_killpg, \
             patch("pdd.agentic_common.os.getpgid", return_value=12345):

            with pytest.raises(subprocess.TimeoutExpired):
                _subprocess_run(
                    ["test"],
                    capture_output=True,
                    text=True,
                    timeout=10.0,
                    start_new_session=True,
                )

            # The critical assertion: os.killpg must be called to kill orphans
            mock_killpg.assert_called_once_with(
                12345,
                signal.SIGKILL,
            ), (
                "BUG: _subprocess_run does not call os.killpg() on timeout. "
                "Child processes from CLI tools become orphans."
            )


# ===========================================================================
# 2. Step 1 timeout retry
# ===========================================================================

class TestStep1TimeoutRetry:
    """When Step 1 (code gen) times out, the orchestrator should retry it."""

    def test_step1_timeout_is_retried(self, mock_git_repo, orchestrator_io_mocks):
        """Step 1 timeout should be retried at least once before being marked
        as failed. Currently there's no step-level retry — the failure just
        propagates."""
        mock_run = orchestrator_io_mocks["run"]

        step1_call_count = 0

        def side_effect(*args, **kwargs):
            nonlocal step1_call_count
            label = kwargs.get("label", "")

            if "step1" in label:
                step1_call_count += 1
                if step1_call_count == 1:
                    # First attempt: timeout
                    return (False, "All agent providers failed: anthropic: Timeout expired", 0.0, "")
                else:
                    # Retry: success
                    return (True, "Code generation complete.", 0.10, "claude-3-opus")

            if "step9" in label:
                return (True, "ALL_TESTS_PASS", 0.10, "claude-3-opus")

            return (True, f"Output for {label}", 0.05, "claude-3-opus")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **_default_orchestrator_kwargs(mock_git_repo)
        )

        assert step1_call_count >= 2, (
            f"Step 1 was only called {step1_call_count} time(s). "
            "When Step 1 times out, the orchestrator should retry it at least once "
            "before marking it as failed and continuing to diagnostic steps."
        )

    def test_step1_timeout_no_retry_wastes_budget(self, mock_git_repo, orchestrator_io_mocks):
        """Without retry, Step 1 timeout causes Steps 2-3 to re-diagnose the
        issue, wasting budget on redundant work."""
        mock_run = orchestrator_io_mocks["run"]

        steps_called = []

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            step_match = re.search(r"step(\d+)", label)
            if step_match:
                steps_called.append(int(step_match.group(1)))

            if "step1" in label:
                return (False, "All agent providers failed: anthropic: Timeout expired", 0.0, "")
            if "step9" in label:
                return (True, "ALL_TESTS_PASS", 0.10, "claude-3-opus")
            return (True, f"Output for {label}", 0.05, "claude-3-opus")

        mock_run.side_effect = side_effect

        run_agentic_e2e_fix_orchestrator(
            **_default_orchestrator_kwargs(mock_git_repo)
        )

        # Step 1 should appear at least twice (original + retry)
        step1_count = steps_called.count(1)
        assert step1_count >= 2, (
            f"Step 1 called {step1_count} time(s). Expected retry on timeout. "
            f"Steps called: {steps_called}"
        )


# ===========================================================================
# 3. final_message posted to GitHub on early exit
# ===========================================================================

class TestFinalMessagePostedToGithub:
    """When workflow exits early, a final comment must be posted to the issue."""

    def test_not_a_bug_posts_final_comment(self, mock_git_repo, orchestrator_io_mocks):
        """When Step 3 returns NOT_A_BUG, a comment should be posted to GitHub
        explaining why the workflow stopped."""
        mock_run = orchestrator_io_mocks["run"]

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step3" in label:
                return (True, "NOT_A_BUG: This is expected behavior.", 0.05, "claude-3-opus")
            return (True, f"Output for {label}", 0.05, "claude-3-opus")

        mock_run.side_effect = side_effect

        with patch("pdd.agentic_e2e_fix_orchestrator.post_final_comment") as mock_post:
            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                **_default_orchestrator_kwargs(mock_git_repo)
            )

        assert not success
        assert "not a bug" in msg.lower()

        # A final comment should have been posted to the issue
        assert mock_post.called, (
            "No final comment was posted to GitHub when workflow exited with NOT_A_BUG. "
            "Users won't know why the workflow stopped unless a comment is posted."
        )

    def test_missing_loop_token_posts_final_comment(self, mock_git_repo, orchestrator_io_mocks):
        """When Step 9 has no loop control token, a final comment should be
        posted explaining the workflow stopped."""
        mock_run = orchestrator_io_mocks["run"]

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                return (True, "Verification complete. Tests checked.", 0.10, "claude-3-opus")
            return (True, f"Output for {label}", 0.05, "claude-3-opus")

        mock_run.side_effect = side_effect

        with patch("pdd.agentic_e2e_fix_orchestrator.post_final_comment") as mock_post:
            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                **_default_orchestrator_kwargs(mock_git_repo)
            )

        assert mock_post.called, (
            "No final comment posted to GitHub when workflow stopped due to missing "
            "loop control token in Step 9."
        )

    def test_max_cycles_posts_final_comment(self, mock_git_repo, orchestrator_io_mocks):
        """When max cycles are exhausted, a final comment should be posted."""
        mock_run = orchestrator_io_mocks["run"]

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                return (True, "CONTINUE_CYCLE — more work needed.", 0.10, "claude-3-opus")
            return (True, f"Output for {label}", 0.05, "claude-3-opus")

        mock_run.side_effect = side_effect

        with patch("pdd.agentic_e2e_fix_orchestrator.post_final_comment") as mock_post:
            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                **_default_orchestrator_kwargs(mock_git_repo)
            )

        assert not success

        assert mock_post.called, (
            "No final comment posted to GitHub when workflow exhausted max cycles."
        )

    def test_final_comment_includes_reason(self, mock_git_repo, orchestrator_io_mocks):
        """The final GitHub comment must include the reason for stopping."""
        mock_run = orchestrator_io_mocks["run"]

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step3" in label:
                return (True, "NOT_A_BUG: Expected behavior.", 0.05, "claude-3-opus")
            return (True, f"Output for {label}", 0.05, "claude-3-opus")

        mock_run.side_effect = side_effect

        with patch("pdd.agentic_e2e_fix_orchestrator.post_final_comment") as mock_post:
            run_agentic_e2e_fix_orchestrator(
                **_default_orchestrator_kwargs(mock_git_repo)
            )

        if mock_post.called:
            # Check the reason arg contains the reason
            call_kwargs = mock_post.call_args
            kwargs = call_kwargs[1] if call_kwargs[1] else {}
            reason = kwargs.get("reason", "")
            assert "not a bug" in reason.lower() or "NOT_A_BUG" in reason, (
                f"Final comment doesn't include the reason for stopping. Got: {reason}"
            )


# ===========================================================================
# 4. Skip redundant Steps 2-3 when pdd-bug analysis exists
# ===========================================================================

class TestSkipRedundantDiagnosis:
    """When pdd-bug already analyzed the issue, pdd-fix should skip Steps 2-3."""

    def test_skips_steps_2_3_when_bug_state_exists(self, mock_git_repo, orchestrator_io_mocks):
        """If a prior pdd-bug workflow already ran Steps 2-3 (root cause
        analysis), the fix workflow should reuse those results instead of
        re-running them."""
        mock_run = orchestrator_io_mocks["run"]
        mock_load_state = orchestrator_io_mocks["load_state"]

        # No e2e_fix state, but we'll check for bug state separately
        mock_load_state.return_value = (None, None)

        steps_called = []

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            step_match = re.search(r"step(\d+)", label)
            if step_match:
                steps_called.append(int(step_match.group(1)))
            if "step9" in label:
                return (True, "ALL_TESTS_PASS", 0.10, "claude-3-opus")
            return (True, f"Output for {label}", 0.05, "claude-3-opus")

        mock_run.side_effect = side_effect

        # Simulate existing pdd-bug state with Step 2-3 results
        bug_state = {
            "workflow": "bug",
            "issue_number": 830,
            "last_completed_step": 10,
            "step_outputs": {
                "2": "22 failing E2E tests identified: test_foo, test_bar...",
                "3": "CODE_BUG: Root cause is missing null check in handler.py",
                "5": "Root cause analysis: handler.py line 42 missing null check",
            },
        }
        bug_state_dir = mock_git_repo / ".pdd" / "state"
        bug_state_dir.mkdir(parents=True, exist_ok=True)
        bug_state_file = bug_state_dir / "bug_state_830.json"
        bug_state_file.write_text(json.dumps(bug_state))

        run_agentic_e2e_fix_orchestrator(
            **_default_orchestrator_kwargs(mock_git_repo)
        )

        # Steps 2 and 3 should NOT have been called via run_agentic_task
        assert 2 not in steps_called, (
            f"Step 2 was re-run even though pdd-bug already analyzed the issue. "
            f"Steps called: {steps_called}"
        )
        assert 3 not in steps_called, (
            f"Step 3 was re-run even though pdd-bug already analyzed the issue. "
            f"Steps called: {steps_called}"
        )

    def test_no_skip_when_bug_state_missing(self, mock_git_repo, orchestrator_io_mocks):
        """When no pdd-bug state exists, Steps 2-3 should run normally."""
        mock_run = orchestrator_io_mocks["run"]

        steps_called = []

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            step_match = re.search(r"step(\d+)", label)
            if step_match:
                steps_called.append(int(step_match.group(1)))
            if "step9" in label:
                return (True, "ALL_TESTS_PASS", 0.10, "claude-3-opus")
            return (True, f"Output for {label}", 0.05, "claude-3-opus")

        mock_run.side_effect = side_effect

        run_agentic_e2e_fix_orchestrator(
            **_default_orchestrator_kwargs(mock_git_repo)
        )

        # Without bug state, steps 2 and 3 SHOULD be called
        assert 2 in steps_called, f"Step 2 should run when no bug state exists. Steps: {steps_called}"
        assert 3 in steps_called, f"Step 3 should run when no bug state exists. Steps: {steps_called}"

    def test_reuses_bug_step_outputs(self, mock_git_repo, orchestrator_io_mocks):
        """When skipping Steps 2-3, their outputs from the bug workflow should
        be available to subsequent steps via step_outputs."""
        mock_run = orchestrator_io_mocks["run"]
        mock_load = orchestrator_io_mocks["load"]

        # Use a template that includes previous step output placeholders
        mock_load.return_value = "Prompt for {issue_number} prev2={step2_output} prev3={step3_output}"

        step4_prompt = None

        def side_effect(*args, **kwargs):
            nonlocal step4_prompt
            label = kwargs.get("label", "")
            instruction = args[0] if args else kwargs.get("instruction", "")
            if "step4" in label:
                step4_prompt = instruction
            if "step9" in label:
                return (True, "ALL_TESTS_PASS", 0.10, "claude-3-opus")
            return (True, f"Output for {label}", 0.05, "claude-3-opus")

        mock_run.side_effect = side_effect

        # Create pdd-bug state with step 2-3 results
        bug_state = {
            "workflow": "bug",
            "issue_number": 830,
            "last_completed_step": 10,
            "step_outputs": {
                "2": "BUG_STEP2_ANALYSIS: 22 failing tests found",
                "3": "BUG_STEP3_ROOTCAUSE: CODE_BUG in handler.py",
            },
        }
        bug_state_dir = mock_git_repo / ".pdd" / "state"
        bug_state_dir.mkdir(parents=True, exist_ok=True)
        (bug_state_dir / "bug_state_830.json").write_text(json.dumps(bug_state))

        run_agentic_e2e_fix_orchestrator(
            **_default_orchestrator_kwargs(mock_git_repo)
        )

        # Step 4's prompt should contain the bug workflow's step 2-3 outputs
        assert step4_prompt is not None, "Step 4 was never called"
        assert "BUG_STEP2_ANALYSIS" in step4_prompt or "BUG_STEP3_ROOTCAUSE" in step4_prompt, (
            f"Step 4's prompt doesn't include the reused bug workflow outputs. "
            f"When skipping Steps 2-3, their outputs should be injected into context. "
            f"Got: {step4_prompt}"
        )
