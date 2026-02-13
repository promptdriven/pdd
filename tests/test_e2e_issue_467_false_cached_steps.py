"""
E2E Test for Issue #467: pdd bug falsely reporting cached steps

Tests the full bug orchestrator workflow to verify that when all LLM providers
fail for every step, the saved workflow state correctly keeps last_completed_step
at 0 (or the last actually successful step), and on resume the orchestrator
re-runs failed steps instead of blindly skipping them.

Bug Context (now fixed):
-----------
When `pdd bug` was run and ALL agent providers failed for every step:
1. Each failed step set `last_completed_step_to_save = step_num - 1`
2. This "ratcheted" the value up to 5.5 despite zero successes
3. On the next run, the orchestrator would skip steps 1-5.5 as "cached"

Fix:
----
1. On failure, last_completed_step_to_save remains unchanged (no ratchet)
2. On resume, cached step outputs are validated for FAILED: prefixes
3. Consecutive provider failures (>=3) trigger early abort
"""

import json
import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest


@pytest.fixture
def mock_git_repo(tmp_path):
    """Create a minimal git repository for testing the orchestrator."""
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()

    subprocess.run(
        ["git", "init", "-b", "main"], cwd=repo_path,
        check=True, capture_output=True
    )
    subprocess.run(
        ["git", "config", "user.email", "test@test.com"],
        cwd=repo_path, check=True
    )
    subprocess.run(
        ["git", "config", "user.name", "Test User"],
        cwd=repo_path, check=True
    )

    (repo_path / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=repo_path, check=True)
    subprocess.run(
        ["git", "commit", "-m", "Initial commit"],
        cwd=repo_path, check=True, capture_output=True
    )

    return repo_path


@pytest.mark.e2e
class TestIssue467FalseCachedStepsE2E:
    """
    E2E tests for Issue #467: Verify the fix for false cached steps.

    These tests exercise the full state persistence round-trip (save -> load)
    to verify that the fix correctly prevents the ratchet effect and blind resume.
    """

    def test_all_failures_then_resume_reruns_all_steps(self, mock_git_repo):
        """
        E2E test: Two consecutive orchestrator runs with the fix applied.

        Run 1: All LLM providers fail -> state saved with last_completed_step=0
        Run 2: Orchestrator loads state -> re-runs ALL steps from step 1

        Uses REAL save_workflow_state (local file) and REAL load_workflow_state.
        """
        from pdd.agentic_bug_orchestrator import (
            run_agentic_bug_orchestrator,
            _get_state_dir,
        )

        orchestrator_args = {
            "issue_url": "https://github.com/test/repo/issues/467",
            "issue_content": "pdd bug falsely reports cached steps",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 467,
            "issue_author": "jiaminc-cmu",
            "issue_title": "pdd bug reporting falsely cached steps",
            "cwd": mock_git_repo,
            "verbose": False,
            "quiet": True,
            "use_github_state": False,
        }

        mock_worktree = mock_git_repo / ".pdd" / "worktrees" / "fix-issue-467"
        mock_worktree.mkdir(parents=True, exist_ok=True)

        # ---- RUN 1: All providers fail ----
        def all_fail(*args, **kwargs):
            """Simulate all LLM providers failing for every step."""
            return (False, "All agent providers failed", 0.0, "")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=all_fail), \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)):

            run_agentic_bug_orchestrator(**orchestrator_args)

        # Verify state file was written by real save_workflow_state
        state_dir = _get_state_dir(mock_git_repo)
        state_file = state_dir / "bug_state_467.json"
        assert state_file.exists(), "State file should exist after Run 1"

        with open(state_file, "r") as f:
            saved_state = json.load(f)

        # FIX VERIFIED: last_completed_step should be 0 (no ratchet effect)
        assert saved_state["last_completed_step"] == 0, (
            f"last_completed_step should be 0 when all steps fail, "
            f"got {saved_state['last_completed_step']}"
        )

        # Verify all step outputs have FAILED: prefix
        for step_key, output in saved_state["step_outputs"].items():
            assert output.startswith("FAILED:"), (
                f"Step {step_key} should have FAILED prefix, got: {output[:50]}"
            )

        # ---- RUN 2: Resume should re-run all steps ----
        executed_steps = []

        def track_and_succeed(*args, **kwargs):
            """Track which steps execute and return success."""
            label = kwargs.get("label", "")
            executed_steps.append(label)
            if label == "step7":
                return (True, "FILES_CREATED: test_file.py", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=track_and_succeed), \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)):

            run_agentic_bug_orchestrator(**orchestrator_args)

        # FIX VERIFIED: All 11 steps should execute (none skipped)
        assert "step1" in executed_steps, (
            f"Step 1 should be re-executed since its cached output was FAILED, "
            f"but executed steps were: {executed_steps}"
        )
        assert len(executed_steps) == 11, (
            f"All 11 steps should execute when all cached outputs are FAILED, "
            f"got {len(executed_steps)} steps: {executed_steps}"
        )

    def test_partial_failure_state_persistence_round_trip(self, mock_git_repo):
        """
        E2E test: State persistence round-trip with partial failure.

        Run 1: Steps 1-3 succeed, steps 4+ fail -> state saved with last_completed_step=3
        Run 2: Load state -> resume from step 4, re-running failed steps

        Uses REAL save_workflow_state and load_workflow_state (local file).
        """
        from pdd.agentic_bug_orchestrator import (
            run_agentic_bug_orchestrator,
            _get_state_dir,
        )

        orchestrator_args = {
            "issue_url": "https://github.com/test/repo/issues/467",
            "issue_content": "pdd bug falsely reports cached steps",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 467,
            "issue_author": "jiaminc-cmu",
            "issue_title": "pdd bug reporting falsely cached steps",
            "cwd": mock_git_repo,
            "verbose": False,
            "quiet": True,
            "use_github_state": False,
        }

        mock_worktree = mock_git_repo / ".pdd" / "worktrees" / "fix-issue-467"
        mock_worktree.mkdir(parents=True, exist_ok=True)

        # ---- RUN 1: Steps 1-3 succeed, steps 4+ fail ----
        def partial_failure(*args, **kwargs):
            """Steps 1-3 succeed, 4+ fail."""
            label = kwargs.get("label", "")
            step_str = label.replace("step", "").replace("_", ".")
            try:
                step_num = float(step_str)
            except ValueError:
                step_num = 0
            if step_num <= 3:
                return (True, f"Step {step_num} succeeded", 0.1, "gpt-4")
            return (False, "All agent providers failed", 0.0, "")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=partial_failure), \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)):

            run_agentic_bug_orchestrator(**orchestrator_args)

        # Read persisted state
        state_dir = _get_state_dir(mock_git_repo)
        state_file = state_dir / "bug_state_467.json"
        assert state_file.exists(), "State file should exist after Run 1"

        with open(state_file, "r") as f:
            saved_state = json.load(f)

        # FIX VERIFIED: last_completed_step should be 3 (last successful step)
        assert saved_state["last_completed_step"] == 3, (
            f"last_completed_step should be 3 (last successful step), "
            f"got {saved_state['last_completed_step']}"
        )

        # Verify successful steps don't have FAILED prefix
        for step_key in ["1", "2", "3"]:
            assert not saved_state["step_outputs"][step_key].startswith("FAILED:"), (
                f"Step {step_key} succeeded and should not have FAILED prefix"
            )

        # Verify failed steps DO have FAILED prefix
        for step_key in ["4", "5", "5.5"]:
            if step_key in saved_state["step_outputs"]:
                assert saved_state["step_outputs"][step_key].startswith("FAILED:"), (
                    f"Step {step_key} failed and should have FAILED prefix"
                )

        # ---- RUN 2: Resume should re-run from step 4 ----
        executed_steps = []

        def track_and_succeed(*args, **kwargs):
            """Track and succeed for all steps."""
            label = kwargs.get("label", "")
            executed_steps.append(label)
            if label == "step7":
                return (True, "FILES_CREATED: test_file.py", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=track_and_succeed), \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)):

            run_agentic_bug_orchestrator(**orchestrator_args)

        # FIX VERIFIED: Step 4 should be re-run (it failed)
        assert "step4" in executed_steps, (
            f"Step 4 should be re-executed since its cached output was FAILED, "
            f"but executed steps were: {executed_steps}"
        )

        # Steps 1-3 should NOT be re-run (they succeeded)
        assert "step1" not in executed_steps
        assert "step2" not in executed_steps
        assert "step3" not in executed_steps

        # Steps 4, 5, 5.5, 6-10 should all be executed (8 steps)
        assert len(executed_steps) == 8, (
            f"Expected 8 steps (4, 5, 5.5, 6-10) but got {len(executed_steps)}: {executed_steps}"
        )

    def test_state_file_correct_after_consecutive_failures(self, mock_git_repo):
        """
        E2E test: Verify state file content is correct after consecutive failures.

        Exercises a single run where all steps fail and reads the persisted
        state file to confirm last_completed_step=0 and all outputs are FAILED.
        """
        from pdd.agentic_bug_orchestrator import (
            run_agentic_bug_orchestrator,
            _get_state_dir,
        )

        orchestrator_args = {
            "issue_url": "https://github.com/test/repo/issues/467",
            "issue_content": "pdd bug falsely reports cached steps",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 467,
            "issue_author": "jiaminc-cmu",
            "issue_title": "pdd bug reporting falsely cached steps",
            "cwd": mock_git_repo,
            "verbose": False,
            "quiet": True,
            "use_github_state": False,
        }

        mock_worktree = mock_git_repo / ".pdd" / "worktrees" / "fix-issue-467"
        mock_worktree.mkdir(parents=True, exist_ok=True)

        def all_fail(*args, **kwargs):
            """All providers fail."""
            return (False, "All agent providers failed", 0.0, "")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=all_fail), \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)):

            run_agentic_bug_orchestrator(**orchestrator_args)

        # Read the real persisted state file
        state_dir = _get_state_dir(mock_git_repo)
        state_file = state_dir / "bug_state_467.json"
        assert state_file.exists(), "State file should be written by real save_workflow_state"

        with open(state_file, "r") as f:
            state = json.load(f)

        # FIX VERIFIED: last_completed_step should be 0 when all steps fail
        assert state["last_completed_step"] == 0, (
            f"last_completed_step should be 0 when all steps fail, "
            f"got {state['last_completed_step']}"
        )

        # All outputs should be FAILED
        assert len(state["step_outputs"]) > 0, "State should have step outputs"
        for step_key, output in state["step_outputs"].items():
            assert output.startswith("FAILED:"), (
                f"Step {step_key} should be FAILED but got: {output[:50]}"
            )

        # Verify consistency: last_completed_step=0 with all FAILED outputs
        failed_count = sum(
            1 for v in state["step_outputs"].values() if v.startswith("FAILED:")
        )
        assert failed_count == len(state["step_outputs"]), (
            "All step outputs should be FAILED when all providers fail"
        )
