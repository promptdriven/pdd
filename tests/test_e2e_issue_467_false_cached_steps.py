"""
E2E Test for Issue #467: pdd bug falsely reporting cached steps

Tests the full bug orchestrator workflow to verify that when all LLM providers
fail for every step, the saved workflow state does not falsely claim steps are
"cached" (completed) on subsequent runs.

Bug Context:
-----------
When `pdd bug` is run and ALL agent providers fail for every step:
1. The orchestrator runs through all 11 steps, each returning failure
2. Each failed step sets `last_completed_step_to_save = step_num - 1`
3. Because the loop never breaks, this "ratchets" the value up to 5.5
4. The state is saved with `last_completed_step=5.5` to local file / GitHub
5. On the NEXT `pdd bug` run, `load_workflow_state` reads this state
6. The orchestrator prints "Resuming from step 6 (steps 1-5.5 cached)"
7. Steps 1-5.5 are skipped even though NONE of them succeeded

This E2E test exercises the REAL state persistence round-trip:
- Run 1: All providers fail → real save_workflow_state writes corrupted state
- Run 2: real load_workflow_state reads it → orchestrator blindly resumes from step 6

Unlike the unit tests in test_agentic_bug_orchestrator.py which mock
save/load_workflow_state, this test uses the real local file persistence
to verify the bug manifests through the full code path.

Root Cause:
----------
Two interacting defects in agentic_bug_orchestrator.py:
1. Failure handling (lines 514-522): `last_completed_step_to_save = step_num - 1`
   assumes the previous step succeeded, which is false with consecutive failures.
2. Resume logic (line 255): `load_workflow_state` returns raw state without
   validating that cached step outputs don't have FAILED: prefixes.
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
    E2E tests for Issue #467: False cached steps due to ratchet effect.

    These tests exercise the full state persistence round-trip (save → load)
    to verify the bug manifests end-to-end, not just at the unit level.
    """

    def test_all_failures_then_resume_skips_steps(self, mock_git_repo):
        """
        E2E test: Two consecutive orchestrator runs demonstrate the bug.

        Run 1: All LLM providers fail → state saved with last_completed_step=5.5
        Run 2: Orchestrator loads state → skips to step 6, missing steps 1-5.5

        This test uses REAL save_workflow_state (local file) and REAL
        load_workflow_state to exercise the full persistence round-trip.
        Only LLM calls, GitHub state, and console are mocked.
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
            "use_github_state": False,  # Use local file only (no GitHub API)
        }

        # Create worktree directory so _setup_worktree mock works
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

        # BUG ASSERTION: The ratchet effect causes last_completed_step to be 5.5
        # even though ALL steps failed. Correct value should be 0.
        assert saved_state["last_completed_step"] != 0, (
            "If this assertion fails, the bug has been FIXED. "
            "last_completed_step correctly stayed at 0 despite all steps failing. "
            "Update this test to verify the fix instead."
        )
        assert saved_state["last_completed_step"] == 5.5, (
            f"Expected ratcheted value of 5.5, got {saved_state['last_completed_step']}"
        )

        # Verify all step outputs have FAILED: prefix
        for step_key, output in saved_state["step_outputs"].items():
            assert output.startswith("FAILED:"), (
                f"Step {step_key} should have FAILED prefix, got: {output[:50]}"
            )

        # ---- RUN 2: Resume from corrupted state ----
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
             patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)):

            success, msg, cost, model, files = run_agentic_bug_orchestrator(
                **orchestrator_args
            )

        # BUG ASSERTION: The orchestrator should re-run from step 1 since all
        # cached outputs are FAILED, but due to the blind resume bug, it skips
        # to step 6 and only executes steps 6-10.
        assert "step1" not in executed_steps, (
            "If this assertion fails, the bug has been FIXED. "
            "The orchestrator correctly re-ran step 1 despite corrupted state. "
            "Update this test to verify the fix instead."
        )

        # Verify we skipped steps 1-5 (the blind resume bug)
        skipped_steps = {"step1", "step2", "step3", "step4", "step5", "step5_5"}
        executed_set = set(executed_steps)
        actually_skipped = skipped_steps - executed_set

        assert len(actually_skipped) > 0, (
            "At least some steps should be skipped due to the blind resume bug. "
            "If no steps were skipped, the bug may have been fixed."
        )

        # The bug causes only steps 6-10 to execute (5 steps instead of 11)
        assert len(executed_steps) < 11, (
            f"Due to the blind resume bug, fewer than 11 steps should execute. "
            f"Got {len(executed_steps)} steps: {executed_steps}"
        )

    def test_partial_failure_state_persistence_round_trip(self, mock_git_repo):
        """
        E2E test: State persistence round-trip with partial failure.

        Run 1: Steps 1-3 succeed, steps 4+ fail → state saved
        Run 2: Load state → verify resume behavior

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

        # BUG ASSERTION: The ratchet effect causes last_completed_step > 3
        # even though step 3 is the last successful step.
        assert saved_state["last_completed_step"] != 3, (
            "If this assertion fails, the bug has been FIXED. "
            "last_completed_step correctly stayed at 3. "
            "Update this test to verify the fix instead."
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

        # ---- RUN 2: Resume from corrupted state ----
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

        # BUG ASSERTION: Step 4 should be re-run (it failed), but the blind
        # resume bug skips it because last_completed_step > 4.
        assert "step4" not in executed_steps, (
            "If this assertion fails, the bug has been FIXED. "
            "The orchestrator correctly re-ran step 4. "
            "Update this test to verify the fix instead."
        )

        # Steps 1-3 should NOT be re-run (they succeeded)
        assert "step1" not in executed_steps, (
            "Step 1 succeeded and should not be re-run on resume"
        )
        assert "step2" not in executed_steps, (
            "Step 2 succeeded and should not be re-run on resume"
        )
        assert "step3" not in executed_steps, (
            "Step 3 succeeded and should not be re-run on resume"
        )

    def test_state_file_contains_ratcheted_value_after_consecutive_failures(
        self, mock_git_repo
    ):
        """
        E2E test: Directly verify the state file content after consecutive failures.

        This test exercises a single run where all steps fail and then reads
        the persisted state file to confirm the ratchet effect has written
        an incorrect last_completed_step value to disk.

        This differs from the unit test by using REAL save_workflow_state
        to write the actual JSON file, not capturing mock calls.
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

        # The state file on disk should reflect the bug:
        # last_completed_step=5.5 even though all steps failed
        assert state["last_completed_step"] == 5.5, (
            f"BUG VERIFICATION: Expected ratcheted last_completed_step=5.5 in "
            f"persisted state file, got {state['last_completed_step']}. "
            f"If value is 0, the bug has been fixed."
        )

        # All outputs should be FAILED
        assert len(state["step_outputs"]) > 0, "State should have step outputs"
        for step_key, output in state["step_outputs"].items():
            assert output.startswith("FAILED:"), (
                f"Step {step_key} should be FAILED but got: {output[:50]}"
            )

        # The combination of last_completed_step=5.5 + all FAILED outputs
        # is the exact corrupted state that causes the false cache on resume
        failed_count = sum(
            1 for v in state["step_outputs"].values() if v.startswith("FAILED:")
        )
        assert failed_count == len(state["step_outputs"]), (
            "ALL step outputs are FAILED, yet last_completed_step claims 5.5 "
            "steps completed successfully — this is the issue #467 bug."
        )
