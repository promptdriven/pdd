"""
E2E Test for Issue #579: Full orchestrator crash on re-run with existing branch/worktree

Unlike the unit tests in test_e2e_issue_579_bug_worktree_rerun.py which test
_setup_worktree() in isolation, these tests exercise the full
run_agentic_bug_orchestrator() flow — the code path a user triggers when
running `pdd bug <issue-url>` a second time.

Bug Context:
-----------
When `pdd bug` is run a second time on the same issue:
- Path 1 (fresh re-run): The orchestrator reaches Step 5.5, calls
  _setup_worktree(resume_existing=False), but the branch can't be deleted
  (checked out in main repo). The bug orchestrator returns a hard error
  instead of falling back to `git worktree add --force`.
- Path 2 (resume re-run): The orchestrator loads cached state showing
  steps 1-5.5+ completed, tries to recreate the worktree with
  _setup_worktree(resume_existing=True), but uses `git worktree add`
  without `--force`, failing on stale worktree associations.

The change orchestrator handles both cases correctly (fix from #445).
These E2E tests verify the bug at the orchestrator level, matching the
pattern from test_e2e_issue_445_worktree_resume.py.
"""

import pytest
import shutil
import subprocess
from pathlib import Path
from unittest.mock import patch


@pytest.fixture
def git_repo_with_checked_out_fix_branch(tmp_path):
    """Create a git repo where fix/issue-579 is checked out (simulating prior pdd bug run).

    This represents the scenario where `pdd bug` was run once, created
    the fix/issue-579 branch with some work, and the user runs it again
    from a checkout of that branch.
    """
    main_repo = tmp_path / "main_repo"
    main_repo.mkdir()

    subprocess.run(["git", "init", "-b", "main"], cwd=main_repo, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=main_repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=main_repo, check=True)

    (main_repo / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=main_repo, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=main_repo, check=True, capture_output=True)

    # Create and checkout fix/issue-579 branch (simulating prior pdd bug run)
    subprocess.run(["git", "checkout", "-b", "fix/issue-579"], cwd=main_repo, check=True, capture_output=True)
    (main_repo / "fix.py").write_text("# Fix for issue 579\n")
    subprocess.run(["git", "add", "fix.py"], cwd=main_repo, check=True)
    subprocess.run(["git", "commit", "-m", "Work from prior pdd bug run"], cwd=main_repo, check=True, capture_output=True)

    return {"main_repo": main_repo}


@pytest.fixture
def git_repo_with_stale_worktree_for_resume(tmp_path):
    """Create a git repo with a stale worktree for fix/issue-579 (simulating resume).

    This represents the scenario where a prior `pdd bug` run completed some steps,
    saved state, and the worktree was cleaned up, but git still has stale worktree
    metadata for the branch. On resume, the orchestrator calls
    _setup_worktree(resume_existing=True) which uses `git worktree add` without
    --force, failing on the stale worktree association.
    """
    main_repo = tmp_path / "main_repo"
    main_repo.mkdir()

    subprocess.run(["git", "init", "-b", "main"], cwd=main_repo, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=main_repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=main_repo, check=True)

    (main_repo / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=main_repo, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=main_repo, check=True, capture_output=True)

    # Create worktree for fix/issue-579 (simulating prior pdd bug run)
    worktree_dir = main_repo / ".pdd" / "worktrees" / "fix-issue-579"
    worktree_dir.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["git", "worktree", "add", "-b", "fix/issue-579", str(worktree_dir), "HEAD"],
        cwd=main_repo, check=True, capture_output=True
    )
    (worktree_dir / "fix.py").write_text("# Fix for issue 579\n")
    subprocess.run(["git", "add", "fix.py"], cwd=worktree_dir, check=True)
    subprocess.run(["git", "commit", "-m", "Work from prior run"], cwd=worktree_dir, check=True, capture_output=True)

    # Create a second worktree to leave stale metadata, then remove the directory
    stale_wt_path = main_repo / ".pdd" / "worktrees" / "fix-issue-579-stale"
    subprocess.run(
        ["git", "worktree", "remove", str(worktree_dir), "--force"],
        cwd=main_repo, check=True, capture_output=True
    )
    # Re-add to create a second worktree ref, then remove just the directory
    subprocess.run(
        ["git", "worktree", "add", "--force", str(stale_wt_path), "fix/issue-579"],
        cwd=main_repo, check=True, capture_output=True
    )
    # Delete directory but don't prune — git still thinks branch is in use
    shutil.rmtree(stale_wt_path)

    # Verify branch exists but worktree directory is gone
    result = subprocess.run(
        ["git", "show-ref", "--verify", "refs/heads/fix/issue-579"],
        cwd=main_repo, capture_output=True
    )
    assert result.returncode == 0, "Branch should still exist"
    assert not stale_wt_path.exists(), "Stale worktree directory should be gone"

    return {"main_repo": main_repo}


@pytest.mark.e2e
class TestIssue579OrchestratorRerunE2E:
    """
    E2E tests for Issue #579: Full orchestrator crash on re-run.

    These tests call run_agentic_bug_orchestrator() (the user-facing entry point)
    with mocked LLM calls but real git/worktree operations, verifying that the
    full code path handles re-runs correctly.
    """

    def test_orchestrator_fresh_rerun_crashes_on_checked_out_branch(
        self, git_repo_with_checked_out_fix_branch, monkeypatch
    ):
        """
        E2E Bug Test (Path 1): Full orchestrator fails on re-run when branch is checked out.

        Scenario: User runs `pdd bug <issue>` a second time. The orchestrator reaches
        Step 5.5 and calls _setup_worktree(resume_existing=False). Since the branch
        fix/issue-579 is checked out, _delete_branch() fails, and the bug orchestrator
        returns a hard error instead of falling back to `git worktree add --force`.

        Current (buggy) behavior: Orchestrator returns (False, "Failed to create worktree: ...")
        Expected (fixed) behavior: Orchestrator succeeds, creates worktree with --force
        """
        from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

        main_repo = git_repo_with_checked_out_fix_branch["main_repo"]
        monkeypatch.chdir(main_repo)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        def mock_load_state(*args, **kwargs):
            """No cached state — fresh run from step 1."""
            return None, None

        def mock_save_state(*args, **kwargs):
            return None

        def mock_clear_state(*args, **kwargs):
            pass

        step_calls = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM calls — return success for all steps.

            Steps 1-5 produce outputs that don't trigger any hard-stop conditions.
            Step 5.5 triggers worktree creation. If the worktree bug is present,
            the orchestrator will fail before reaching step 5.5's LLM call.
            """
            step_calls.append(label)

            # Step 1: Duplicate check — must NOT contain "Duplicate of #"
            if label == "step1":
                return (True, "No duplicates found. This is a new issue.", 0.001, "mock-model")

            # Step 2: Docs check — must NOT contain "Feature Request" or "User Error"
            if label == "step2":
                return (True, "This is a confirmed bug, not user error.", 0.001, "mock-model")

            # Step 3: Triage — must NOT contain "Needs More Info"
            if label == "step3":
                return (True, "Sufficient information. Proceeding with investigation.", 0.001, "mock-model")

            # Step 5.5: Prompt classification — must NOT contain "PROMPT_REVIEW:"
            if label == "step5_5":
                return (True, "DEFECT_TYPE: code\nThe bug is in the code.", 0.001, "mock-model")

            # Step 7: Must produce FILES_CREATED to avoid hard stop
            if label == "step7":
                return (True, "FILES_CREATED: tests/test_fix.py\nTest generated.", 0.001, "mock-model")

            # Step 8: Must NOT contain "FAIL: Test does not work as expected"
            if label == "step8":
                return (True, "Test correctly catches the bug.", 0.001, "mock-model")

            # Step 9: E2E test
            if label == "step9":
                return (True, "E2E_SKIP: Simple bug, no E2E test needed.", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        with patch('pdd.agentic_bug_orchestrator.load_workflow_state', side_effect=mock_load_state):
            with patch('pdd.agentic_bug_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_bug_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                    with patch('pdd.agentic_bug_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
                        success, message, cost, model, files = run_agentic_bug_orchestrator(
                            issue_url="https://github.com/test/repo/issues/579",
                            issue_content="Bug: re-run crashes with worktree conflict",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=579,
                            issue_author="testuser",
                            issue_title="Re-run crashes with git worktree conflict",
                            cwd=main_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                        )

        # The orchestrator should succeed (all 11 steps) even when the branch
        # is already checked out. On buggy code, it fails at worktree creation.
        assert success, (
            f"Orchestrator should succeed on re-run with checked-out branch. "
            f"Got failure: {message!r}. "
            f"Bug: _setup_worktree returns hard error when _delete_branch() fails "
            f"instead of falling back to 'git worktree add --force'. "
            f"Steps executed: {step_calls}"
        )

        # Verify we got past Step 5.5 (where worktree is created)
        assert "step5_5" in step_calls, (
            f"Should have reached step 5.5 (worktree creation point). "
            f"Steps executed: {step_calls}"
        )

        # Clean up worktree
        wt_path = main_repo / ".pdd" / "worktrees" / "fix-issue-579"
        subprocess.run(["git", "worktree", "remove", str(wt_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)

    def test_orchestrator_resume_crashes_on_stale_worktree(
        self, git_repo_with_stale_worktree_for_resume, monkeypatch
    ):
        """
        E2E Bug Test (Path 2): Full orchestrator fails on resume when branch has stale worktree.

        Scenario: Prior `pdd bug` run completed steps 1-7, saved state, and the worktree
        was cleaned up. The branch still has stale worktree metadata. On resume, the
        orchestrator calls _setup_worktree(resume_existing=True) which uses
        `git worktree add <path> <branch>` without --force, crashing because git thinks
        the branch is still in use by the stale worktree.

        Current (buggy) behavior: Orchestrator returns (False, "Failed to recreate worktree...")
        Expected (fixed) behavior: Orchestrator recreates worktree with --force and resumes
        """
        from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

        main_repo = git_repo_with_stale_worktree_for_resume["main_repo"]
        monkeypatch.chdir(main_repo)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # The worktree path that should be recreated
        expected_wt_path = main_repo / ".pdd" / "worktrees" / "fix-issue-579"

        # Simulate cached state: steps 1-7 complete, worktree path saved
        # The worktree directory no longer exists, so the orchestrator will
        # try to recreate it with _setup_worktree(resume_existing=True)
        cached_state = {
            "workflow": "bug",
            "issue_number": 579,
            "last_completed_step": 7,
            "step_outputs": {
                "1": "No duplicates found",
                "2": "Confirmed bug",
                "3": "Sufficient information",
                "4": "Bug reproduced",
                "5": "Root cause identified",
                "5.5": "DEFECT_TYPE: code",
                "6": "Test plan created",
                "7": "FILES_CREATED: tests/test_fix.py",
            },
            "total_cost": 0.50,
            "model_used": "mock-model",
            "changed_files": ["tests/test_fix.py"],
            # Point to a worktree path that no longer exists on disk
            "worktree_path": str(expected_wt_path),
        }

        def mock_load_state(*args, **kwargs):
            return cached_state, "mock-comment-id"

        def mock_save_state(*args, **kwargs):
            return None

        def mock_clear_state(*args, **kwargs):
            pass

        step_calls = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            step_calls.append(label)

            # Step 8: Verify test
            if label == "step8":
                return (True, "Test correctly catches the bug.", 0.001, "mock-model")

            # Step 9: E2E test
            if label == "step9":
                return (True, "E2E_SKIP: Simple bug, no E2E test needed.", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        with patch('pdd.agentic_bug_orchestrator.load_workflow_state', side_effect=mock_load_state):
            with patch('pdd.agentic_bug_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_bug_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                    with patch('pdd.agentic_bug_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
                        success, message, cost, model, files = run_agentic_bug_orchestrator(
                            issue_url="https://github.com/test/repo/issues/579",
                            issue_content="Bug: re-run crashes with worktree conflict",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=579,
                            issue_author="testuser",
                            issue_title="Re-run crashes with git worktree conflict",
                            cwd=main_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                        )

        # The orchestrator should succeed on resume even with stale worktree metadata.
        # On buggy code, it fails at worktree recreation with:
        # "Failed to recreate worktree on resume: Failed to create worktree: ..."
        assert success, (
            f"Orchestrator should succeed on resume with stale worktree. "
            f"Got failure: {message!r}. "
            f"Bug: _setup_worktree(resume_existing=True) uses 'git worktree add' "
            f"without '--force', crashing when branch has stale worktree associations. "
            f"Steps executed: {step_calls}"
        )

        # Verify we resumed from step 8 (steps 1-7 were cached)
        assert "step8" in step_calls, (
            f"Should have resumed at step 8. Steps executed: {step_calls}"
        )

        # Clean up worktree
        subprocess.run(["git", "worktree", "remove", str(expected_wt_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)
        subprocess.run(["git", "worktree", "prune"],
                       cwd=main_repo, check=False, capture_output=True)

    def test_change_orchestrator_rerun_succeeds_as_control(
        self, git_repo_with_checked_out_fix_branch, monkeypatch
    ):
        """
        Control Test: The change orchestrator handles the same re-run scenario correctly.

        This proves the bug is specific to the bug orchestrator and that the
        change orchestrator's --force pattern (from #445) works at the full
        orchestrator level, not just at the _setup_worktree() level.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        main_repo = git_repo_with_checked_out_fix_branch["main_repo"]
        monkeypatch.chdir(main_repo)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Create the change/ branch too (change orchestrator uses change/issue-NNN)
        subprocess.run(
            ["git", "branch", "change/issue-579"],
            cwd=main_repo, check=True, capture_output=True
        )

        # Cached state: steps 1-10 complete, needs step 11 (which requires worktree)
        cached_state = {
            "last_completed_step": 10,
            "step_outputs": {
                "1": "No duplicates found",
                "2": "Documentation reviewed",
                "3": "Research complete",
                "4": "Requirements clarified",
                "5": "Docs changes identified",
                "6": "Dev units identified",
                "7": "Architecture reviewed",
                "8": "Prompt changes analyzed",
                "9": "Changes implemented",
                "10": "Architecture updated",
            },
            "total_cost": 0.50,
            "model_used": "mock-model",
            "worktree_path": None,
            "issue_updated_at": "2024-01-01T00:00:00Z",
        }

        def mock_load_state(*args, **kwargs):
            return cached_state, "mock-comment-id"

        def mock_save_state(*args, **kwargs):
            pass

        def mock_clear_state(*args, **kwargs):
            pass

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            return (True, f"Mock success for {label}", 0.001, "mock-model")

        with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                    with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
                        success, message, cost, model, files = run_agentic_change_orchestrator(
                            issue_url="https://github.com/test/repo/issues/579",
                            issue_content="Control test for worktree re-run",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=579,
                            issue_author="testuser",
                            issue_title="Control: change orchestrator handles re-run",
                            issue_updated_at="2024-01-01T00:00:00Z",
                            cwd=main_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                        )

        # The change orchestrator should succeed — it has the --force fix from #445
        assert success, (
            f"Change orchestrator should handle re-run with checked-out branch. "
            f"Got: {message!r}. This control test validates that the --force pattern works."
        )

        # Clean up
        wt_path = main_repo / ".pdd" / "worktrees" / "change-issue-579"
        subprocess.run(["git", "worktree", "remove", str(wt_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)
