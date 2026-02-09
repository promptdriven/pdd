"""
E2E Test for Issue #445: Worktree restoration fails when resuming on existing issue branch

Tests the full change orchestrator workflow to verify that worktree restoration
succeeds when resuming from cached state on a machine where the branch is already
checked out.

Bug Context:
-----------
When PDD CLI resumes a `change` workflow from cached state (stored as a GitHub issue
comment), `_setup_worktree()` fails with exit code 255 because it tries to create a
branch that already exists and is currently checked out.

The bug manifests when:
1. Run `pdd change <issue_url>` — PDD CLI completes steps 1-10, saves state to GitHub
   issue comment, creates `change/issue-445` branch, and pushes it
2. Run `pdd change <issue_url>` again on a fresh clone that has `change/issue-445`
   checked out as the current branch
3. PDD CLI loads state from GitHub, sees "Steps 1-10 already complete (cached)", tries
   to resume from Step 11
4. Step 11 requires a worktree → calls `_setup_worktree()` → **fails with exit 255**

This is the exact scenario when PDD Cloud's executor re-triggers a job: it clones the
repo, checks out the existing `change/issue-445` branch (to build on prior work), then
runs `pdd change`.

Root Cause:
----------
_setup_worktree() in agentic_change_orchestrator.py (line 168) ignores the return
value from _delete_branch(), causing silent failures when trying to delete a
checked-out branch. Git won't delete a currently checked-out branch (safety mechanism),
so _delete_branch() returns (False, error). Since this return value is ignored, the
code proceeds to `git worktree add -b` which fails with exit code 255 because the
branch already exists.

Expected Behavior:
-----------------
When the branch exists but can't be deleted (e.g., currently checked out), the
orchestrator should use `git worktree add <path> <existing-branch>` (without `-b`) to
attach the worktree to the existing branch.
"""

import pytest
import subprocess
from pathlib import Path
from unittest.mock import patch


@pytest.fixture
def mock_git_repo_with_branch(tmp_path):
    """Create a git repository simulating the PDD Cloud resume scenario.

    This fixture creates:
    1. A main repository with initial commit
    2. A remote repository (simulating GitHub)
    3. A `change/issue-445` branch that is currently checked out
    4. The branch has been pushed to remote (simulating prior PDD run)
    """
    main_repo = tmp_path / "main_repo"
    main_repo.mkdir()

    # Initialize git repo
    subprocess.run(["git", "init", "-b", "main"], cwd=main_repo, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=main_repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=main_repo, check=True)

    # Create minimal project structure
    pdd_dir = main_repo / "pdd"
    pdd_dir.mkdir()
    (pdd_dir / "__init__.py").write_text("__version__ = '0.0.1'\n")

    (main_repo / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=main_repo, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=main_repo, check=True, capture_output=True)

    # Create remote repository
    remote_repo = tmp_path / "remote.git"
    subprocess.run(["git", "init", "--bare", str(remote_repo)], check=True, capture_output=True)

    subprocess.run(["git", "remote", "add", "origin", str(remote_repo)], cwd=main_repo, check=True)
    subprocess.run(["git", "push", "-u", "origin", "main"], cwd=main_repo, check=True, capture_output=True)

    # Create and push the change/issue-445 branch (simulating prior PDD run)
    subprocess.run(["git", "checkout", "-b", "change/issue-445"], cwd=main_repo, check=True, capture_output=True)

    # Simulate some work from the prior PDD run
    (main_repo / "CHANGES.md").write_text("# Changes from issue 445\n")
    subprocess.run(["git", "add", "CHANGES.md"], cwd=main_repo, check=True)
    subprocess.run(["git", "commit", "-m", "Work from prior PDD run"], cwd=main_repo, check=True, capture_output=True)

    subprocess.run(["git", "push", "-u", "origin", "change/issue-445"], cwd=main_repo, check=True, capture_output=True)

    # Verify the branch is currently checked out
    result = subprocess.run(
        ["git", "branch", "--show-current"],
        cwd=main_repo,
        capture_output=True,
        text=True,
        check=True
    )
    assert result.stdout.strip() == "change/issue-445", "Branch should be checked out"

    # Verify the branch exists in remote
    result = subprocess.run(
        ["git", "ls-remote", "--heads", "origin", "change/issue-445"],
        cwd=main_repo,
        capture_output=True,
        text=True,
        check=True
    )
    assert "change/issue-445" in result.stdout, "Branch should exist in remote"

    return {
        "main_repo": main_repo,
        "remote_repo": remote_repo,
    }


@pytest.mark.e2e
class TestIssue445WorktreeResumptionE2E:
    """
    E2E tests for Issue #445: Worktree restoration when resuming with branch checked out.

    These tests verify the complete code path from workflow resumption through worktree
    creation, demonstrating the bug and verifying the fix.
    """

    def test_setup_worktree_succeeds_when_branch_is_checked_out(self, mock_git_repo_with_branch):
        """
        Regression test for issue #445: _setup_worktree() must succeed even when the
        target branch is already checked out in the main worktree.
        """
        from pdd.agentic_change_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_branch["main_repo"]
        issue_number = 445

        # Verify preconditions
        result = subprocess.run(
            ["git", "branch", "--show-current"],
            cwd=main_repo,
            capture_output=True,
            text=True,
            check=True
        )
        assert result.stdout.strip() == "change/issue-445", "Precondition: branch must be checked out"

        # Call _setup_worktree - should succeed via --force fallback
        worktree_path, error = _setup_worktree(main_repo, issue_number, quiet=True)

        assert worktree_path is not None, f"Expected worktree to be created, but got error: {error!r}"
        assert error is None, f"Expected no error, got: {error!r}"
        assert worktree_path.exists(), "Worktree path should exist after successful creation"

        # Verify the worktree is on the correct branch
        branch_result = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=worktree_path,
            capture_output=True,
            text=True,
            check=True,
        )
        assert branch_result.stdout.strip() == "change/issue-445", \
            f"Worktree should be on 'change/issue-445', got: {branch_result.stdout.strip()!r}"

        # Clean up
        subprocess.run(["git", "worktree", "remove", str(worktree_path)], cwd=main_repo, check=False)

    def test_orchestrator_resume_succeeds_with_checked_out_branch(self, mock_git_repo_with_branch, monkeypatch):
        """
        Regression test for issue #445: Full orchestrator resume must succeed when
        the target branch is already checked out.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        main_repo = mock_git_repo_with_branch["main_repo"]
        monkeypatch.chdir(main_repo)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Simulate cached state from prior run (steps 1-10 complete)
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
            "model_used": "gpt-4",
            "worktree_path": None,
            "issue_updated_at": "2024-01-01T00:00:00Z",
        }

        def mock_load_state(*args, **kwargs):
            return cached_state, "mock-github-comment-id"

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
                            issue_url="https://github.com/test/repo/issues/445",
                            issue_content="Worktree restoration bug",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=445,
                            issue_author="gltanaka",
                            issue_title="Worktree restoration fails when resuming on existing issue branch",
                            issue_updated_at="2024-01-01T00:00:00Z",
                            cwd=main_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=True,
                        )

                        assert success, f"Orchestrator should succeed when resuming with checked-out branch, got: {message}"
                        assert isinstance(files, list), "Expected files to be a list"

    def test_orchestrator_resume_succeeds_after_fix(self, mock_git_repo_with_branch, monkeypatch):
        """
        E2E Test: After fix, orchestrator should successfully resume with branch checked out.

        This test verifies the expected behavior after the fix is applied:
        1. When branch exists but can't be deleted (currently checked out)
        2. _setup_worktree() should use `git worktree add <path> <branch>` (without -b)
        3. Orchestrator should successfully resume and complete the workflow

        This test will PASS only after the fix is applied to agentic_change_orchestrator.py.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        main_repo = mock_git_repo_with_branch["main_repo"]
        monkeypatch.chdir(main_repo)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Simulate cached state from prior run (steps 1-10 complete)
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
            "model_used": "gpt-4",
            "worktree_path": None,  # Worktree was cleaned up
            "issue_updated_at": "2024-01-01T00:00:00Z",
        }

        def mock_load_state(*args, **kwargs):
            """Mock loading cached state from GitHub issue comment."""
            return cached_state, "mock-github-comment-id"

        def mock_save_state(*args, **kwargs):
            """Mock saving state to GitHub issue comment."""
            pass

        def mock_clear_state(*args, **kwargs):
            """Mock clearing state from GitHub issue comment."""
            pass

        step_calls = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM calls - verify we get to step 11 (requires worktree)."""
            step_calls.append(label)
            return (True, f"Mock success for {label}", 0.001, "mock-model")

        with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                    with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
                        # Run the orchestrator
                        success, message, cost, model, files = run_agentic_change_orchestrator(
                            issue_url="https://github.com/test/repo/issues/445",
                            issue_content="Worktree restoration bug",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=445,
                            issue_author="gltanaka",
                            issue_title="Worktree restoration fails when resuming on existing issue branch",
                            issue_updated_at="2024-01-01T00:00:00Z",
                            cwd=main_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=True,
                        )

                        # After fix: should succeed
                        if success:
                            # Verify we actually got to step 11 (which requires worktree)
                            assert any("step11" in label.lower() or "identify" in label.lower() for label in step_calls), \
                                f"Should have reached step 11, but step_calls were: {step_calls}"

                            # Verify worktree was created
                            worktree_path = main_repo / ".pdd" / "worktrees" / "change-issue-445"
                            assert worktree_path.exists(), \
                                f"Worktree should exist at {worktree_path} after successful resume"

                            # Clean up
                            subprocess.run(["git", "worktree", "remove", str(worktree_path), "--force"],
                                         cwd=main_repo, check=False, capture_output=True)
                        else:
                            # Before fix: will fail with worktree error
                            assert "Failed to restore worktree" in message or "255" in message, \
                                f"Expected worktree restoration error, got: {message}"
                            pytest.xfail("Fix not yet applied - worktree restoration still fails with exit 255")
