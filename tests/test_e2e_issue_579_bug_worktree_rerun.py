"""
E2E Test for Issue #579: pdd bug/fix re-run on same issue crashes with git worktree conflict

Tests the bug orchestrator's _setup_worktree() to verify it handles re-runs gracefully
when a branch already exists and cannot be deleted.

Bug Context:
-----------
When `pdd bug` or `pdd fix` is run a second time on the same issue, it crashes because:
1. Path 1 (line 167-169): _setup_worktree() returns a hard error when _delete_branch()
   fails (e.g., branch is currently checked out). The change orchestrator (fixed in #445)
   falls back to `git worktree add --force` instead.
2. Path 2 (line 177-178): The resume path uses `git worktree add` without `--force`,
   so git refuses when the branch is already associated with another worktree.

Root Cause:
----------
Issue #445 fixed this exact bug in agentic_change_orchestrator.py and
agentic_test_orchestrator.py, but the fix was never ported to agentic_bug_orchestrator.py.

The change orchestrator's pattern:
- Check _delete_branch() return value; only set branch_exists=False on success
- If branch still exists (couldn't delete), use `git worktree add --force <path> <branch>`
- If branch doesn't exist, create new with `git worktree add -b <branch> <path> HEAD`

The bug orchestrator's (broken) pattern:
- If _delete_branch() fails, return hard error (None, "Failed to delete existing branch: ...")
- Resume path uses `git worktree add` without `--force`

Expected Behavior:
-----------------
_setup_worktree() should succeed when re-run on the same issue by using `--force` to
attach the worktree to the existing branch when it can't be deleted.
"""

import pytest
import subprocess
from pathlib import Path
from unittest.mock import patch


@pytest.fixture
def mock_git_repo_with_checked_out_branch(tmp_path):
    """Create a git repository where the fix/issue-579 branch is currently checked out.

    This simulates the scenario where `pdd bug` was run once, creating the
    fix/issue-579 branch, and the user runs it again on the same issue while
    the branch is still checked out (can't be deleted).
    """
    main_repo = tmp_path / "main_repo"
    main_repo.mkdir()

    # Initialize git repo
    subprocess.run(["git", "init", "-b", "main"], cwd=main_repo, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=main_repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=main_repo, check=True)

    # Create initial commit
    (main_repo / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=main_repo, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=main_repo, check=True, capture_output=True)

    # Create and checkout fix/issue-579 branch (simulating prior pdd bug run)
    subprocess.run(["git", "checkout", "-b", "fix/issue-579"], cwd=main_repo, check=True, capture_output=True)

    # Add some work on the branch (simulating prior pdd bug output)
    (main_repo / "fix.py").write_text("# Fix for issue 579\n")
    subprocess.run(["git", "add", "fix.py"], cwd=main_repo, check=True)
    subprocess.run(["git", "commit", "-m", "Work from prior pdd bug run"], cwd=main_repo, check=True, capture_output=True)

    # Verify precondition: branch is checked out
    result = subprocess.run(
        ["git", "branch", "--show-current"],
        cwd=main_repo, capture_output=True, text=True, check=True
    )
    assert result.stdout.strip() == "fix/issue-579", "Precondition: branch must be checked out"

    return {"main_repo": main_repo}


@pytest.fixture
def mock_git_repo_with_stale_worktree(tmp_path):
    """Create a git repository with a stale worktree referencing fix/issue-579.

    This simulates the scenario where a prior `pdd bug` run created a worktree
    for the branch, but the worktree directory was cleaned up while git still
    has the branch registered to that worktree path. On re-run, `git worktree add`
    (without --force) refuses because the branch is still associated with the
    stale worktree entry.
    """
    main_repo = tmp_path / "main_repo"
    main_repo.mkdir()

    # Initialize git repo
    subprocess.run(["git", "init", "-b", "main"], cwd=main_repo, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=main_repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=main_repo, check=True)

    # Create initial commit
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

    # Add some work in the worktree
    (worktree_dir / "fix.py").write_text("# Fix for issue 579\n")
    subprocess.run(["git", "add", "fix.py"], cwd=worktree_dir, check=True)
    subprocess.run(["git", "commit", "-m", "Work from prior run"], cwd=worktree_dir, check=True, capture_output=True)

    # Remove the worktree via git (clean removal)
    subprocess.run(
        ["git", "worktree", "remove", str(worktree_dir), "--force"],
        cwd=main_repo, check=True, capture_output=True
    )

    # Verify the branch still exists but worktree is gone
    result = subprocess.run(
        ["git", "show-ref", "--verify", "refs/heads/fix/issue-579"],
        cwd=main_repo, capture_output=True
    )
    assert result.returncode == 0, "Branch should still exist after worktree removal"
    assert not worktree_dir.exists(), "Worktree directory should be removed"

    return {"main_repo": main_repo}


@pytest.fixture
def mock_git_repo_clean(tmp_path):
    """Create a clean git repository with no fix/issue-579 branch.

    This simulates the first-ever run of `pdd bug` on an issue — no
    prior branch or worktree exists.
    """
    main_repo = tmp_path / "main_repo"
    main_repo.mkdir()

    subprocess.run(["git", "init", "-b", "main"], cwd=main_repo, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=main_repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=main_repo, check=True)

    (main_repo / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=main_repo, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=main_repo, check=True, capture_output=True)

    return {"main_repo": main_repo}


@pytest.mark.e2e
class TestIssue579BugWorktreeRerunE2E:
    """
    E2E tests for Issue #579: pdd bug/fix re-run crashes with git worktree conflict.

    These tests verify that the bug orchestrator's _setup_worktree() handles re-runs
    gracefully by using the same --force fallback pattern as the change orchestrator.
    """

    def test_path1_fresh_run_branch_checked_out_returns_error(self, mock_git_repo_with_checked_out_branch):
        """
        Bug test for Path 1: _setup_worktree() returns hard error when branch
        can't be deleted because it's currently checked out.

        Current (buggy) behavior: returns (None, "Failed to delete existing branch: ...")
        Expected (fixed) behavior: falls back to `git worktree add --force` and succeeds.

        This test FAILS on the current buggy code (asserts success but gets error).
        """
        from pdd.agentic_bug_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_checked_out_branch["main_repo"]

        # Verify precondition: branch is checked out (can't be deleted)
        result = subprocess.run(
            ["git", "branch", "--show-current"],
            cwd=main_repo, capture_output=True, text=True, check=True
        )
        assert result.stdout.strip() == "fix/issue-579", "Precondition: branch must be checked out"

        # Call _setup_worktree — on buggy code this returns (None, error)
        # After fix, it should succeed by using --force fallback
        worktree_path, error = _setup_worktree(main_repo, 579, quiet=True)

        # Assert the fix: should succeed, not return error
        assert worktree_path is not None, (
            f"_setup_worktree() should succeed when branch exists but can't be deleted. "
            f"Got error: {error!r}. "
            f"Bug: returns hard error instead of falling back to 'git worktree add --force'."
        )
        assert error is None, f"Expected no error, got: {error!r}"
        assert worktree_path.exists(), "Worktree path should exist after successful creation"

        # Verify the worktree is on the correct branch
        branch_result = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=worktree_path, capture_output=True, text=True, check=True,
        )
        assert branch_result.stdout.strip() == "fix/issue-579", (
            f"Worktree should be on 'fix/issue-579', got: {branch_result.stdout.strip()!r}"
        )

        # Clean up
        subprocess.run(["git", "worktree", "remove", str(worktree_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)

    def test_path2_resume_without_force_flag(self, mock_git_repo_with_stale_worktree):
        """
        Bug test for Path 2: _setup_worktree() with resume_existing=True uses
        `git worktree add` without `--force`, failing when the branch is still
        associated with a stale worktree entry.

        Current (buggy) behavior: uses `git worktree add <path> <branch>` (no --force),
        which fails if the branch was previously associated with a worktree.
        Expected (fixed) behavior: uses `git worktree add --force <path> <branch>`.

        NOTE: This path only triggers when resume_existing=True AND the branch
        still exists. In the current buggy code, the worktree add command at line 177-178
        doesn't use --force. The change orchestrator always uses --force in this path.

        This test FAILS on the current buggy code because the non-force worktree add
        may fail when the branch has stale worktree associations.
        """
        from pdd.agentic_bug_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_stale_worktree["main_repo"]

        # Create a new worktree that registers the branch, then remove directory but
        # leave the git worktree metadata stale (simulating a crash/incomplete cleanup)
        stale_wt_path = main_repo / ".pdd" / "worktrees" / "fix-issue-579-stale"
        stale_wt_path.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "worktree", "add", "--force", str(stale_wt_path), "fix/issue-579"],
            cwd=main_repo, check=True, capture_output=True
        )
        # Delete the directory but don't prune — git still thinks the branch is in use
        import shutil
        shutil.rmtree(stale_wt_path)

        # Now call _setup_worktree with resume_existing=True
        # Buggy code: `git worktree add <path> <branch>` at line 177-178 without --force
        # This should fail because git thinks fix/issue-579 is already checked out in stale_wt_path
        worktree_path, error = _setup_worktree(main_repo, 579, quiet=True, resume_existing=True)

        # After fix, should succeed with --force
        assert worktree_path is not None, (
            f"_setup_worktree() with resume_existing=True should succeed even when branch "
            f"has stale worktree associations. Got error: {error!r}. "
            f"Bug: uses 'git worktree add' without '--force' flag."
        )
        assert error is None, f"Expected no error, got: {error!r}"
        assert worktree_path.exists(), "Worktree path should exist after successful creation"

        # Clean up
        subprocess.run(["git", "worktree", "remove", str(worktree_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)
        # Also prune stale worktree entries
        subprocess.run(["git", "worktree", "prune"], cwd=main_repo, check=False, capture_output=True)

    def test_regression_no_branch_creates_fresh(self, mock_git_repo_clean):
        """
        Regression test: first-ever run with no existing branch should work normally.

        This ensures the fix doesn't break the happy path where no branch exists yet.
        """
        from pdd.agentic_bug_orchestrator import _setup_worktree

        main_repo = mock_git_repo_clean["main_repo"]

        worktree_path, error = _setup_worktree(main_repo, 579, quiet=True)

        assert worktree_path is not None, f"Expected worktree creation to succeed, got error: {error!r}"
        assert error is None
        assert worktree_path.exists()

        # Verify new branch was created
        branch_result = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=worktree_path, capture_output=True, text=True, check=True,
        )
        assert branch_result.stdout.strip() == "fix/issue-579"

        # Clean up
        subprocess.run(["git", "worktree", "remove", str(worktree_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)

    def test_regression_deletable_branch_creates_fresh(self, mock_git_repo_clean):
        """
        Regression test: when branch exists but CAN be deleted (not checked out),
        should delete and recreate fresh.

        This ensures the fix doesn't break the case where branch deletion succeeds.
        """
        from pdd.agentic_bug_orchestrator import _setup_worktree

        main_repo = mock_git_repo_clean["main_repo"]

        # Create the branch (but don't check it out — stay on main)
        subprocess.run(
            ["git", "branch", "fix/issue-579"],
            cwd=main_repo, check=True, capture_output=True
        )

        # Verify we're on main, not the fix branch
        result = subprocess.run(
            ["git", "branch", "--show-current"],
            cwd=main_repo, capture_output=True, text=True, check=True
        )
        assert result.stdout.strip() == "main", "Should be on main branch"

        worktree_path, error = _setup_worktree(main_repo, 579, quiet=True)

        assert worktree_path is not None, f"Expected worktree creation to succeed, got error: {error!r}"
        assert error is None
        assert worktree_path.exists()

        # Clean up
        subprocess.run(["git", "worktree", "remove", str(worktree_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)

    def test_fresh_rerun_resets_branch_to_main_head(self, tmp_path):
        """
        When resume_existing=False and the branch can't be deleted, the worktree
        should be reset to the main repo's current HEAD so old commits from the
        prior run don't leak into the new PR.

        Without the reset, the worktree would start at the old branch tip (with
        stale test files and commits from the first run).
        """
        from pdd.agentic_bug_orchestrator import _setup_worktree

        # Set up a repo on main, with fix/issue-579 checked out in a worktree
        # (simulating: user is on main, prior pdd bug created fix branch in a worktree)
        main_repo = tmp_path / "main_repo"
        main_repo.mkdir()
        subprocess.run(["git", "init", "-b", "main"], cwd=main_repo, check=True, capture_output=True)
        subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=main_repo, check=True)
        subprocess.run(["git", "config", "user.name", "Test User"], cwd=main_repo, check=True)

        # Initial commit on main
        (main_repo / "README.md").write_text("# Test\n")
        subprocess.run(["git", "add", "."], cwd=main_repo, check=True)
        subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=main_repo, check=True, capture_output=True)

        main_head = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=main_repo, capture_output=True, text=True, check=True,
        ).stdout.strip()

        # Create fix/issue-579 in a separate worktree (simulating first pdd bug run)
        old_worktree = tmp_path / "old_worktree"
        subprocess.run(
            ["git", "worktree", "add", "-b", "fix/issue-579", str(old_worktree), "HEAD"],
            cwd=main_repo, check=True, capture_output=True,
        )

        # Add a commit on fix branch (stale work from prior run)
        (old_worktree / "fix.py").write_text("# Old fix\n")
        subprocess.run(["git", "add", "fix.py"], cwd=old_worktree, check=True)
        subprocess.run(["git", "commit", "-m", "Old work from prior run"], cwd=old_worktree, check=True, capture_output=True)

        old_branch_head = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=old_worktree, capture_output=True, text=True, check=True,
        ).stdout.strip()

        # Confirm the branch has diverged from main
        assert old_branch_head != main_head, "Precondition: branch should have extra commits"

        # Remove the old worktree directory but DON'T prune — branch is still
        # registered to old worktree, so _delete_branch will fail
        import shutil
        shutil.rmtree(old_worktree)

        # Verify main repo is on main (user's normal state)
        current = subprocess.run(
            ["git", "branch", "--show-current"],
            cwd=main_repo, capture_output=True, text=True, check=True,
        ).stdout.strip()
        assert current == "main", "Precondition: repo should be on main"

        # Fresh re-run: resume_existing=False
        worktree_path, error = _setup_worktree(main_repo, 579, quiet=True, resume_existing=False)

        assert worktree_path is not None, f"Should succeed, got: {error!r}"
        assert error is None

        # The worktree's HEAD should match main's HEAD, NOT the old branch tip
        worktree_head = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=worktree_path, capture_output=True, text=True, check=True,
        ).stdout.strip()

        assert worktree_head == main_head, (
            f"Fresh re-run should reset branch to main HEAD.\n"
            f"  Main HEAD:     {main_head}\n"
            f"  Worktree HEAD: {worktree_head}\n"
            f"  Old branch:    {old_branch_head}\n"
            f"Old commits from prior run are leaking into the worktree."
        )

        # The old file from the first run should not be present
        assert not (worktree_path / "fix.py").exists(), (
            "Old file 'fix.py' from prior run should be gone after reset"
        )

        # Clean up
        subprocess.run(["git", "worktree", "remove", str(worktree_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)

    def test_resume_rerun_keeps_old_commits(self, mock_git_repo_with_checked_out_branch):
        """
        When resume_existing=True, the branch should NOT be reset — old commits
        and files from the prior run should be preserved (that's the point of resuming).
        """
        from pdd.agentic_bug_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_checked_out_branch["main_repo"]

        # Get the branch's current tip (includes "Work from prior pdd bug run" commit)
        branch_head_before = subprocess.run(
            ["git", "rev-parse", "fix/issue-579"],
            cwd=main_repo, capture_output=True, text=True, check=True,
        ).stdout.strip()

        # Call with resume_existing=True
        worktree_path, error = _setup_worktree(main_repo, 579, quiet=True, resume_existing=True)

        assert worktree_path is not None, f"Should succeed, got: {error!r}"
        assert error is None

        # The worktree's HEAD should match the OLD branch tip (not reset)
        worktree_head = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=worktree_path, capture_output=True, text=True, check=True,
        ).stdout.strip()

        assert worktree_head == branch_head_before, (
            f"Resume should keep old branch commits.\n"
            f"  Expected (old branch): {branch_head_before}\n"
            f"  Got (worktree HEAD):   {worktree_head}\n"
            f"Branch was unexpectedly reset during resume."
        )

        # The old file from the first run should still be present
        assert (worktree_path / "fix.py").exists(), (
            "Old file 'fix.py' should be preserved when resuming"
        )

        # Clean up
        subprocess.run(["git", "worktree", "remove", str(worktree_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)

    def test_change_orchestrator_handles_checked_out_branch(self, mock_git_repo_with_checked_out_branch):
        """
        Control test: verify the change orchestrator's _setup_worktree succeeds
        under the same conditions where the bug orchestrator fails.

        This confirms the bug is specific to the bug orchestrator and that the
        change orchestrator's --force pattern works correctly.
        """
        from pdd.agentic_change_orchestrator import _setup_worktree as change_setup_worktree

        main_repo = mock_git_repo_with_checked_out_branch["main_repo"]

        # First, create the change branch (rename fix/ to change/ for the change orchestrator)
        subprocess.run(
            ["git", "branch", "change/issue-579"],
            cwd=main_repo, check=True, capture_output=True
        )

        # Call the change orchestrator's _setup_worktree — should succeed
        worktree_path, error = change_setup_worktree(main_repo, 579, quiet=True)

        assert worktree_path is not None, (
            f"Change orchestrator should handle checked-out branch gracefully. Got: {error!r}"
        )
        assert error is None

        # Clean up
        subprocess.run(["git", "worktree", "remove", str(worktree_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)
