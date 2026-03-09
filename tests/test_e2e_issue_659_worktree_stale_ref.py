"""
E2E Test for Issue #659: Stale worktree references block branch operations
in test and checkup orchestrators.

Bug Context:
-----------
When a Cloud Run container crashes or restarts, the worktree directory is
removed but `git worktree prune` is never called. This leaves stale worktree
references in git's internal state. On the next run:

1. `worktree_path.exists()` → False → cleanup skipped
2. `_branch_exists()` → True → tries to delete branch
3. `git branch -D` fails: "branch is used by worktree" (stale ref)
4. Orchestrators without `--force` fallback crash

The bug and change orchestrators already have the `--force` fallback (from
issues #445 and #579). The test and checkup orchestrators do NOT, causing
the failure reported in issue #659.

Root Cause:
----------
- No `git worktree prune` is called before branch operations
- test orchestrator: returns hard error when `_delete_branch()` fails (no --force fallback)
- checkup orchestrator (fresh run): ignores `_delete_branch()` failure, sets
  `has_branch = False`, then `git worktree add -b` fails because the branch
  still exists
- checkup orchestrator (resume): uses `git worktree add` without `--force`,
  fails because git thinks the branch is still in use by the stale worktree

Expected Fix:
------------
(a) Call `git worktree prune` at the start of `_setup_worktree()` in all orchestrators
(b) Add `--force` fallback to test and checkup orchestrators (matching bug/change)
"""

import pytest
import shutil
import subprocess
from pathlib import Path
from unittest.mock import MagicMock


@pytest.fixture
def mock_git_repo_with_stale_worktree_ref(tmp_path):
    """Create a git repo with a stale worktree reference.

    Simulates the Cloud Run crash scenario:
    1. A worktree was created for a branch
    2. The worktree directory was deleted (container crash/restart)
    3. `git worktree prune` was NOT called
    4. Git still thinks the branch is checked out in the (now-missing) worktree

    This means `git branch -D <branch>` fails with:
        "error: Cannot delete branch '<branch>' checked out at '<stale_path>'"
    And `git worktree add` (without --force) also fails.
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

    return {"main_repo": main_repo}


def _create_stale_worktree(main_repo: Path, branch_name: str, worktree_subpath: str):
    """Helper: create a worktree, then delete the directory without pruning.

    This leaves a stale worktree reference in git's internal state, which
    is exactly what happens when a Cloud Run container crashes.
    """
    stale_wt = main_repo / ".pdd" / "worktrees" / worktree_subpath
    stale_wt.parent.mkdir(parents=True, exist_ok=True)

    # Create worktree with the branch
    subprocess.run(
        ["git", "worktree", "add", "-b", branch_name, str(stale_wt), "HEAD"],
        cwd=main_repo, check=True, capture_output=True,
    )

    # Verify worktree and branch exist
    assert stale_wt.exists(), "Worktree should exist after creation"
    result = subprocess.run(
        ["git", "show-ref", "--verify", f"refs/heads/{branch_name}"],
        cwd=main_repo, capture_output=True,
    )
    assert result.returncode == 0, f"Branch {branch_name} should exist"

    # Delete the directory WITHOUT pruning — simulates Cloud Run crash
    shutil.rmtree(stale_wt)
    assert not stale_wt.exists(), "Worktree directory should be gone"

    # Verify the branch is now undeletable (stale ref blocks it)
    del_result = subprocess.run(
        ["git", "branch", "-D", branch_name],
        cwd=main_repo, capture_output=True, text=True,
    )
    assert del_result.returncode != 0, (
        f"Precondition failed: git branch -D should fail due to stale worktree ref. "
        f"stdout={del_result.stdout!r}, stderr={del_result.stderr!r}"
    )


@pytest.mark.e2e
class TestIssue659WorktreeStaleRefE2E:
    """
    E2E tests for Issue #659: stale worktree references block test and
    checkup orchestrators but not bug/change orchestrators.
    """

    # ── Test 1: test orchestrator fails with stale ref ──────────────

    def test_test_orchestrator_fails_with_stale_worktree_ref(
        self, mock_git_repo_with_stale_worktree_ref
    ):
        """
        BUG REPRODUCTION: The test orchestrator's _setup_worktree() returns a
        hard error when _delete_branch() fails due to a stale worktree reference.

        Current (buggy) behavior:
            _branch_exists() → True
            _delete_branch() → fails (stale ref)
            → returns (None, "Failed to delete existing branch ...")

        Expected (fixed) behavior:
            Either prune stale worktrees first, or fall back to --force.
            → returns (worktree_path, None)

        This test FAILS on buggy code (asserts success but gets error).
        """
        from pdd.agentic_test_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_stale_worktree_ref["main_repo"]

        # Create stale worktree for test/issue-659 branch
        _create_stale_worktree(main_repo, "test/issue-659", "test-issue-659-stale")

        # Call _setup_worktree — on buggy code this returns (None, error)
        mock_console = MagicMock()
        worktree_path, error = _setup_worktree(
            main_repo, 659, quiet=True, console=mock_console
        )

        # After fix, should succeed
        assert worktree_path is not None, (
            f"_setup_worktree() should handle stale worktree refs gracefully. "
            f"Got error: {error!r}. "
            f"Bug: returns hard error instead of pruning stale refs or using --force fallback."
        )
        assert error is None, f"Expected no error, got: {error!r}"
        assert worktree_path.exists(), "Worktree directory should exist after creation"

        # Verify branch is correct
        branch_result = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=worktree_path, capture_output=True, text=True, check=True,
        )
        assert branch_result.stdout.strip() == "test/issue-659"

        # Clean up
        subprocess.run(
            ["git", "worktree", "remove", str(worktree_path), "--force"],
            cwd=main_repo, check=False, capture_output=True,
        )

    # ── Test 2: checkup orchestrator fails with stale ref (fresh run) ──

    def test_checkup_orchestrator_fails_with_stale_ref_fresh_run(
        self, mock_git_repo_with_stale_worktree_ref
    ):
        """
        BUG REPRODUCTION: The checkup orchestrator's _setup_worktree() ignores
        the _delete_branch() failure, sets has_branch=False unconditionally,
        then tries `git worktree add -b` which fails because the branch still
        exists (it was never actually deleted).

        Current (buggy) behavior (lines 270-273):
            _delete_branch() → fails silently (return value ignored)
            has_branch = False  ← WRONG: branch still exists
            git worktree add -b <branch> → fails: "branch already exists"

        Expected (fixed) behavior:
            Either prune first, or check _delete_branch() return and use --force.
            → returns (worktree_path, None)

        This test FAILS on buggy code.
        """
        from pdd.agentic_checkup_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_stale_worktree_ref["main_repo"]

        # Create stale worktree for checkup/issue-659 branch
        _create_stale_worktree(main_repo, "checkup/issue-659", "checkup-issue-659-stale")

        # Call _setup_worktree with resume_existing=False (fresh run)
        worktree_path, error = _setup_worktree(
            main_repo, 659, quiet=True, resume_existing=False
        )

        # After fix, should succeed
        assert worktree_path is not None, (
            f"_setup_worktree() should handle stale worktree refs on fresh run. "
            f"Got error: {error!r}. "
            f"Bug: ignores _delete_branch() failure, then 'git worktree add -b' "
            f"fails because branch still exists."
        )
        assert error is None, f"Expected no error, got: {error!r}"
        assert worktree_path.exists(), "Worktree directory should exist after creation"

        # Clean up
        subprocess.run(
            ["git", "worktree", "remove", str(worktree_path), "--force"],
            cwd=main_repo, check=False, capture_output=True,
        )

    # ── Test 3: checkup orchestrator fails with stale ref (resume) ──

    def test_checkup_orchestrator_fails_with_stale_ref_resume(
        self, mock_git_repo_with_stale_worktree_ref
    ):
        """
        BUG REPRODUCTION: The checkup orchestrator's _setup_worktree() with
        resume_existing=True uses `git worktree add <path> <branch>` without
        --force. Git refuses because the branch is still associated with the
        stale worktree entry.

        Current (buggy) behavior (lines 280-281):
            git worktree add <path> <branch>  ← no --force
            → fails: "fatal: '<branch>' is already checked out at '<stale_path>'"

        Expected (fixed) behavior:
            Use `git worktree add --force` or prune stale refs first.
            → returns (worktree_path, None)

        This test FAILS on buggy code.
        """
        from pdd.agentic_checkup_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_stale_worktree_ref["main_repo"]

        # Create stale worktree for checkup/issue-659 branch
        _create_stale_worktree(main_repo, "checkup/issue-659", "checkup-issue-659-stale")

        # Call _setup_worktree with resume_existing=True
        worktree_path, error = _setup_worktree(
            main_repo, 659, quiet=True, resume_existing=True
        )

        # After fix, should succeed
        assert worktree_path is not None, (
            f"_setup_worktree() with resume should handle stale worktree refs. "
            f"Got error: {error!r}. "
            f"Bug: uses 'git worktree add' without '--force' flag."
        )
        assert error is None, f"Expected no error, got: {error!r}"
        assert worktree_path.exists(), "Worktree directory should exist after creation"

        # Clean up
        subprocess.run(
            ["git", "worktree", "remove", str(worktree_path), "--force"],
            cwd=main_repo, check=False, capture_output=True,
        )

    # ── Test 4: bug orchestrator handles stale ref (control) ────────

    def test_bug_orchestrator_handles_stale_ref(
        self, mock_git_repo_with_stale_worktree_ref
    ):
        """
        CONTROL TEST: The bug orchestrator already has the --force fallback
        and should handle stale worktree refs correctly.

        This test PASSES on current code — confirms the fix pattern works.
        """
        from pdd.agentic_bug_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_stale_worktree_ref["main_repo"]

        # Create stale worktree for fix/issue-659 branch
        _create_stale_worktree(main_repo, "fix/issue-659", "fix-issue-659-stale")

        worktree_path, error = _setup_worktree(main_repo, 659, quiet=True)

        assert worktree_path is not None, (
            f"Bug orchestrator should handle stale refs via --force fallback. "
            f"Got error: {error!r}"
        )
        assert error is None, f"Expected no error, got: {error!r}"
        assert worktree_path.exists()

        # Clean up
        subprocess.run(
            ["git", "worktree", "remove", str(worktree_path), "--force"],
            cwd=main_repo, check=False, capture_output=True,
        )

    # ── Test 5: change orchestrator handles stale ref (control) ─────

    def test_change_orchestrator_handles_stale_ref(
        self, mock_git_repo_with_stale_worktree_ref
    ):
        """
        CONTROL TEST: The change orchestrator already has the --force fallback
        and should handle stale worktree refs correctly.

        This test PASSES on current code — confirms the fix pattern works.
        """
        from pdd.agentic_change_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_stale_worktree_ref["main_repo"]

        # Create stale worktree for change/issue-659 branch
        _create_stale_worktree(main_repo, "change/issue-659", "change-issue-659-stale")

        worktree_path, error = _setup_worktree(main_repo, 659, quiet=True)

        assert worktree_path is not None, (
            f"Change orchestrator should handle stale refs via --force fallback. "
            f"Got error: {error!r}"
        )
        assert error is None, f"Expected no error, got: {error!r}"
        assert worktree_path.exists()

        # Clean up
        subprocess.run(
            ["git", "worktree", "remove", str(worktree_path), "--force"],
            cwd=main_repo, check=False, capture_output=True,
        )

    # ── Test 6: test orchestrator error propagation ─────────────────

    def test_test_orchestrator_error_contains_stale_ref_details(
        self, mock_git_repo_with_stale_worktree_ref
    ):
        """
        PROPAGATION TEST: When the test orchestrator fails with a stale
        worktree ref, the error message should indicate a branch deletion
        failure (not a generic/swallowed error).

        This test PASSES on buggy code — it documents the current (broken)
        error propagation behavior. After the fix, this test should be
        updated or removed (since the error path won't be taken).
        """
        from pdd.agentic_test_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_stale_worktree_ref["main_repo"]
        _create_stale_worktree(main_repo, "test/issue-659", "test-issue-659-stale2")

        mock_console = MagicMock()
        worktree_path, error = _setup_worktree(
            main_repo, 659, quiet=True, console=mock_console
        )

        # On current buggy code: returns error about branch deletion failure
        # After fix: this path won't be reached (worktree_path will be set)
        if worktree_path is None:
            # Buggy behavior — error should mention branch deletion
            assert error is not None
            assert "test/issue-659" in error or "delete" in error.lower() or "branch" in error.lower(), (
                f"Error should mention branch deletion failure, got: {error!r}"
            )
        # If worktree_path is not None, the fix is in place — that's fine too

    # ── Test 7: checkup orchestrator error propagation (fresh run) ──

    def test_checkup_orchestrator_error_propagation_fresh_run(
        self, mock_git_repo_with_stale_worktree_ref
    ):
        """
        PROPAGATION TEST: When the checkup orchestrator fails on a fresh run
        with a stale worktree ref, the error should mention "worktree" or
        "branch" (not a silent/swallowed failure).

        Current buggy behavior: _delete_branch() failure is silently ignored,
        then `git worktree add -b` fails with "branch already exists".

        This test PASSES on buggy code — documents the broken error path.
        """
        from pdd.agentic_checkup_orchestrator import _setup_worktree

        main_repo = mock_git_repo_with_stale_worktree_ref["main_repo"]
        _create_stale_worktree(main_repo, "checkup/issue-659", "checkup-issue-659-stale2")

        worktree_path, error = _setup_worktree(
            main_repo, 659, quiet=True, resume_existing=False
        )

        # On current buggy code: returns error about worktree creation failure
        # After fix: this path won't be reached
        if worktree_path is None:
            assert error is not None
            assert "worktree" in error.lower() or "branch" in error.lower(), (
                f"Error should mention worktree/branch failure, got: {error!r}"
            )
