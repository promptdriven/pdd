"""
E2E Test for Issue #659: Full orchestrator failure with stale worktree references.

Unlike the unit-level tests in test_e2e_issue_659_worktree_stale_ref.py which call
_setup_worktree() directly, these tests exercise the full orchestrator entry points
(run_agentic_test_orchestrator / run_agentic_checkup_orchestrator) — the code path
triggered when a user runs `pdd test <url>` or `pdd checkup <url>`.

Bug Context:
-----------
When a Cloud Run container crashes or restarts, the worktree directory is removed
but `git worktree prune` is never called. On the next job:

1. The orchestrator reaches the step that requires a worktree
2. _setup_worktree() tries to delete the stale branch, fails
3. Test orchestrator: returns hard error (no --force fallback)
4. Checkup orchestrator: silently ignores failure, then crashes on `git worktree add -b`

The bug and change orchestrators already handle this via --force fallback.

Test Strategy:
-------------
- Mock LLM calls (run_agentic_task) and workflow state persistence
- Use real git operations — no mocking of the buggy component
- Simulate cached state so orchestrators jump to worktree-dependent steps
- Assert orchestrator succeeds (it currently fails due to the bug)
"""

import pytest
import shutil
import subprocess
from pathlib import Path
from unittest.mock import patch


@pytest.fixture
def git_repo_with_stale_worktree(tmp_path):
    """Create a git repo that simulates a Cloud Run crash leaving stale worktree refs.

    Steps:
    1. Initialize a repo with an initial commit
    2. Create a worktree + branch (simulating a prior job)
    3. Delete the worktree directory WITHOUT pruning (simulating container crash)
    4. Git still thinks the branch is in use by the (now-missing) worktree
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


def _create_stale_worktree(main_repo: Path, branch_name: str, worktree_subpath: str):
    """Create a worktree then delete its directory without pruning.

    This leaves git's internal worktree metadata pointing at a missing directory,
    which blocks `git branch -D` and `git worktree add` without --force.
    """
    stale_wt = main_repo / ".pdd" / "worktrees" / worktree_subpath
    stale_wt.parent.mkdir(parents=True, exist_ok=True)

    subprocess.run(
        ["git", "worktree", "add", "-b", branch_name, str(stale_wt), "HEAD"],
        cwd=main_repo, check=True, capture_output=True,
    )
    assert stale_wt.exists()

    # Simulate Cloud Run crash: directory gone, git metadata remains
    shutil.rmtree(stale_wt)
    assert not stale_wt.exists()

    # Verify the branch is now undeletable (stale ref blocks it)
    del_result = subprocess.run(
        ["git", "branch", "-D", branch_name],
        cwd=main_repo, capture_output=True, text=True,
    )
    assert del_result.returncode != 0, (
        f"Precondition: git branch -D should fail due to stale worktree ref. "
        f"stderr={del_result.stderr!r}"
    )


@pytest.mark.e2e
class TestIssue659OrchestratorStaleWorktreeE2E:
    """
    E2E tests exercising full orchestrator flows with stale worktree references.

    These tests call the top-level run_agentic_*_orchestrator() functions with
    mocked LLM calls but real git operations, matching the pattern from
    test_e2e_issue_579_orchestrator_rerun.py.
    """

    # ── Test 1: test orchestrator full flow fails ──────────────────

    def test_test_orchestrator_fails_on_stale_worktree(
        self, git_repo_with_stale_worktree, monkeypatch
    ):
        """
        BUG REPRODUCTION (E2E): Full test orchestrator fails when a stale worktree
        ref exists for the test/issue-659 branch.

        User scenario: `pdd test <issue-url>` on Cloud Run after a prior container
        crashed, leaving a stale worktree ref for the same issue branch.

        The orchestrator reaches Step 12 (worktree creation point), calls
        _setup_worktree(), which fails because:
          _branch_exists() → True
          _delete_branch() → fails (stale ref, no --force fallback)
          → returns (None, "Failed to delete existing branch...")
          → orchestrator returns (False, "Failed to create worktree: ...")

        This test FAILS on buggy code (asserts success but gets failure).
        """
        from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator

        main_repo = git_repo_with_stale_worktree["main_repo"]
        monkeypatch.chdir(main_repo)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Create stale worktree for the test/issue-659 branch
        _create_stale_worktree(main_repo, "test/issue-659", "test-issue-659-stale")

        # Simulate cached state: steps 1-11 complete.
        # The orchestrator will try to create a worktree before Step 12.
        cached_state = {
            "last_completed_step": 11,
            "step_outputs": {
                "1": "No duplicates found",
                "2": "Documentation reviewed",
                "3": "Research complete",
                "4": "Test scope identified",
                "5": "Test plan designed",
                "5.5": "Enhanced test plan",
                "6": "Test dependencies identified",
                "7": "Mock strategy defined",
                "8": "Test design finalized",
                "9": "FILES_CREATED: tests/test_something.py",
                "10": "Tests verified",
                "11": "CHECKLIST_STATUS: COMPLETE",
            },
            "total_cost": 0.50,
            "model_used": "mock-model",
            "worktree_path": None,
        }

        def mock_load_state(*args, **kwargs):
            return cached_state, "mock-comment-id"

        def mock_save_state(*args, **kwargs):
            return None

        def mock_clear_state(*args, **kwargs):
            pass

        step_calls = []

        def mock_run_agentic_task(*args, **kwargs):
            label = kwargs.get("label", args[5] if len(args) > 5 else "unknown")
            step_calls.append(label)
            if label == "step12":
                return (True, "FILES_CREATED: tests/test_something.py\nFILES_MODIFIED: none", 0.001, "mock-model")
            return (True, f"Mock success for {label}", 0.001, "mock-model")

        with patch('pdd.agentic_test_orchestrator.load_workflow_state', side_effect=mock_load_state):
            with patch('pdd.agentic_test_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_test_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                    with patch('pdd.agentic_test_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
                        success, message, cost, model, files = run_agentic_test_orchestrator(
                            issue_url="https://github.com/test/repo/issues/659",
                            issue_content="Stale worktree ref bug",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=659,
                            issue_author="testuser",
                            issue_title="Stale worktree blocks test orchestrator",
                            cwd=main_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                        )

        # After fix: orchestrator should succeed past worktree creation
        assert success, (
            f"Test orchestrator should handle stale worktree refs gracefully. "
            f"Got failure: {message!r}. "
            f"Bug: _setup_worktree() returns hard error when _delete_branch() fails "
            f"on stale ref — no --force fallback or git worktree prune. "
            f"Steps executed: {step_calls}"
        )

        # Clean up
        wt_path = main_repo / ".pdd" / "worktrees" / "test-issue-659"
        subprocess.run(["git", "worktree", "remove", str(wt_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)

    # ── Test 2: checkup orchestrator full flow fails (fresh run) ───

    def test_checkup_orchestrator_fails_on_stale_worktree_fresh(
        self, git_repo_with_stale_worktree, monkeypatch
    ):
        """
        BUG REPRODUCTION (E2E): Full checkup orchestrator fails on fresh run when
        a stale worktree ref exists for the checkup/issue-659 branch.

        User scenario: `pdd checkup <issue-url>` on Cloud Run after a prior container
        crashed. The orchestrator creates a worktree before Step 3 (fix-verify loop).

        The failure chain:
          _delete_branch() → fails silently (return value ignored)
          has_branch = False ← WRONG, branch still exists
          git worktree add -b <branch> → fails: "branch already exists"
          → orchestrator returns (False, "Failed to create worktree: ...")

        This test FAILS on buggy code.
        """
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        main_repo = git_repo_with_stale_worktree["main_repo"]
        monkeypatch.chdir(main_repo)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Create stale worktree for checkup/issue-659
        _create_stale_worktree(main_repo, "checkup/issue-659", "checkup-issue-659-stale")

        # Simulate cached state: steps 1-2 complete.
        # The orchestrator will create a worktree before Step 3 (fix loop).
        cached_state = {
            "workflow": "checkup",
            "issue_number": 659,
            "last_completed_step": 2,
            "step_outputs": {
                "1": "Issue analyzed: stale worktree bug",
                "2": "Checkup plan created",
            },
            "total_cost": 0.10,
            "model_used": "mock-model",
            "worktree_path": None,
            "fix_verify_iteration": 0,
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
            # Step 7: must return "All Issues Fixed" to exit the loop
            if "step7" in label:
                return (True, "All Issues Fixed", 0.001, "mock-model")
            return (True, f"Mock success for {label}", 0.001, "mock-model")

        with patch('pdd.agentic_checkup_orchestrator.load_workflow_state', side_effect=mock_load_state):
            with patch('pdd.agentic_checkup_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_checkup_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                    with patch('pdd.agentic_checkup_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
                        success, message, cost, model = run_agentic_checkup_orchestrator(
                            issue_url="https://github.com/test/repo/issues/659",
                            issue_content="Stale worktree ref bug in checkup",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=659,
                            issue_title="Stale worktree blocks checkup orchestrator",
                            architecture_json="{}",
                            pddrc_content="",
                            cwd=main_repo,
                            verbose=False,
                            quiet=True,
                            no_fix=False,
                            use_github_state=False,
                        )

        # After fix: orchestrator should succeed
        assert success, (
            f"Checkup orchestrator should handle stale worktree refs on fresh run. "
            f"Got failure: {message!r}. "
            f"Bug: _delete_branch() failure is silently ignored, then "
            f"'git worktree add -b' fails because branch still exists. "
            f"Steps executed: {step_calls}"
        )

        # Clean up
        wt_path = main_repo / ".pdd" / "worktrees" / "checkup-issue-659"
        subprocess.run(["git", "worktree", "remove", str(wt_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)

    # ── Test 3: bug orchestrator handles stale ref (control) ───────

    def test_bug_orchestrator_succeeds_with_stale_worktree_control(
        self, git_repo_with_stale_worktree, monkeypatch
    ):
        """
        CONTROL TEST (E2E): The bug orchestrator handles stale worktree refs
        correctly at the full orchestrator level via its --force fallback.

        This proves the fix pattern works end-to-end and that the bug is specific
        to test/checkup orchestrators. Matches the control pattern from
        test_e2e_issue_579_orchestrator_rerun.py.
        """
        from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

        main_repo = git_repo_with_stale_worktree["main_repo"]
        monkeypatch.chdir(main_repo)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Create stale worktree for fix/issue-659
        _create_stale_worktree(main_repo, "fix/issue-659", "fix-issue-659-stale")

        # No cached state — fresh run from step 1
        def mock_load_state(*args, **kwargs):
            return None, None

        def mock_save_state(*args, **kwargs):
            return None

        def mock_clear_state(*args, **kwargs):
            pass

        step_calls = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            step_calls.append(label)

            if label == "step1":
                return (True, "No duplicates found. This is a new issue.", 0.001, "mock-model")
            if label == "step2":
                return (True, "This is a confirmed bug, not user error.", 0.001, "mock-model")
            if label == "step3":
                return (True, "Sufficient information. Proceeding.", 0.001, "mock-model")
            if label == "step7":
                return (True, "DEFECT_TYPE: code\nThe bug is in the code.", 0.001, "mock-model")
            if label == "step9":
                return (True, "FILES_CREATED: tests/test_fix.py\nTest generated.", 0.001, "mock-model")
            if label == "step10":
                return (True, "Test correctly catches the bug.", 0.001, "mock-model")
            if label == "step11":
                return (True, "E2E_SKIP: Simple bug.", 0.001, "mock-model")
            return (True, f"Mock success for {label}", 0.001, "mock-model")

        with patch('pdd.agentic_bug_orchestrator.load_workflow_state', side_effect=mock_load_state):
            with patch('pdd.agentic_bug_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_bug_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                    with patch('pdd.agentic_bug_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
                        success, message, cost, model, files = run_agentic_bug_orchestrator(
                            issue_url="https://github.com/test/repo/issues/659",
                            issue_content="Stale worktree ref bug — control test",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=659,
                            issue_author="testuser",
                            issue_title="Control: bug orchestrator handles stale refs",
                            cwd=main_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                        )

        # Bug orchestrator should succeed — it has --force fallback
        assert success, (
            f"Bug orchestrator should handle stale worktree refs via --force fallback. "
            f"Got failure: {message!r}. Steps executed: {step_calls}"
        )

        # Clean up
        wt_path = main_repo / ".pdd" / "worktrees" / "fix-issue-659"
        subprocess.run(["git", "worktree", "remove", str(wt_path), "--force"],
                       cwd=main_repo, check=False, capture_output=True)
