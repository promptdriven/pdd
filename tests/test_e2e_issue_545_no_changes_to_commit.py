"""
E2E Test for Issue #545: pdd fix exits 'no changes to commit' when fix exists
as unstaged changes.

Bug: When pdd fix resumes after a prior interrupted run, the orchestrator
captures initial_file_hashes AFTER the prior run's modifications already exist
on disk. The hash delta is zero, so _commit_and_push() returns "No changes to
commit" — leaving modified files orphaned as unstaged changes in the worktree.

These tests exercise the full orchestrator code path with real git operations.
Only LLM execution (run_agentic_task) and state persistence are mocked.
_get_file_hashes and _commit_and_push run unpatched against real git repos.
"""

import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest


def _create_git_repo_with_remote(tmp_path: Path):
    """Create a git repo cloned from a bare remote, suitable for push testing."""
    bare = tmp_path / "bare.git"
    worktree = tmp_path / "worktree"

    subprocess.run(["git", "init", "--bare", str(bare)],
                   check=True, capture_output=True)
    subprocess.run(["git", "clone", str(bare), str(worktree)],
                   check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"],
                   cwd=worktree, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.name", "Test"],
                   cwd=worktree, check=True, capture_output=True)

    # Create initial committed file inside a pdd/ subdirectory
    pdd_dir = worktree / "pdd"
    pdd_dir.mkdir()
    module = pdd_dir / "module.py"
    module.write_text("x = 1\n")

    subprocess.run(["git", "add", "."],
                   cwd=worktree, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "initial commit"],
                   cwd=worktree, check=True, capture_output=True)

    branch = subprocess.run(
        ["git", "rev-parse", "--abbrev-ref", "HEAD"],
        cwd=worktree, capture_output=True, text=True, check=True
    ).stdout.strip()
    subprocess.run(["git", "push", "-u", "origin", branch],
                   cwd=worktree, check=True, capture_output=True)

    return worktree, module


def _run_orchestrator_with_all_tests_pass(worktree: Path):
    """Run the full orchestrator with Step 2 returning ALL_TESTS_PASS.

    Only mocks LLM calls and state persistence. _get_file_hashes and
    _commit_and_push run unpatched against the real git repo.
    """
    from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

    def step_side_effect(*args, **kwargs):
        """Mock LLM: Step 2 returns ALL_TESTS_PASS, everything else passes."""
        label = kwargs.get("label", "")
        if "step2" in label:
            return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_template, \
         patch("pdd.agentic_e2e_fix_orchestrator.console"):

        mock_run.side_effect = step_side_effect
        mock_load.return_value = (None, None)
        mock_save.return_value = None
        mock_template.return_value = "Prompt for {issue_number}"

        success, message, cost, model, files = run_agentic_e2e_fix_orchestrator(
            issue_url="http://github.com/owner/repo/issues/545",
            issue_content="Bug: pdd fix exits 'no changes to commit'",
            repo_owner="owner",
            repo_name="repo",
            issue_number=545,
            issue_author="user",
            issue_title="Fix unstaged changes on resume",
            cwd=worktree,
            quiet=True,
            max_cycles=1,
            resume=False,
            use_github_state=False,
        )

    return success, message, cost, model, files


class TestIssue545OrphanedChangesCommittedE2E:
    """E2E tests for Issue #545: orchestrator must commit pre-existing unstaged
    modifications when ALL_TESTS_PASS at Step 2.

    These tests simulate the resume scenario where a prior pdd fix run wrote
    code changes to disk but the commit step (Step 8) failed. On the next run,
    Step 2 detects ALL_TESTS_PASS (the code is already fixed), but the
    orchestrator must still detect and commit the orphaned unstaged changes.
    """

    def test_orchestrator_commits_orphaned_changes_on_all_tests_pass(self, tmp_path):
        """Primary E2E bug test: orchestrator must commit a pre-existing
        unstaged modification when ALL_TESTS_PASS at Step 2.

        Scenario:
        1. Git repo has 'pdd/module.py' committed as "x = 1"
        2. Prior run modified it to "x = 2" but commit failed (unstaged change)
        3. Orchestrator starts, captures tainted hash snapshot
        4. Step 2 returns ALL_TESTS_PASS -> _commit_and_push() is called
        5. Bug: hash delta is zero -> "No changes to commit" -> file orphaned
        6. Fix: fallback to _get_modified_and_untracked() detects the change
        """
        worktree, module = _create_git_repo_with_remote(tmp_path)

        # Simulate prior run's modification (exists BEFORE orchestrator starts)
        module.write_text("x = 2  # fixed by prior interrupted run\n")

        success, message, cost, model, files = _run_orchestrator_with_all_tests_pass(worktree)

        assert success is True, f"Orchestrator should succeed, got message: {message}"

        # Assert on REAL git state — the orphaned file must be committed
        diff_result = subprocess.run(
            ["git", "diff", "--name-only", "HEAD"],
            cwd=worktree, capture_output=True, text=True
        )
        assert diff_result.stdout.strip() == "", (
            f"Issue #545 BUG DETECTED: Pre-existing unstaged modification from a "
            f"prior interrupted pdd fix run was NOT committed by the orchestrator.\n\n"
            f"  Still unstaged: {diff_result.stdout.strip()!r}\n\n"
            f"  The orchestrator called _commit_and_push() with a tainted hash "
            f"snapshot (captured AFTER the modification), so hash delta was zero "
            f"and it returned 'No changes to commit' without checking "
            f"git diff --name-only HEAD.\n\n"
            f"  Fix: add a fallback to _get_modified_and_untracked(cwd) in "
            f"_commit_and_push() when hash comparison yields empty files_to_commit."
        )

        # Verify the commit was pushed to the remote (use @{upstream} instead
        # of origin/HEAD — bare repos don't set a symbolic HEAD ref).
        unpushed = subprocess.run(
            ["git", "rev-list", "@{upstream}..HEAD"],
            cwd=worktree, capture_output=True, text=True
        )
        assert unpushed.stdout.strip() == "", (
            f"Issue #545: The fix commit should have been pushed to remote, "
            f"but unpushed commits exist: {unpushed.stdout.strip()!r}"
        )

    def test_orchestrator_commits_multiple_orphaned_files(self, tmp_path):
        """E2E test: orchestrator commits ALL orphaned files, not just one.

        Simulates the real-world scenario from the issue where 9+ files were
        left as unstaged changes after a prior interrupted run.
        """
        worktree, module = _create_git_repo_with_remote(tmp_path)

        # Create additional committed files
        pdd_dir = worktree / "pdd"
        for name in ["code_generator.py", "llm_invoke.py", "preprocess.py"]:
            f = pdd_dir / name
            f.write_text(f"# original {name}\n")
        subprocess.run(["git", "add", "."],
                       cwd=worktree, check=True, capture_output=True)
        subprocess.run(["git", "commit", "-m", "add more files"],
                       cwd=worktree, check=True, capture_output=True)
        subprocess.run(["git", "push"],
                       cwd=worktree, check=True, capture_output=True)

        # Simulate prior run modifying ALL files (orphaned unstaged changes)
        module.write_text("x = 2  # fixed\n")
        (pdd_dir / "code_generator.py").write_text("# fixed code_generator\n")
        (pdd_dir / "llm_invoke.py").write_text("# fixed llm_invoke\n")
        (pdd_dir / "preprocess.py").write_text("# fixed preprocess\n")

        success, message, cost, model, files = _run_orchestrator_with_all_tests_pass(worktree)

        assert success is True, f"Orchestrator should succeed, got: {message}"

        # All 4 orphaned files must be committed
        diff_result = subprocess.run(
            ["git", "diff", "--name-only", "HEAD"],
            cwd=worktree, capture_output=True, text=True
        )
        remaining = diff_result.stdout.strip()
        assert remaining == "", (
            f"Issue #545: All orphaned files should have been committed but "
            f"{remaining!r} remain unstaged. _commit_and_push() returned "
            f"'No changes to commit' because the hash snapshot was tainted."
        )

    def test_orchestrator_reports_no_changes_when_worktree_is_clean(self, tmp_path):
        """Regression guard: clean worktree stays clean after orchestrator run.

        When there are no pre-existing modifications, the orchestrator should
        NOT create spurious commits. This ensures the fallback doesn't introduce
        false positives.
        """
        worktree, module = _create_git_repo_with_remote(tmp_path)

        # NO modifications — worktree is clean
        success, message, cost, model, files = _run_orchestrator_with_all_tests_pass(worktree)

        assert success is True

        # Verify no spurious commits were created
        log_result = subprocess.run(
            ["git", "log", "--oneline"],
            cwd=worktree, capture_output=True, text=True
        )
        # Should only have the initial commit, no fix commit
        assert "fix:" not in log_result.stdout.lower(), (
            f"Regression: No fix commit should be created when worktree is clean. "
            f"Git log: {log_result.stdout.strip()!r}"
        )
