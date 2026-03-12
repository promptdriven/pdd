"""Unit tests for Issue #794: Anti-TDD test generation and test file discovery bugs.

Bug 1 (agentic_bug_orchestrator): Step 10 verification relies solely on string
matching ("FAIL: Test does not work as expected" in output) with no independent
subprocess-based pytest execution. Anti-TDD tests that pass on buggy code slip
through because the orchestrator trusts LLM self-reporting.

Bug 2 (agentic_e2e_fix_orchestrator): _get_modified_and_untracked() uses
`git diff --name-only HEAD` which only finds uncommitted changes. Test files
committed during pdd bug are invisible to all 4 discovery paths in
_extract_test_files(), causing _verify_tests_independently() to miss them.
"""

import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Set

import pytest
from unittest.mock import MagicMock, patch, call

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator
from pdd.agentic_e2e_fix_orchestrator import (
    _extract_test_files,
    _get_modified_and_untracked,
    _verify_tests_independently,
)


# ---------------------------------------------------------------------------
# Bug 1: Anti-TDD tests slip through Step 10 (agentic_bug_orchestrator)
# ---------------------------------------------------------------------------


class TestBug1AntiTddVerification:
    """Bug orchestrator Step 10 should independently verify tests fail on buggy code."""

    @pytest.fixture
    def mock_deps(self, tmp_path):
        """Mock external dependencies for the bug orchestrator."""
        mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
        mock_worktree_path.mkdir(parents=True, exist_ok=True)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
             patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
             patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree:

            mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
            mock_load.return_value = "Prompt for {issue_number}"
            mock_worktree.return_value = (mock_worktree_path, None)

            yield mock_run, mock_load, mock_console

    @pytest.fixture
    def default_args(self, tmp_path):
        """Default arguments for run_agentic_bug_orchestrator."""
        return {
            "issue_url": "http://github.com/owner/repo/issues/1",
            "issue_content": "Bug description",
            "repo_owner": "owner",
            "repo_name": "repo",
            "issue_number": 1,
            "issue_author": "user",
            "issue_title": "Bug Title",
            "cwd": tmp_path,
            "verbose": False,
            "quiet": True,
        }

    def test_step10_does_not_catch_anti_tdd_tests_that_pass_on_buggy_code(
        self, mock_deps, default_args
    ):
        """Step 10 should reject tests that PASS on buggy code.

        TDD requires tests to fail before fix. If Step 10's LLM output says
        "PASS: Test correctly detects the bug" but the test actually passes on
        buggy code (anti-TDD), the orchestrator should catch this via
        independent pytest execution and return failure.

        Currently: orchestrator trusts LLM's "PASS" claim (no "FAIL:" string
        in output), so anti-TDD tests slip through.
        """
        mock_run, mock_load, _ = mock_deps

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
                # Step 9 generates a test file (anti-TDD: asserts buggy behavior)
                return (
                    True,
                    "Generated test\nFILES_CREATED: test_anti_tdd.py",
                    0.1,
                    "model",
                )
            if label == "step10":
                # LLM claims PASS — but the test actually passes on buggy code
                # (anti-TDD: asserts buggy behavior as correct)
                return (
                    True,
                    "PASS: Test correctly detects the bug. The test failed as expected.",
                    0.1,
                    "model",
                )
            return (True, f"Output for {label}", 0.1, "model")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_bug_orchestrator(
            **default_args
        )

        # After fix: orchestrator should independently run pytest and detect
        # that the test PASSES on buggy code (anti-TDD), returning failure.
        # Currently: orchestrator sees no "FAIL:" string, treats it as success.
        assert success is False, (
            "Orchestrator should reject anti-TDD tests that pass on buggy code. "
            "Step 10 should independently verify the test fails via pytest subprocess, "
            "not just trust the LLM's 'PASS' claim."
        )

    def test_step10_string_match_is_only_verification(self, mock_deps, default_args):
        """Demonstrates the root cause: Step 10 only checks for 'FAIL:' string.

        When the LLM self-reports failure with the exact string
        "FAIL: Test does not work as expected", the orchestrator correctly
        stops. But there's no independent pytest verification — the
        string match IS the only check.
        """
        mock_run, mock_load, _ = mock_deps

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
                return (
                    True,
                    "Generated test\nFILES_CREATED: test_file.py",
                    0.1,
                    "model",
                )
            if label == "step10":
                # LLM self-reports failure
                return (
                    True,
                    "FAIL: Test does not work as expected",
                    0.1,
                    "model",
                )
            return (True, f"Output for {label}", 0.1, "model")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_bug_orchestrator(
            **default_args
        )

        # This correctly triggers the hard stop (string match works)
        assert success is False
        assert "Stopped at Step 10" in msg

    def test_orchestrator_should_run_pytest_independently_at_step10(
        self, mock_deps, default_args
    ):
        """The bug orchestrator should have independent pytest verification at Step 10.

        The fix orchestrator already has _verify_tests_independently() for
        Steps 2 and 9. The bug orchestrator should adopt the same pattern
        for Step 10 to catch anti-TDD tests.

        Currently: the bug orchestrator has no such verification.
        """
        mock_run, mock_load, _ = mock_deps

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
                return (
                    True,
                    "Generated test\nFILES_CREATED: test_file.py",
                    0.1,
                    "model",
                )
            if label == "step10":
                return (True, "Test verification output", 0.1, "model")
            return (True, f"Output for {label}", 0.1, "model")

        mock_run.side_effect = side_effect

        # After fix: the orchestrator should call an independent verification
        # function (like _verify_tests_independently or run_pytest_and_capture_output)
        # to confirm the generated test actually FAILS on the current code.
        with patch(
            "pdd.agentic_bug_orchestrator.run_pytest_and_capture_output",
            return_value={
                "test_results": [
                    {"passed": 1, "failures": 0, "errors": 0, "standard_output": "1 passed"}
                ]
            },
        ) as mock_pytest:
            success, msg, cost, model, files = run_agentic_bug_orchestrator(
                **default_args
            )

            # After fix: run_pytest_and_capture_output should be called at Step 10
            # to independently verify the test fails
            assert mock_pytest.called, (
                "Bug orchestrator should independently run pytest at Step 10 to verify "
                "the generated test fails on buggy code. Currently it only does string "
                "matching on LLM output."
            )


# ---------------------------------------------------------------------------
# Bug 2: Fix orchestrator misses committed test files
# (agentic_e2e_fix_orchestrator)
# ---------------------------------------------------------------------------


class TestBug2GetModifiedAndUntracked:
    """_get_modified_and_untracked() misses files committed on the feature branch."""

    def _init_git_repo_with_committed_test(self, tmp_path: Path) -> Path:
        """Create a git repo with a committed test file on a feature branch.

        Simulates the real workflow: main branch exists, feature branch diverges,
        and pdd bug commits a test file on the feature branch.
        """
        subprocess.run(["git", "init", "-b", "main"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(
            ["git", "config", "user.email", "test@test.com"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "commit", "--allow-empty", "-m", "init"],
            cwd=tmp_path, capture_output=True, check=True,
        )

        # Create a feature branch (like pdd bug workflow does)
        subprocess.run(
            ["git", "checkout", "-b", "bug/issue-123"],
            cwd=tmp_path, capture_output=True, check=True,
        )

        # Create and commit a test file (like pdd bug would)
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        test_file = tests_dir / "test_committed.py"
        test_file.write_text("def test_something(): assert True\n")
        subprocess.run(["git", "add", "tests/test_committed.py"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(
            ["git", "commit", "-m", "pdd bug: add test"],
            cwd=tmp_path, capture_output=True, check=True,
        )

        return test_file

    def test_committed_files_not_discovered(self, tmp_path):
        """_get_modified_and_untracked() uses `git diff --name-only HEAD` which
        only shows uncommitted changes. Files committed on the feature branch
        are invisible.

        After fix: should use `git diff --name-only <base>...HEAD` or similar
        to also find files added in commits since the branch diverged.
        """
        self._init_git_repo_with_committed_test(tmp_path)

        result = _get_modified_and_untracked(tmp_path)

        # After fix: committed test file should be found
        assert "tests/test_committed.py" in result, (
            "_get_modified_and_untracked() should discover files committed on "
            "the feature branch, not just uncommitted changes. Currently uses "
            "`git diff --name-only HEAD` which misses committed files."
        )

    def test_uncommitted_files_are_discovered(self, tmp_path):
        """Baseline: uncommitted (untracked) files ARE found by
        _get_modified_and_untracked(). This confirms the function works
        for its current scope — the bug is the missing scope for committed files.
        """
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(
            ["git", "commit", "--allow-empty", "-m", "init"],
            cwd=tmp_path, capture_output=True, check=True,
        )

        # Create untracked file (not committed)
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "test_untracked.py").write_text("def test_x(): pass\n")

        result = _get_modified_and_untracked(tmp_path)

        assert "tests/test_untracked.py" in result


class TestBug2ExtractTestFiles:
    """_extract_test_files() misses committed test files when hash detection disabled."""

    def test_committed_test_file_not_extracted(self, tmp_path):
        """When hash detection is disabled (initial_file_hashes=None) and no
        markers or changed_files reference a committed test file,
        _extract_test_files() should still find it via a fallback path.

        Simulates the PR #619 scenario: pdd bug committed
        test_concurrent_label_race_issue_613.py in a second commit, but it's
        not in issue_content markers or changed_files. With hash detection
        disabled, all 4 discovery paths fail.

        After fix: a fallback directory scan or branch diff should discover it.
        """
        # Initialize git repo with committed test file
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(
            ["git", "config", "user.email", "test@test.com"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "commit", "--allow-empty", "-m", "init"],
            cwd=tmp_path, capture_output=True, check=True,
        )

        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        test_file = tests_dir / "test_race_issue_613.py"
        test_file.write_text("def test_race(): assert False, 'bug'\n")
        subprocess.run(["git", "add", "."], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(
            ["git", "commit", "-m", "pdd bug commit 2"],
            cwd=tmp_path, capture_output=True, check=True,
        )

        # No markers, no changed_files, no hash detection
        result = _extract_test_files(
            issue_content="",
            changed_files=[],
            cwd=tmp_path,
            initial_file_hashes=None,
        )

        # After fix: committed test file should be discovered via fallback
        assert "tests/test_race_issue_613.py" in result, (
            "_extract_test_files() should discover committed test files even when "
            "hash detection is disabled. A fallback path (directory scan or "
            f"branch diff) is needed. Got: {result}"
        )

    def test_uncommitted_test_file_is_extracted(self, tmp_path):
        """Baseline: untracked test files ARE found via hash detection.

        This confirms _extract_test_files works when the file is untracked
        and hash detection is enabled.
        """
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(
            ["git", "commit", "--allow-empty", "-m", "init"],
            cwd=tmp_path, capture_output=True, check=True,
        )

        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "test_untracked_issue.py").write_text("def test_x(): pass\n")

        # Empty initial hashes = snapshot before workflow
        result = _extract_test_files(
            issue_content="",
            changed_files=[],
            cwd=tmp_path,
            initial_file_hashes={},
        )

        assert "tests/test_untracked_issue.py" in result


class TestBug2VerifyTestsIndependently:
    """Missed test files are never verified, allowing false ALL_TESTS_PASS."""

    def test_missed_test_files_never_verified(self, tmp_path):
        """End-to-end impact: when _extract_test_files() misses a committed
        test file, _verify_tests_independently() never checks it.

        This allows the orchestrator to report ALL_TESTS_PASS while the
        missed test file still has failing assertions from anti-TDD generation.
        """
        # Setup: two test files on disk, one failing
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "test_discovered.py").write_text("def test_ok(): pass\n")
        (tests_dir / "test_missed_committed.py").write_text(
            "def test_anti_tdd(): assert False, 'anti-TDD assertion'\n"
        )

        # Initialize git so _get_modified_and_untracked works
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(
            ["git", "config", "user.email", "test@test.com"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "commit", "--allow-empty", "-m", "init"],
            cwd=tmp_path, capture_output=True, check=True,
        )

        # Commit the missed file (simulating pdd bug commit 2)
        subprocess.run(
            ["git", "add", "tests/test_missed_committed.py"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "commit", "-m", "pdd bug: add test"],
            cwd=tmp_path, capture_output=True, check=True,
        )

        # Step 1: _extract_test_files only finds the discovered file
        # (test_missed_committed.py is committed, not in markers or changed_files)
        discovered = _extract_test_files(
            issue_content="",
            changed_files=["tests/test_discovered.py"],
            cwd=tmp_path,
            initial_file_hashes=None,
        )

        # Step 2: verify only runs on discovered files
        mock_result = {
            "test_results": [
                {"passed": 1, "failures": 0, "errors": 0, "standard_output": "1 passed"}
            ]
        }
        with patch(
            "pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output",
            return_value=mock_result,
        ):
            all_passed, output = _verify_tests_independently(discovered, tmp_path)

        # After fix: test_missed_committed.py should be in discovered files
        # and verification should catch its failure
        assert "test_missed_committed.py" in output, (
            "Verification output should include test_missed_committed.py. "
            "Currently this file is missed by _extract_test_files() because "
            "it was committed (not untracked), so _verify_tests_independently() "
            f"never checks it. Verification output: {output}"
        )
