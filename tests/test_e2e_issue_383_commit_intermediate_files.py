"""
E2E Test for Issue #383: pdd fix agentic commits debug backup files to GitHub

This E2E test verifies that the `pdd fix agentic` workflow correctly filters out
intermediate/debug files (like `*_fixed.py`) when committing changes to GitHub.

The bug: `_commit_and_push()` in `agentic_e2e_fix_orchestrator.py` commits ALL
files that changed during the workflow based solely on hash comparison, with no
filtering for intermediate/debug file patterns.

Evidence: In PR #44 of pdd_cap repository, files like `pdd/auth_test_commands_auth_fixed.py`
and `tests/test_auth_test_commands_auth_fixed.py` were incorrectly committed.

This E2E test:
1. Sets up a real git repository
2. Invokes the orchestrator with mocked LLM calls
3. Simulates the creation of intermediate `*_fixed.py` files during Step 8
4. Verifies that `_commit_and_push()` filters out intermediate files

The test should FAIL on buggy code (intermediate files are committed) and
PASS once the filtering is implemented.

Key difference from unit tests:
- Unit tests mock subprocess.run to track which files are staged
- This E2E test uses a real git repository and checks actual git state
"""

import os
import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock
import re

import pytest


@pytest.fixture
def e2e_git_repo(tmp_path):
    """Create a realistic git repository for E2E testing.

    This fixture creates a git repo structure similar to the pdd_cap repo
    where the bug was observed.
    """
    # Initialize git repo
    subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
    subprocess.run(
        ["git", "config", "user.email", "e2e-test@example.com"],
        cwd=tmp_path,
        capture_output=True,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "E2E Test User"],
        cwd=tmp_path,
        capture_output=True,
        check=True,
    )

    # Create directory structure similar to real project
    (tmp_path / "pdd").mkdir()
    (tmp_path / "tests").mkdir()
    (tmp_path / ".pdd").mkdir()

    # Create initial files and make initial commit
    (tmp_path / "pdd" / "__init__.py").write_text('"""PDD package."""\n')
    (tmp_path / "pdd" / "auth.py").write_text('"""Auth module."""\n\ndef authenticate():\n    pass\n')
    (tmp_path / "tests" / "__init__.py").write_text("")
    (tmp_path / "tests" / "test_auth.py").write_text('"""Auth tests."""\n\ndef test_auth():\n    pass\n')

    subprocess.run(["git", "add", "."], cwd=tmp_path, capture_output=True, check=True)
    subprocess.run(
        ["git", "commit", "-m", "Initial commit"],
        cwd=tmp_path,
        capture_output=True,
        check=True,
    )

    # Create a branch for the "fix" (simulating pdd bug creating a branch)
    subprocess.run(
        ["git", "checkout", "-b", "fix/issue-383"],
        cwd=tmp_path,
        capture_output=True,
        check=True,
    )

    return tmp_path


def get_last_commit_files(cwd: Path) -> list[str]:
    """Get list of files changed in the last commit."""
    result = subprocess.run(
        ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", "HEAD"],
        cwd=cwd,
        capture_output=True,
        text=True,
        check=True,
    )
    return [f for f in result.stdout.strip().split("\n") if f]


@pytest.mark.e2e
class TestIssue383CommitIntermediateFilesE2E:
    """
    E2E tests for Issue #383: Verify _commit_and_push filters intermediate files.

    These tests exercise the REAL _commit_and_push function against a REAL git
    repository, without mocking the file filtering logic.
    """

    def test_e2e_commit_and_push_with_intermediate_files(self, e2e_git_repo):
        """
        E2E Test: _commit_and_push should NOT commit intermediate *_fixed.py files.

        This test replicates the exact scenario from PR #44 where files like
        `pdd/auth_test_commands_auth_fixed.py` were incorrectly committed.
        """
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push

        cwd = e2e_git_repo

        (cwd / "pdd" / "auth.py").write_text(
            '"""Auth module - fixed."""\n\ndef authenticate():\n    return True\n'
        )
        (cwd / "tests" / "test_auth.py").write_text(
            '"""Auth tests - fixed."""\n\ndef test_auth():\n    assert True\n'
        )

        (cwd / "pdd" / "auth_fixed.py").write_text(
            '"""Intermediate output - should not be committed."""\n'
        )
        (cwd / "tests" / "test_auth_fixed.py").write_text(
            '"""Intermediate test output - should not be committed."""\n'
        )

        initial_hashes = {}

        original_run = subprocess.run

        def mock_run_for_push_only(args, **kwargs):
            if args[0:2] == ["git", "push"]:
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                return result
            return original_run(args, **kwargs)

        with patch("subprocess.run", side_effect=mock_run_for_push_only):
            success, message = _commit_and_push(
                cwd=cwd,
                issue_number=383,
                issue_title="Test intermediate file filtering",
                repo_owner="test",
                repo_name="repo",
                initial_file_hashes=initial_hashes,
                quiet=True,
            )

        committed_files = get_last_commit_files(cwd)

        assert success is True, f"_commit_and_push should succeed, got: {message}"
        assert "pdd/auth.py" in committed_files, (
            "Legitimate file pdd/auth.py should be committed"
        )
        assert "tests/test_auth.py" in committed_files, (
            "Legitimate file tests/test_auth.py should be committed"
        )

        assert "pdd/auth_fixed.py" not in committed_files, (
            f"BUG (Issue #383): pdd/auth_fixed.py was committed! Files: {committed_files}"
        )
        assert "tests/test_auth_fixed.py" not in committed_files, (
            f"BUG (Issue #383): tests/test_auth_fixed.py was committed! Files: {committed_files}"
        )

    def test_e2e_commit_filters_all_intermediate_patterns(self, e2e_git_repo):
        """E2E Test: _commit_and_push filters all known intermediate file patterns."""
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push

        cwd = e2e_git_repo

        (cwd / "pdd" / "module.py").write_text('"""Fixed module."""\n')

        intermediate_files = [
            "pdd/module_fixed.py",
            "pdd/module.fixed.py",
            "pdd/module-fixed.py",
            "pdd/module.py.bak",
            "pdd/module.py.backup",
            "pdd/module.py.orig",
            "pdd/module.py.tmp",
        ]

        for f in intermediate_files:
            (cwd / f).write_text(f'"""Intermediate: {f}"""\n')

        initial_hashes = {}

        original_run = subprocess.run
        def mock_run_for_push_only(args, **kwargs):
            if args[0:2] == ["git", "push"]:
                result = MagicMock()
                result.returncode = 0
                return result
            return original_run(args, **kwargs)

        with patch("subprocess.run", side_effect=mock_run_for_push_only):
            success, message = _commit_and_push(
                cwd=cwd,
                issue_number=383,
                issue_title="Test all intermediate patterns",
                repo_owner="test",
                repo_name="repo",
                initial_file_hashes=initial_hashes,
                quiet=True,
            )

        committed_files = get_last_commit_files(cwd)

        assert "pdd/module.py" in committed_files, (
            "Legitimate file should be committed"
        )

        for f in intermediate_files:
            assert f not in committed_files, (
                f"BUG (Issue #383): Intermediate file {f} was committed! All: {committed_files}"
            )

    def test_e2e_only_intermediate_files_results_in_no_commit(self, e2e_git_repo):
        """E2E Test: When only intermediate files exist, no commit should be made."""
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push

        cwd = e2e_git_repo

        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=cwd, capture_output=True, text=True, check=True,
        )
        initial_commit = result.stdout.strip()

        (cwd / "pdd" / "module_fixed.py").write_text('"""Intermediate."""\n')
        (cwd / "tests" / "test_module_fixed.py").write_text('"""Intermediate."""\n')

        initial_hashes = {}

        original_run = subprocess.run
        def mock_run_for_push_only(args, **kwargs):
            if args[0:2] == ["git", "push"]:
                result = MagicMock()
                result.returncode = 0
                return result
            return original_run(args, **kwargs)

        with patch("subprocess.run", side_effect=mock_run_for_push_only):
            success, message = _commit_and_push(
                cwd=cwd,
                issue_number=383,
                issue_title="Test no commit when only intermediate",
                repo_owner="test",
                repo_name="repo",
                initial_file_hashes=initial_hashes,
                quiet=True,
            )

        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=cwd, capture_output=True, text=True, check=True,
        )
        final_commit = result.stdout.strip()

        if initial_commit != final_commit:
            committed_files = get_last_commit_files(cwd)
            intermediate_in_commit = [
                f for f in committed_files
                if "_fixed" in f or ".bak" in f or ".backup" in f or ".orig" in f or ".tmp" in f
            ]
            if intermediate_in_commit:
                pytest.fail(
                    f"BUG (Issue #383): Commit made with only intermediate files!\n"
                    f"Files committed: {intermediate_in_commit}\nMessage: {message}"
                )

    def test_e2e_pr44_exact_scenario(self, e2e_git_repo):
        """E2E Test: Replicate the exact scenario from PR #44 that exposed the bug."""
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push

        cwd = e2e_git_repo

        (cwd / "pdd" / "auth_test_commands.py").write_text(
            '"""Auth test commands - the actual fix."""\n'
        )
        (cwd / "tests" / "test_auth_test_commands.py").write_text(
            '"""Tests for auth test commands - the actual fix."""\n'
        )

        (cwd / "pdd" / "auth_test_commands_auth_fixed.py").write_text(
            '"""Intermediate - should not be committed (PR #44 bug)."""\n'
        )
        (cwd / "tests" / "test_auth_test_commands_auth_fixed.py").write_text(
            '"""Intermediate - should not be committed (PR #44 bug)."""\n'
        )

        initial_hashes = {}

        original_run = subprocess.run
        def mock_run_for_push_only(args, **kwargs):
            if args[0:2] == ["git", "push"]:
                result = MagicMock()
                result.returncode = 0
                return result
            return original_run(args, **kwargs)

        with patch("subprocess.run", side_effect=mock_run_for_push_only):
            success, message = _commit_and_push(
                cwd=cwd,
                issue_number=383,
                issue_title="PR #44 exact scenario",
                repo_owner="test",
                repo_name="repo",
                initial_file_hashes=initial_hashes,
                quiet=True,
            )

        committed_files = get_last_commit_files(cwd)

        for f in ["pdd/auth_test_commands_auth_fixed.py", "tests/test_auth_test_commands_auth_fixed.py"]:
            assert f not in committed_files, (
                f"BUG (Issue #383): PR #44 reproduced! {f} was committed. All: {committed_files}"
            )

        assert "pdd/auth_test_commands.py" in committed_files
        assert "tests/test_auth_test_commands.py" in committed_files
