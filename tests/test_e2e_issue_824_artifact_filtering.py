"""
E2E test for issue #824: pdd fix agentic commits debug/backup files to PRs.

This test exercises the REAL _commit_and_push → _is_intermediate_file pipeline
using an actual git repository. Unlike the unit tests which test _is_intermediate_file
in isolation, and the integration tests which mock subprocess.run, this E2E test:

1. Creates a real git repository (git init, git commit)
2. Creates both legitimate code files and all artifact patterns from issue #824
3. Calls _commit_and_push with the REAL _is_intermediate_file filter (no mocking)
4. Uses real git add/commit operations (only git push is intercepted)
5. Inspects the actual git commit to verify which files were committed

This verifies the full end-to-end data flow: file detection → filtering → staging → commit.
"""

import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_e2e_fix_orchestrator import _commit_and_push


class TestE2EArtifactFiltering:
    """E2E: Verify _commit_and_push excludes all artifact patterns from real git commits."""

    @pytest.fixture
    def git_repo(self, tmp_path):
        """Create a real git repository with an initial commit."""
        subprocess.run(
            ["git", "init"], cwd=tmp_path, capture_output=True, check=True
        )
        subprocess.run(
            ["git", "config", "user.email", "test@example.com"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test User"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        # Initial commit so HEAD exists
        (tmp_path / "README.md").write_text("# project\n")
        subprocess.run(
            ["git", "add", "README.md"], cwd=tmp_path, capture_output=True, check=True
        )
        subprocess.run(
            ["git", "commit", "-m", "initial commit"],
            cwd=tmp_path, capture_output=True, check=True,
        )
        return tmp_path

    def _get_committed_files(self, cwd: Path) -> list[str]:
        """Get the list of files in the most recent commit."""
        result = subprocess.run(
            ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", "HEAD"],
            cwd=cwd, capture_output=True, text=True, check=True,
        )
        return [f for f in result.stdout.strip().split("\n") if f]

    def _create_artifact_files(self, cwd: Path) -> dict[str, list[str]]:
        """Create all artifact patterns from issue #824 plus legitimate files.

        Returns dict with 'legitimate' and 'artifact' file lists.
        """
        legitimate = ["module.py", "tests/test_module.py"]
        artifacts = [
            # .pdd/backups/** (timestamped iteration backups)
            ".pdd/backups/2026-03-09_123456/module.py",
            ".pdd/backups/2026-03-09_123456/test_module.py",
            # .pdd/core_dumps/*.json (crash/diagnostic dumps)
            ".pdd/core_dumps/pdd-core-abc123.json",
            # step*_output.md (workflow step debug output)
            "step9_output.md",
            # *_errors.txt / *_fix_errors.txt (test error logs)
            "waitlist_fix_errors.txt",
            "waitlist_test_errors.txt",
            # test_issue_*_reproduction.py (bug reproduction leftovers)
            "test_issue_824_reproduction.py",
            # Original #383 patterns (should still be filtered)
            "module_fixed.py",
            "tests/test_module_fixed.py",
            "module.py.bak",
        ]

        # Create legitimate files
        for f in legitimate:
            path = cwd / f
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"# legitimate: {f}\n")

        # Create artifact files
        for f in artifacts:
            path = cwd / f
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"# artifact: {f}\n")

        return {"legitimate": legitimate, "artifacts": artifacts}

    def _run_commit_and_push(self, cwd: Path) -> tuple[bool, str]:
        """Run _commit_and_push with only git push mocked (no remote)."""
        original_run = subprocess.run

        def intercept_push(args, **kwargs):
            """Let all git commands run for real except push."""
            if (
                isinstance(args, list)
                and len(args) >= 2
                and args[0] == "git"
                and args[1] == "push"
            ):
                result = MagicMock()
                result.returncode = 0
                result.stdout = ""
                result.stderr = ""
                return result
            return original_run(args, **kwargs)

        with patch("subprocess.run", side_effect=intercept_push):
            return _commit_and_push(
                cwd=cwd,
                issue_number=824,
                issue_title="pdd fix agentic is committing debug/backup files",
                repo_owner="test",
                repo_name="repo",
                initial_file_hashes={},  # empty = all files are "new"
                quiet=True,
            )

    def test_e2e_artifact_files_excluded_from_commit(self, git_repo):
        """E2E: Real git commit must contain only legitimate files, not artifacts.

        This is the primary E2E test for issue #824. It creates a real git repo,
        populates it with both legitimate code and all known artifact patterns,
        runs _commit_and_push with real git operations, then inspects the actual
        commit to verify artifact files were filtered out.
        """
        files = self._create_artifact_files(git_repo)

        success, message = self._run_commit_and_push(git_repo)

        # The commit should succeed
        assert success, f"_commit_and_push failed: {message}"

        # Inspect what was actually committed
        committed = self._get_committed_files(git_repo)

        # All legitimate files must be in the commit
        for f in files["legitimate"]:
            assert f in committed, (
                f"Legitimate file '{f}' was NOT committed. Committed: {committed}"
            )

        # NO artifact files should be in the commit
        for f in files["artifacts"]:
            assert f not in committed, (
                f"Issue #824: Artifact file '{f}' was committed but should have been "
                f"filtered by _is_intermediate_file(). Committed files: {committed}"
            )

    def test_e2e_artifact_files_excluded_via_fallback_path(self, git_repo):
        """E2E: Artifact filtering works on the fallback path (git diff/untracked).

        When initial_file_hashes match current state (no hash-diff changes detected),
        _commit_and_push falls back to _get_modified_and_untracked(). This test
        verifies that the fallback path also filters artifacts.
        """
        from pdd.agentic_e2e_fix_orchestrator import _get_file_hashes

        # Create files first, then snapshot hashes so the hash-diff path finds nothing
        files = self._create_artifact_files(git_repo)
        initial_hashes = _get_file_hashes(git_repo)

        # Now modify files so they appear in git diff (fallback detection)
        (git_repo / "module.py").write_text("# modified legitimate file\n")
        (git_repo / "step9_output.md").write_text("# modified artifact\n")
        (git_repo / "waitlist_fix_errors.txt").write_text("more errors\n")

        original_run = subprocess.run

        def intercept_push(args, **kwargs):
            if (
                isinstance(args, list)
                and len(args) >= 2
                and args[0] == "git"
                and args[1] == "push"
            ):
                result = MagicMock()
                result.returncode = 0
                result.stdout = ""
                result.stderr = ""
                return result
            return original_run(args, **kwargs)

        with patch("subprocess.run", side_effect=intercept_push):
            success, message = _commit_and_push(
                cwd=git_repo,
                issue_number=824,
                issue_title="Test fallback path filtering",
                repo_owner="test",
                repo_name="repo",
                initial_file_hashes=initial_hashes,
                quiet=True,
            )

        assert success, f"_commit_and_push failed: {message}"

        committed = self._get_committed_files(git_repo)

        assert "module.py" in committed, (
            f"Legitimate file 'module.py' was NOT committed via fallback. "
            f"Committed: {committed}"
        )
        assert "step9_output.md" not in committed, (
            "Issue #824: step9_output.md should NOT be committed via fallback path"
        )
        assert "waitlist_fix_errors.txt" not in committed, (
            "Issue #824: waitlist_fix_errors.txt should NOT be committed via fallback path"
        )

    def test_e2e_only_legitimate_files_in_git_diff_stat(self, git_repo):
        """E2E: After _commit_and_push, git show --stat must list only legitimate files.

        This is a complementary check using git show --stat (the same view a
        developer sees when reviewing a PR) to confirm no artifact files leaked.
        """
        files = self._create_artifact_files(git_repo)

        self._run_commit_and_push(git_repo)

        # Use git show --stat (what a reviewer sees)
        result = subprocess.run(
            ["git", "show", "--stat", "--format="],
            cwd=git_repo, capture_output=True, text=True, check=True,
        )
        stat_output = result.stdout

        # Artifact patterns should NOT appear in the stat output
        artifact_markers = [
            ".pdd/backups/",
            ".pdd/core_dumps/",
            "step9_output.md",
            "_errors.txt",
            "test_issue_824_reproduction.py",
            "_fixed.py",
            ".bak",
        ]
        for marker in artifact_markers:
            assert marker not in stat_output, (
                f"Issue #824: Artifact pattern '{marker}' found in git show --stat "
                f"output (would be visible in PR):\n{stat_output}"
            )
