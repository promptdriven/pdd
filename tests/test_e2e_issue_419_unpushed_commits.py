"""
E2E Test for Issue #419: Agentic fix doesn't push commits when exiting early

Tests that _commit_and_push() pushes existing commits even when the working tree is clean.
The bug occurs when LLM agents create commits during Step 1 and the workflow exits early at
Step 2 - those commits weren't being pushed because _get_file_hashes() only detects uncommitted changes.
"""

import pytest
import subprocess
import tempfile
from pathlib import Path
from pdd.agentic_e2e_fix_orchestrator import _commit_and_push, _get_file_hashes


class TestIssue419UnpushedCommitsE2E:
    """Tests for Issue #419: _commit_and_push pushes existing commits when working tree is clean."""

    def test_commit_and_push_with_clean_working_tree_and_unpushed_commits(self):
        """Test that _commit_and_push pushes existing commits when working tree is clean."""
        with tempfile.TemporaryDirectory() as tmpdir:
            repo_path = Path(tmpdir) / "test_repo"
            repo_path.mkdir()

            subprocess.run(["git", "init", "-b", "main"], cwd=repo_path, check=True, capture_output=True)
            subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_path, check=True)
            subprocess.run(["git", "config", "user.name", "Test User"], cwd=repo_path, check=True)

            initial_file = repo_path / "README.md"
            initial_file.write_text("Initial content\n")
            subprocess.run(["git", "add", "README.md"], cwd=repo_path, check=True)
            subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_path, check=True)

            remote_path = Path(tmpdir) / "remote.git"
            subprocess.run(["git", "init", "--bare", str(remote_path)], check=True, capture_output=True)
            subprocess.run(["git", "remote", "add", "origin", str(remote_path)], cwd=repo_path, check=True)
            subprocess.run(["git", "push", "-u", "origin", "main"], cwd=repo_path, check=True, capture_output=True)

            # Capture initial state (clean working tree)
            initial_file_hashes = _get_file_hashes(repo_path)
            assert initial_file_hashes == {}, "Working tree should be clean before workflow starts"

            # Simulate LLM agent creating and committing a fix
            test_file = repo_path / "pdd" / "commands" / "generate.py"
            test_file.parent.mkdir(parents=True, exist_ok=True)
            test_file.write_text("def generate():\n    # Fixed bug\n    pass\n")

            subprocess.run(["git", "add", str(test_file.relative_to(repo_path))], cwd=repo_path, check=True)
            subprocess.run(
                ["git", "commit", "-m", "Fix issue #419: LLM agent commit"],
                cwd=repo_path,
                check=True,
                capture_output=True
            )

            log_result = subprocess.run(
                ["git", "log", "--oneline", "-1"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "Fix issue #419" in log_result.stdout

            remote_log = subprocess.run(
                ["git", "log", "origin/main", "--oneline", "-1"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "Fix issue #419" not in remote_log.stdout

            status_result = subprocess.run(
                ["git", "status", "-sb"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "ahead 1" in status_result.stdout

            # Call _commit_and_push with initial hashes
            success, message = _commit_and_push(
                cwd=repo_path,
                issue_number=419,
                issue_title="Bug: Agentic fix doesn't push commits when exiting early at Step 2",
                repo_owner="owner", repo_name="repo",
                initial_file_hashes=initial_file_hashes,
                quiet=True
            )

            assert success is True, f"_commit_and_push should succeed, got: {message}"

            if message == "No changes to commit":
                pytest.fail(
                    f"BUG: _commit_and_push() returned '{message}' without pushing. "
                    f"Commit exists locally but was not pushed to remote."
                )

            # Verify commit was pushed
            remote_log_after = subprocess.run(
                ["git", "log", "origin/main", "--oneline", "-1"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "Fix issue #419" in remote_log_after.stdout

            status_after = subprocess.run(
                ["git", "status", "-sb"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "ahead" not in status_after.stdout

    def test_commit_and_push_without_unpushed_commits_succeeds(self):
        """Test that _commit_and_push succeeds when there are no changes or unpushed commits."""
        with tempfile.TemporaryDirectory() as tmpdir:
            repo_path = Path(tmpdir) / "test_repo"
            repo_path.mkdir()

            # Initialize and set up repo with remote
            subprocess.run(["git", "init", "-b", "main"], cwd=repo_path, check=True, capture_output=True)
            subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_path, check=True)
            subprocess.run(["git", "config", "user.name", "Test User"], cwd=repo_path, check=True)

            initial_file = repo_path / "README.md"
            initial_file.write_text("Initial content\n")
            subprocess.run(["git", "add", "README.md"], cwd=repo_path, check=True)
            subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_path, check=True)

            remote_path = Path(tmpdir) / "remote.git"
            subprocess.run(["git", "init", "--bare", str(remote_path)], check=True, capture_output=True)
            subprocess.run(["git", "remote", "add", "origin", str(remote_path)], cwd=repo_path, check=True)
            subprocess.run(["git", "push", "-u", "origin", "main"], cwd=repo_path, check=True, capture_output=True)

            # Capture initial state (clean)
            initial_file_hashes = _get_file_hashes(repo_path)

            # Call _commit_and_push without any changes
            success, message = _commit_and_push(
                cwd=repo_path,
                issue_number=419,
                issue_title="Test issue",
                repo_owner="owner", repo_name="repo",
                initial_file_hashes=initial_file_hashes,
                quiet=True
            )

            # Should succeed without errors
            assert success is True, f"Should succeed when no changes exist, got: {message}"
            assert "No changes" in message or "up to date" in message.lower(), \
                f"Message should indicate no changes, got: {message}"

    def test_commit_and_push_with_uncommitted_changes_works_correctly(self):
        """Test that _commit_and_push commits and pushes uncommitted changes (baseline)."""
        with tempfile.TemporaryDirectory() as tmpdir:
            repo_path = Path(tmpdir) / "test_repo"
            repo_path.mkdir()

            # Set up repo
            subprocess.run(["git", "init", "-b", "main"], cwd=repo_path, check=True, capture_output=True)
            subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_path, check=True)
            subprocess.run(["git", "config", "user.name", "Test User"], cwd=repo_path, check=True)

            initial_file = repo_path / "README.md"
            initial_file.write_text("Initial content\n")
            subprocess.run(["git", "add", "README.md"], cwd=repo_path, check=True)
            subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_path, check=True)

            remote_path = Path(tmpdir) / "remote.git"
            subprocess.run(["git", "init", "--bare", str(remote_path)], check=True, capture_output=True)
            subprocess.run(["git", "remote", "add", "origin", str(remote_path)], cwd=repo_path, check=True)
            subprocess.run(["git", "push", "-u", "origin", "main"], cwd=repo_path, check=True, capture_output=True)

            # Capture initial state
            initial_file_hashes = _get_file_hashes(repo_path)

            # Create uncommitted changes
            test_file = repo_path / "new_file.py"
            test_file.write_text("print('hello')\n")

            # Call _commit_and_push
            success, message = _commit_and_push(
                cwd=repo_path,
                issue_number=419,
                issue_title="Test issue",
                repo_owner="owner", repo_name="repo",
                initial_file_hashes=initial_file_hashes,
                quiet=True
            )

            # Should commit and push the new file
            assert success is True, f"Should succeed, got: {message}"
            assert "Committed and pushed 1 file(s)" in message, \
                f"Should report committing 1 file, got: {message}"

            # Verify file is in remote
            remote_files = subprocess.run(
                ["git", "ls-tree", "-r", "origin/main", "--name-only"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "new_file.py" in remote_files.stdout, \
                "New file should be pushed to remote"
