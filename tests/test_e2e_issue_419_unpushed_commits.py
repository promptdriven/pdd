"""
E2E Test for Issue #419: Agentic fix doesn't push commits when exiting early at Step 2

This test reproduces the bug where commits created by LLM agents during Step 1 are not
pushed to the remote repository when the workflow exits early at Step 2 with ALL_TESTS_PASS.

The bug is in pdd/agentic_e2e_fix_orchestrator.py, function _commit_and_push() at lines 237-238:

    if not files_to_commit:
        return True, "No changes to commit"  # ❌ BUG: Exits without pushing!

Root Cause:
1. Before workflow: initial_file_hashes = _get_file_hashes(cwd) returns {} (working tree clean)
2. Step 1: LLM agent modifies a file and CREATES A COMMIT
3. Step 2: Detects ALL_TESTS_PASS, exits early
4. After workflow: _commit_and_push() is called
5. Inside _commit_and_push():
   - current_hashes = _get_file_hashes(cwd) returns {} because working tree is clean
   - files_to_commit is empty (hash comparison finds no uncommitted changes)
   - Function returns "No changes to commit" WITHOUT executing git push
   - The commit from Step 1 remains unpushed

Expected Behavior:
When the workflow completes successfully, ALL commits created during the workflow should be
pushed to the remote, regardless of whether the workflow exits early or runs all 9 steps.

This test verifies the bug by:
1. Creating a real git repository with a remote
2. Simulating the workflow: initial_file_hashes captured with clean working tree
3. Simulating LLM agent: creating and committing a change
4. Calling _commit_and_push() with the initial_file_hashes
5. Verifying that the commit was NOT pushed (bug behavior)
"""

import pytest
import subprocess
import tempfile
from pathlib import Path
from pdd.agentic_e2e_fix_orchestrator import _commit_and_push, _get_file_hashes


class TestIssue419UnpushedCommitsE2E:
    """
    E2E tests for Issue #419: Verify commits are pushed even when workflow exits early.

    These tests reproduce the exact scenario where LLM agents create commits during Step 1
    and the workflow exits early at Step 2, but those commits are not pushed to remote.
    """

    def test_commit_and_push_with_clean_working_tree_and_unpushed_commits(self):
        """
        Primary Test for Issue #419: _commit_and_push should push unpushed commits
        even when working tree is clean.

        Scenario:
        1. Workflow starts with clean working tree
        2. LLM agent creates a commit during Step 1
        3. Workflow exits early at Step 2 (ALL_TESTS_PASS)
        4. _commit_and_push() is called with initial_file_hashes from before Step 1

        Expected (after fix):
        - Function detects unpushed commits
        - Executes git push
        - Returns success message like "Pushed existing commits"
        - Remote branch contains the commit

        Actual (bug behavior):
        - _get_file_hashes() returns {} (working tree is clean)
        - files_to_commit is empty
        - Returns "No changes to commit" without pushing
        - Remote does NOT contain the commit
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create a real git repository
            repo_path = Path(tmpdir) / "test_repo"
            repo_path.mkdir()

            # Initialize repo with initial commit
            subprocess.run(["git", "init", "-b", "main"], cwd=repo_path, check=True, capture_output=True)
            subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_path, check=True)
            subprocess.run(["git", "config", "user.name", "Test User"], cwd=repo_path, check=True)

            initial_file = repo_path / "README.md"
            initial_file.write_text("Initial content\n")
            subprocess.run(["git", "add", "README.md"], cwd=repo_path, check=True)
            subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_path, check=True)

            # Create a "remote" repository (bare repo to simulate GitHub)
            remote_path = Path(tmpdir) / "remote.git"
            subprocess.run(["git", "init", "--bare", str(remote_path)], check=True, capture_output=True)

            # Add remote and push initial commit
            subprocess.run(["git", "remote", "add", "origin", str(remote_path)], cwd=repo_path, check=True)
            subprocess.run(["git", "push", "-u", "origin", "main"], cwd=repo_path, check=True, capture_output=True)

            # SIMULATE WORKFLOW START: Capture initial file hashes (working tree is clean)
            initial_file_hashes = _get_file_hashes(repo_path)
            assert initial_file_hashes == {}, "Working tree should be clean before workflow starts"

            # SIMULATE STEP 1: LLM agent creates a fix and commits it
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

            # Verify commit exists locally
            log_result = subprocess.run(
                ["git", "log", "--oneline", "-1"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "Fix issue #419" in log_result.stdout, "Commit should exist locally"

            # Verify commit is NOT on remote yet
            remote_log = subprocess.run(
                ["git", "log", "origin/main", "--oneline", "-1"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "Fix issue #419" not in remote_log.stdout, "Commit should NOT be on remote yet"

            # Verify branch is ahead of remote
            status_result = subprocess.run(
                ["git", "status", "-sb"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "ahead 1" in status_result.stdout, "Branch should be ahead of remote by 1 commit"

            # SIMULATE WORKFLOW END: Call _commit_and_push with initial_file_hashes from before Step 1
            success, message = _commit_and_push(
                cwd=repo_path,
                issue_number=419,
                issue_title="Bug: Agentic fix doesn't push commits when exiting early at Step 2",
                initial_file_hashes=initial_file_hashes,
                quiet=True
            )

            # BUG CHECK: The function should push the commit, but currently returns "No changes to commit"
            assert success is True, f"_commit_and_push should succeed, got: {message}"

            # This is the BUG: The function returns "No changes to commit" without pushing
            if message == "No changes to commit":
                pytest.fail(
                    f"BUG DETECTED (Issue #419): _commit_and_push() returned '{message}' "
                    f"without pushing the commit created by the LLM agent.\n\n"
                    f"Root cause: _get_file_hashes() only detects uncommitted files using "
                    f"'git diff --name-only HEAD', which returns empty when working tree is clean.\n\n"
                    f"The commit from Step 1 exists locally but was NOT pushed to remote.\n\n"
                    f"Expected: Function should detect unpushed commits and execute 'git push'\n"
                    f"Actual: Function exits early at line 238 without pushing"
                )

            # After fix, verify the commit was pushed to remote
            remote_log_after = subprocess.run(
                ["git", "log", "origin/main", "--oneline", "-1"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "Fix issue #419" in remote_log_after.stdout, \
                "Commit should be pushed to remote after _commit_and_push()"

            # Verify branch is up to date with remote
            status_after = subprocess.run(
                ["git", "status", "-sb"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                check=True
            )
            assert "ahead" not in status_after.stdout, \
                "Branch should be up to date with remote (not ahead)"

    def test_commit_and_push_without_unpushed_commits_succeeds(self):
        """
        Edge Case Test: _commit_and_push should succeed when no commits or changes exist.

        Scenario:
        - Workflow exits early at Step 2 without creating any commits
        - No uncommitted files
        - No unpushed commits

        Expected:
        - Function returns success (no errors)
        - Message indicates "No changes to push" or "up to date"
        """
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
                initial_file_hashes=initial_file_hashes,
                quiet=True
            )

            # Should succeed without errors
            assert success is True, f"Should succeed when no changes exist, got: {message}"
            assert "No changes" in message or "up to date" in message.lower(), \
                f"Message should indicate no changes, got: {message}"

    def test_commit_and_push_with_uncommitted_changes_works_correctly(self):
        """
        Baseline Test: Verify existing behavior works for uncommitted changes.

        This test verifies the existing code path that already works correctly:
        when files are modified but not committed, _commit_and_push should commit and push them.

        This is NOT the bug scenario, but confirms the existing functionality still works.
        """
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
