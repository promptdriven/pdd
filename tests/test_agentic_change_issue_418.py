"""
Unit Tests for Issue #418: Resource Leak - Temp Directories Not Cleaned Up When Git Clone Fails

This test verifies that temporary directories created during repository setup are
properly cleaned up when git clone operations fail.

The Bug:
- _setup_repository() creates a temp directory with tempfile.mkdtemp() at line 112
- When git clone fails, RuntimeError is raised at lines 129 or 131
- The temp directory is never cleaned up, causing disk space leaks
- Each failed operation leaves an orphaned directory on disk

Test Strategy:
- Use mocking to simulate clone failures
- Track temp directory creation and verify cleanup
- Cover both failure modes: non-zero exit code and subprocess exceptions
- Include regression test to ensure successful clones still work

User-Facing Impact:
- Network interruptions during clone
- Git authentication failures
- Rate limiting or private repository access errors
- Non-existent repositories
- Each failure leaks disk space permanently
"""

import json
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_change import run_agentic_change


class TestIssue418TempDirectoryLeak:
    """
    Unit tests for Issue #418: Temp directory resource leak when git clone fails.
    """

    def test_temp_dir_cleaned_up_on_clone_failure_nonzero_exit(self, tmp_path: Path):
        """
        Test that temp directory is cleaned up when git clone returns non-zero exit code.

        Scenario:
        1. run_agentic_change() is called with a valid issue URL
        2. _setup_repository() creates a temp directory (line 112)
        3. gh repo clone command returns non-zero exit code (network error, auth failure, etc.)
        4. RuntimeError is raised at line 129

        Expected: Temp directory should be cleaned up before raising the error
        Bug behavior: Temp directory remains on disk (leaked)

        This covers the most common failure scenarios:
        - Network interruptions
        - Authentication failures
        - Non-existent repositories
        - Rate limiting
        """
        # Create a real temp directory that we can verify exists/doesn't exist
        real_temp_dir = tmp_path / "pdd_test_repo_clone_fail"
        real_temp_dir.mkdir()

        with patch("pdd.agentic_change.shutil.which") as mock_which, \
             patch("pdd.agentic_change.subprocess.run") as mock_subprocess, \
             patch("pdd.agentic_change.tempfile.mkdtemp") as mock_mkdtemp, \
             patch("pdd.agentic_change.console"), \
             patch("pdd.agentic_change.Path.cwd") as mock_cwd:

            # Setup: gh is installed
            mock_which.return_value = "/usr/bin/gh"

            # Setup: temp directory creation returns our test path
            mock_mkdtemp.return_value = str(real_temp_dir)

            # Setup: Not in the target repository (force clone path)
            mock_cwd.return_value.__truediv__.return_value.exists.return_value = False

            # Setup: Issue API call succeeds
            issue_data = {
                "title": "Test Issue",
                "body": "Test body",
                "user": {"login": "testuser"},
                "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments"
            }

            def subprocess_side_effect(args, **kwargs):
                cmd = args if isinstance(args, list) else []

                # Issue API call succeeds (check the full path)
                if "api" in cmd and len(cmd) > 2 and "repos/owner/repo/issues/1" in cmd[2]:
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = json.dumps(issue_data)
                    return m

                # Comments API call succeeds
                if "api" in cmd and len(cmd) > 2 and "comments" in cmd[2]:
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = "[]"
                    return m

                # Git remote check fails (not in repo)
                if "git" in cmd[0] and "remote" in cmd:
                    m = MagicMock()
                    m.returncode = 1
                    return m

                # Clone fails with non-zero exit code
                if "repo" in cmd and "clone" in cmd:
                    m = MagicMock()
                    m.returncode = 1
                    m.stderr = "fatal: repository not found"
                    return m

                # Default
                m = MagicMock()
                m.returncode = 0
                m.stdout = ""
                return m

            mock_subprocess.side_effect = subprocess_side_effect

            # Verify temp dir exists before the call
            assert real_temp_dir.exists(), "Test setup failed: temp_dir should exist"

            # Execute: Call run_agentic_change which should fail and clean up
            success, msg, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")

            # Verify the function failed as expected
            assert success is False
            assert "Failed to clone repository" in msg

            # THE BUG CHECK: Temp directory should be cleaned up
            if real_temp_dir.exists():
                pytest.fail(
                    f"BUG DETECTED (Issue #418): Temp directory was not cleaned up!\n\n"
                    f"Scenario:\n"
                    f"  1. _setup_repository() creates temp_dir at line 112: tempfile.mkdtemp()\n"
                    f"  2. gh repo clone returns non-zero exit code (line 128)\n"
                    f"  3. RuntimeError raised at line 129: 'Failed to clone repository'\n"
                    f"  4. Temp directory never cleaned up - LEAKED!\n\n"
                    f"Results:\n"
                    f"  - Temp directory path: {real_temp_dir}\n"
                    f"  - Directory exists after error: {real_temp_dir.exists()} ⚠️\n"
                    f"  - Expected: Directory deleted before raising error\n\n"
                    f"Impact:\n"
                    f"  - Each failed clone leaks a temp directory\n"
                    f"  - Common triggers: network errors, auth failures, rate limiting\n"
                    f"  - Permanent disk space leak until manual cleanup\n\n"
                    f"Root Cause:\n"
                    f"  - Line 112 creates temp directory with mkdtemp()\n"
                    f"  - Line 129 raises RuntimeError without cleanup\n"
                    f"  - No shutil.rmtree() call before exception\n\n"
                    f"Fix:\n"
                    f"  Add cleanup before raising at line 129:\n"
                    f"    if result.returncode != 0:\n"
                    f"        shutil.rmtree(temp_dir, ignore_errors=True)\n"
                    f"        raise RuntimeError(...)\n"
                )

    def test_temp_dir_cleaned_up_on_subprocess_exception(self, tmp_path: Path):
        """
        Test that temp directory is cleaned up when subprocess.run raises an exception.

        Scenario:
        1. run_agentic_change() is called with a valid issue URL
        2. _setup_repository() creates a temp directory (line 112)
        3. subprocess.run() raises an exception (OSError, command not found, etc.)
        4. Exception is caught at line 130 and RuntimeError is raised at line 131

        Expected: Temp directory should be cleaned up before re-raising the error
        Bug behavior: Temp directory remains on disk (leaked)

        This covers less common but still real scenarios:
        - gh command not found or corrupted
        - OS-level errors (disk full, permission denied)
        - System resource exhaustion
        """
        real_temp_dir = tmp_path / "pdd_test_repo_exception"
        real_temp_dir.mkdir()

        with patch("pdd.agentic_change.shutil.which") as mock_which, \
             patch("pdd.agentic_change.subprocess.run") as mock_subprocess, \
             patch("pdd.agentic_change.tempfile.mkdtemp") as mock_mkdtemp, \
             patch("pdd.agentic_change.console"), \
             patch("pdd.agentic_change.Path.cwd") as mock_cwd:

            mock_which.return_value = "/usr/bin/gh"
            mock_mkdtemp.return_value = str(real_temp_dir)
            mock_cwd.return_value.__truediv__.return_value.exists.return_value = False

            issue_data = {
                "title": "Test Issue",
                "body": "Test body",
                "user": {"login": "testuser"},
                "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments"
            }

            call_count = [0]

            def subprocess_side_effect(args, **kwargs):
                cmd = args if isinstance(args, list) else []

                # Issue API call succeeds
                if "api" in cmd and len(cmd) > 2 and "repos/owner/repo/issues/1" in cmd[2]:
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = json.dumps(issue_data)
                    return m

                # Comments API call succeeds
                if "api" in cmd and len(cmd) > 2 and "comments" in cmd[2]:
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = "[]"
                    return m

                # Git remote check fails
                if "git" in cmd[0] and "remote" in cmd:
                    m = MagicMock()
                    m.returncode = 1
                    return m

                # Clone raises exception
                if "repo" in cmd and "clone" in cmd:
                    raise OSError("Command not found: gh")

                m = MagicMock()
                m.returncode = 0
                return m

            mock_subprocess.side_effect = subprocess_side_effect

            # Verify temp dir exists before the call
            assert real_temp_dir.exists(), "Test setup failed: temp_dir should exist"

            # Execute: Call run_agentic_change which should fail and clean up
            success, msg, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")

            # Verify the function failed as expected
            assert success is False
            assert "Failed to execute clone command" in msg

            # THE BUG CHECK: Temp directory should be cleaned up
            if real_temp_dir.exists():
                pytest.fail(
                    f"BUG DETECTED (Issue #418): Temp directory leaked on subprocess exception!\n\n"
                    f"Scenario:\n"
                    f"  1. _setup_repository() creates temp_dir at line 112\n"
                    f"  2. subprocess.run(['gh', 'repo', 'clone', ...]) raises exception (line 121)\n"
                    f"  3. Exception caught at line 130: except Exception as e\n"
                    f"  4. RuntimeError raised at line 131: 'Failed to execute clone command'\n"
                    f"  5. Temp directory never cleaned up - LEAKED!\n\n"
                    f"Results:\n"
                    f"  - Temp directory path: {real_temp_dir}\n"
                    f"  - Directory exists after exception: {real_temp_dir.exists()} ⚠️\n"
                    f"  - Expected: Directory deleted in exception handler\n\n"
                    f"Impact:\n"
                    f"  - Any subprocess exception leaks temp directory\n"
                    f"  - Triggers: missing gh command, OS errors, resource exhaustion\n"
                    f"  - Permanent disk space leak\n\n"
                    f"Fix:\n"
                    f"  Add cleanup in exception handler at line 130:\n"
                    f"    except Exception as e:\n"
                    f"        shutil.rmtree(temp_dir, ignore_errors=True)\n"
                    f"        raise RuntimeError(...)\n"
                )

    def test_temp_dir_not_cleaned_up_on_successful_clone(self, tmp_path: Path):
        """
        Regression test: Successful clone should NOT clean up the temp directory.

        Scenario:
        1. run_agentic_change() is called with a valid issue URL
        2. _setup_repository() creates a temp directory
        3. gh repo clone succeeds
        4. Temp directory is returned to caller for use

        Expected: Temp directory should exist and be returned
        Purpose: Ensure the fix doesn't over-aggressively clean up on success

        This is a regression test to ensure that our fix only cleans up on failure,
        and doesn't break the normal successful flow.
        """
        real_temp_dir = tmp_path / "pdd_test_repo_success"
        real_temp_dir.mkdir()

        with patch("pdd.agentic_change.shutil.which") as mock_which, \
             patch("pdd.agentic_change.subprocess.run") as mock_subprocess, \
             patch("pdd.agentic_change.tempfile.mkdtemp") as mock_mkdtemp, \
             patch("pdd.agentic_change.run_agentic_change_orchestrator") as mock_orch, \
             patch("pdd.agentic_change.console"), \
             patch("pdd.agentic_change.Path.cwd") as mock_cwd:

            mock_which.return_value = "/usr/bin/gh"
            mock_mkdtemp.return_value = str(real_temp_dir)
            mock_cwd.return_value.__truediv__.return_value.exists.return_value = False

            # Orchestrator returns success
            mock_orch.return_value = (True, "Success", 1.0, "gpt-4", ["file.py"])

            issue_data = {
                "title": "Test Issue",
                "body": "Test body",
                "user": {"login": "testuser"},
                "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments"
            }

            def subprocess_side_effect(args, **kwargs):
                cmd = args if isinstance(args, list) else []

                # Issue API call succeeds
                if "api" in cmd and len(cmd) > 2 and "repos/owner/repo/issues/1" in cmd[2]:
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = json.dumps(issue_data)
                    return m

                # Comments API call succeeds
                if "api" in cmd and len(cmd) > 2 and "comments" in cmd[2]:
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = "[]"
                    return m

                # Git remote check fails
                if "git" in cmd[0] and "remote" in cmd:
                    m = MagicMock()
                    m.returncode = 1
                    return m

                # Clone succeeds
                if "repo" in cmd and "clone" in cmd:
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = "Cloning..."
                    return m

                m = MagicMock()
                m.returncode = 0
                return m

            mock_subprocess.side_effect = subprocess_side_effect

            # Execute: Call run_agentic_change which should succeed
            success, msg, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")

            # Verify the function succeeded
            assert success is True

            # Regression check: On success, temp directory should still exist
            # (it's the caller's responsibility to use and clean it up)
            assert real_temp_dir.exists(), (
                f"Regression failure: Temp directory was deleted on successful clone!\n\n"
                f"The fix should only clean up on FAILURE, not on success.\n"
                f"Successful clones need the temp directory for subsequent operations.\n\n"
                f"Temp directory path: {real_temp_dir}\n"
                f"Expected: Directory exists after successful clone\n"
                f"Actual: Directory was deleted (broke existing functionality)"
            )

    def test_multiple_failures_accumulate_leaked_directories(self, tmp_path: Path):
        """
        Integration test: Multiple sequential failures accumulate leaked directories.

        Scenario:
        1. Call run_agentic_change() multiple times with different failing scenarios
        2. Each call creates a new temp directory
        3. Each call fails and should clean up its temp directory

        Expected: No temp directories leaked (each failure cleans up)
        Bug behavior: Each failure leaks a directory, accumulating over time

        This demonstrates the real-world impact where repeated operations (e.g., in CI/CD,
        automated workflows, or retry loops) cause significant disk waste over time.
        """
        leaked_dirs = []

        # Simulate 3 consecutive failures
        for i in range(3):
            real_temp_dir = tmp_path / f"pdd_test_repo_multi_{i}"
            real_temp_dir.mkdir()
            leaked_dirs.append(real_temp_dir)

            with patch("pdd.agentic_change.shutil.which") as mock_which, \
                 patch("pdd.agentic_change.subprocess.run") as mock_subprocess, \
                 patch("pdd.agentic_change.tempfile.mkdtemp") as mock_mkdtemp, \
                 patch("pdd.agentic_change.console"), \
                 patch("pdd.agentic_change.Path.cwd") as mock_cwd:

                mock_which.return_value = "/usr/bin/gh"
                mock_mkdtemp.return_value = str(real_temp_dir)
                mock_cwd.return_value.__truediv__.return_value.exists.return_value = False

                issue_data = {
                    "title": f"Test Issue {i}",
                    "body": f"Test body {i}",
                    "user": {"login": "testuser"},
                    "comments_url": f"https://api.github.com/repos/owner/repo/issues/{i}/comments"
                }

                def subprocess_side_effect(args, **kwargs):
                    cmd = args if isinstance(args, list) else []

                    # Issue API call succeeds
                    if "api" in cmd and len(cmd) > 2 and f"repos/owner/repo/issues/{i}" in cmd[2]:
                        m = MagicMock()
                        m.returncode = 0
                        m.stdout = json.dumps(issue_data)
                        return m

                    # Comments API call succeeds
                    if "api" in cmd and len(cmd) > 2 and "comments" in cmd[2]:
                        m = MagicMock()
                        m.returncode = 0
                        m.stdout = "[]"
                        return m

                    # Git remote check fails
                    if "git" in cmd[0] and "remote" in cmd:
                        m = MagicMock()
                        m.returncode = 1
                        return m

                    # Clone fails
                    if "repo" in cmd and "clone" in cmd:
                        m = MagicMock()
                        m.returncode = 1
                        m.stderr = f"Error {i}: Network timeout"
                        return m

                    m = MagicMock()
                    m.returncode = 0
                    return m

                mock_subprocess.side_effect = subprocess_side_effect

                # Execute: This should fail and clean up
                success, _, _, _, _ = run_agentic_change(f"https://github.com/owner/repo/issues/{i}")
                assert success is False

        # THE BUG CHECK: Count how many directories were leaked
        leaked_count = sum(1 for d in leaked_dirs if d.exists())

        if leaked_count > 0:
            leaked_paths = [str(d) for d in leaked_dirs if d.exists()]
            pytest.fail(
                f"BUG DETECTED (Issue #418): Multiple failures accumulated leaked directories!\n\n"
                f"Scenario:\n"
                f"  - Simulated 3 consecutive clone failures\n"
                f"  - Each created a new temp directory\n"
                f"  - Each should have cleaned up on failure\n\n"
                f"Results:\n"
                f"  - Total operations: 3\n"
                f"  - Directories leaked: {leaked_count} ⚠️\n"
                f"  - Leaked paths:\n    " + "\n    ".join(leaked_paths) + "\n\n"
                f"Impact:\n"
                f"  - In CI/CD: Repeated job failures fill up disk over time\n"
                f"  - In retry loops: Each retry leaks more space\n"
                f"  - In long-running services: Memory/disk exhaustion\n"
                f"  - Real-world example: 100 failures = 100 leaked directories\n\n"
                f"Fix Required:\n"
                f"  Every failure path must clean up temp_dir with shutil.rmtree()\n"
                f"  before raising exceptions."
            )
