"""Tests for Issue #894 Gap 1: run_pytest_and_capture_output subprocess deadlock.

Bug Context:
-----------
run_pytest_and_capture_output() in pytest_output.py uses bare subprocess.run()
without start_new_session=True or process group cleanup. When the orchestrator's
_verify_tests_independently() calls this function and a test spawns child
processes (e.g., E2E tests calling _run_with_provider → CLI subprocess), a
timeout kills only the pytest parent. Grandchild processes survive in the default
process group, holding stdout pipes open, which causes the executor's
read_stream() to hang waiting for EOF.

The fix from Issue #830 (commit a1e3b0e05) added _subprocess_run() with Popen +
os.killpg() for _run_with_provider, but run_pytest_and_capture_output was missed.

These tests verify that run_pytest_and_capture_output:
1. Uses start_new_session=True so child processes get their own process group
2. Calls os.killpg on timeout to kill orphaned child processes
"""

import signal
import subprocess

import pytest
from unittest.mock import patch, MagicMock, call


class TestPytestOutputProcessGroupCleanup:
    """run_pytest_and_capture_output must use process group kill on timeout."""

    def test_subprocess_uses_start_new_session(self, tmp_path):
        """The subprocess must be started with start_new_session=True so that
        child processes spawned by tests (e.g., _run_with_provider) are in a
        killable process group, not the parent's.
        """
        from pdd.pytest_output import run_pytest_and_capture_output

        # Create a minimal test file so the function doesn't bail early
        test_file = tmp_path / "test_dummy.py"
        test_file.write_text("def test_pass(): pass\n")

        mock_proc = MagicMock()
        mock_proc.communicate.return_value = ("1 passed", "")
        mock_proc.returncode = 0

        with patch("pdd.pytest_output.subprocess.Popen", return_value=mock_proc) as mock_popen, \
             patch("pdd.pytest_output._find_project_root", return_value=None), \
             patch("pdd.pytest_output.detect_host_python_executable", return_value="python3"):

            run_pytest_and_capture_output(str(test_file))

            # Verify Popen was called (not subprocess.run)
            assert mock_popen.called, (
                "BUG: run_pytest_and_capture_output still uses subprocess.run() "
                "instead of subprocess.Popen. Child processes from tests will "
                "become orphans on timeout, causing pipe deadlocks (Issue #894)."
            )

            # Verify start_new_session=True
            _, kwargs = mock_popen.call_args
            assert kwargs.get("start_new_session") is True, (
                "BUG: subprocess.Popen called without start_new_session=True. "
                "Child processes share the parent's process group and cannot be "
                "killed reliably on timeout."
            )

    def test_timeout_kills_process_group(self, tmp_path):
        """When pytest subprocess times out, os.killpg must be called to kill
        the entire process group, preventing orphaned child processes from
        holding pipes open.
        """
        from pdd.pytest_output import run_pytest_and_capture_output

        test_file = tmp_path / "test_dummy.py"
        test_file.write_text("def test_pass(): pass\n")

        mock_proc = MagicMock()
        mock_proc.pid = 99999
        mock_proc.communicate.side_effect = subprocess.TimeoutExpired(
            cmd="pytest", timeout=300
        )
        mock_proc.kill.return_value = None
        mock_proc.wait.return_value = None

        with patch("pdd.pytest_output.subprocess.Popen", return_value=mock_proc), \
             patch("pdd.pytest_output.os.killpg") as mock_killpg, \
             patch("pdd.pytest_output.os.getpgid", return_value=99999), \
             patch("pdd.pytest_output._find_project_root", return_value=None), \
             patch("pdd.pytest_output.detect_host_python_executable", return_value="python3"):

            result = run_pytest_and_capture_output(str(test_file))

            # Should still return a timeout result (not crash)
            assert result is not None
            assert result["test_results"][0]["errors"] == 1

            # The critical assertion: process group must be killed
            mock_killpg.assert_called_once_with(
                99999,
                signal.SIGKILL,
            ), (
                "BUG: run_pytest_and_capture_output does not call os.killpg() "
                "on timeout. Grandchild processes from test-spawned subprocesses "
                "become orphans and hold pipes open, causing executor deadlock "
                "(Issue #894)."
            )

    def test_killpg_failure_falls_back_to_proc_kill(self, tmp_path):
        """If os.killpg fails (process already gone), fall back to proc.kill()."""
        from pdd.pytest_output import run_pytest_and_capture_output

        test_file = tmp_path / "test_dummy.py"
        test_file.write_text("def test_pass(): pass\n")

        mock_proc = MagicMock()
        mock_proc.pid = 99999
        mock_proc.communicate.side_effect = subprocess.TimeoutExpired(
            cmd="pytest", timeout=300
        )
        mock_proc.kill.return_value = None
        mock_proc.wait.return_value = None

        with patch("pdd.pytest_output.subprocess.Popen", return_value=mock_proc), \
             patch("pdd.pytest_output.os.killpg", side_effect=ProcessLookupError), \
             patch("pdd.pytest_output.os.getpgid", return_value=99999), \
             patch("pdd.pytest_output._find_project_root", return_value=None), \
             patch("pdd.pytest_output.detect_host_python_executable", return_value="python3"):

            result = run_pytest_and_capture_output(str(test_file))

            # Should still return timeout result
            assert result is not None
            assert result["test_results"][0]["errors"] == 1

            # proc.kill() should be called as fallback
            mock_proc.kill.assert_called(), (
                "When os.killpg fails, proc.kill() must be called as fallback."
            )
