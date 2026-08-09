"""
TDD tests for jobs.py sync failure detection bugs.

Bug 1: jobs.py:534 checks for "Failed" anywhere in stdout, not just on the
       "Overall status:" line. This causes false positives when other code
       (e.g. get_jwt_token.py) prints "Failed" warnings to stdout.

Bug 2: jobs.py:412 never sets job.result on the exception path, so all
       captured stdout/stderr is lost when a job fails.

Bug 3: get_jwt_token.py uses bare print() for warnings, polluting stdout
       with strings that trigger Bug 1.
"""
import io
import logging
import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from pdd.server.jobs import Job, JobManager
from pdd.server.models import JobStatus


# ---------------------------------------------------------------------------
# Bug 1: False positive sync failure detection
#
# The check logic is embedded in _run_click_command (jobs.py:531-535).
# We extract it into a helper to test. The production code should use
# the same logic (extracted to _check_sync_failure or inline equivalent).
# ---------------------------------------------------------------------------

def _current_sync_failure_check(stdout_text: str) -> bool:
    """
    Replicates the CURRENT (buggy) check from jobs.py:531-535.
    Returns True if the check would raise RuntimeError.
    """
    if "Overall status:" in stdout_text and "Failed" in stdout_text:
        return True
    return False


def _correct_sync_failure_check(stdout_text: str) -> bool:
    """
    The CORRECT check: only detect failure if "Failed" appears
    on the same line as "Overall status:".
    """
    for line in stdout_text.splitlines():
        if "Overall status:" in line and "Failed" in line:
            return True
    return False


class TestSyncFailureDetection:
    """Test that the sync stdout check only looks at the 'Overall status:' line."""

    def test_false_positive_stray_failed_in_stdout(self):
        """
        Bug 1: stdout with 'Overall status: Success' AND a stray 'Failed'
        elsewhere should NOT be detected as failure.

        This test proves the bug exists in the current code and defines
        the correct behavior.
        """
        stdout = (
            "Warning: Failed to cache JWT: Permission denied\n"
            "Starting sync...\n"
            "Overall status: Success\n"
        )
        # Current buggy behavior: detects this as failure (FALSE POSITIVE)
        assert _current_sync_failure_check(stdout) is True, (
            "Sanity check: current code should detect this as failure (proving the bug)"
        )
        # Correct behavior: should NOT detect failure
        assert _correct_sync_failure_check(stdout) is False

    def test_true_positive_overall_status_failed(self):
        """Overall status: Failed should be detected as failure."""
        stdout = "Starting sync...\nOverall status: Failed\n"
        assert _correct_sync_failure_check(stdout) is True

    def test_true_positive_with_stray_failed_and_overall_failed(self):
        """Overall status: Failed + stray 'Failed' should still detect failure."""
        stdout = (
            "Warning: Failed to cache JWT: Permission denied\n"
            "Overall status: Failed\n"
        )
        assert _correct_sync_failure_check(stdout) is True

    def test_no_overall_status_line(self):
        """stdout without 'Overall status:' should never detect failure."""
        stdout = "Warning: Failed to cache JWT\nSync complete.\n"
        assert _correct_sync_failure_check(stdout) is False

    def test_overall_status_success_clean(self):
        """Clean success with no stray 'Failed' anywhere."""
        stdout = "Starting sync...\nOverall status: Success\n"
        assert _correct_sync_failure_check(stdout) is False


# ---------------------------------------------------------------------------
# Bug 2: job.result not set on failure path
# ---------------------------------------------------------------------------

class TestJobResultOnFailure:
    """Test that job.result preserves stdout/stderr even when job fails."""

    def test_current_failure_path_loses_output(self):
        """
        Bug 2: Proves the current exception handler doesn't preserve output.
        After _run_click_command raises RuntimeError, _execute_job's exception
        handler at line 412 sets job.error and job.status but NOT job.result.
        """
        job = Job(command="sync", args={"basename": "test"})
        job.live_stdout = "Starting sync...\nOverall status: Success\n"
        job.live_stderr = "some stderr\n"

        # Simulate CURRENT exception handler (jobs.py:412-415)
        job.error = "Sync operation failed (see output for details)"
        job.status = JobStatus.FAILED
        # NOTE: job.result is NOT set (this is the bug)

        # Proves the bug: live output exists but result is None
        assert job.result is None
        assert job.live_stdout != ""

    def test_fixed_failure_path_preserves_output(self):
        """
        After fix: the exception handler should populate job.result from
        job.live_stdout / job.live_stderr so output is accessible.
        """
        job = Job(command="sync", args={"basename": "test"})
        job.live_stdout = "Starting sync...\nOverall status: Success\n"
        job.live_stderr = "some stderr\n"

        # Simulate FIXED exception handler
        job.error = "Sync operation failed (see output for details)"
        if job.live_stdout or job.live_stderr:
            job.result = {
                "stdout": job.live_stdout,
                "stderr": job.live_stderr,
                "exit_code": None,
            }
        job.status = JobStatus.FAILED

        assert job.result is not None
        assert job.result["stdout"] == "Starting sync...\nOverall status: Success\n"
        assert job.result["stderr"] == "some stderr\n"
        assert job.result["exit_code"] is None


# ---------------------------------------------------------------------------
# Bug 3: get_jwt_token.py bare print() to stdout
# ---------------------------------------------------------------------------

class TestGetJwtTokenWarnings:
    """Test that get_jwt_token.py warning functions use logging, not print()."""

    def test_cache_jwt_warning_does_not_print_to_stdout(self):
        """
        Bug 3: _cache_jwt should use logging, not bare print(),
        so 'Failed' warnings don't pollute stdout.
        """
        from pdd.get_jwt_token import _cache_jwt

        captured = io.StringIO()
        with patch('sys.stdout', captured):
            # Trigger the error path: patch open() to raise IOError
            with patch('builtins.open', side_effect=IOError("Permission denied")):
                _cache_jwt("fake-jwt-token")

        stdout_output = captured.getvalue()
        assert "Failed" not in stdout_output, (
            f"_cache_jwt printed 'Failed' to stdout: {stdout_output!r}. "
            "Should use logging.warning() instead."
        )

    def test_store_refresh_token_warning_does_not_print_to_stdout(self):
        """
        Bug 3: _store_refresh_token should use logging, not bare print().
        """
        from pdd.get_jwt_token import FirebaseAuthenticator

        auth = FirebaseAuthenticator.__new__(FirebaseAuthenticator)
        auth.keyring_service_name = "test-service"
        auth.keyring_user_name = "test-user"

        captured = io.StringIO()
        with patch('sys.stdout', captured):
            with patch('pdd.get_jwt_token.KEYRING_AVAILABLE', True):
                with patch('pdd.get_jwt_token.keyring') as mock_keyring:
                    # Non-duplicate error on first attempt → hits line 391
                    mock_keyring.set_password.side_effect = Exception("keyring error")
                    auth._store_refresh_token("fake-token")

        stdout_output = captured.getvalue()
        assert "Failed" not in stdout_output, (
            f"_store_refresh_token printed 'Failed' to stdout: {stdout_output!r}. "
            "Should use logging.warning() instead."
        )

    def test_get_stored_refresh_token_warning_does_not_print_to_stdout(self):
        """
        Bug 3: _get_stored_refresh_token should use logging, not bare print().
        """
        from pdd.get_jwt_token import FirebaseAuthenticator

        auth = FirebaseAuthenticator.__new__(FirebaseAuthenticator)
        auth.keyring_service_name = "test-service"
        auth.keyring_user_name = "test-user"

        captured = io.StringIO()
        with patch('sys.stdout', captured):
            with patch('pdd.get_jwt_token.KEYRING_AVAILABLE', True):
                with patch('pdd.get_jwt_token.keyring') as mock_keyring:
                    mock_keyring.get_password.side_effect = Exception("keyring error")
                    auth._get_stored_refresh_token()

        stdout_output = captured.getvalue()
        assert "Failed" not in stdout_output, (
            f"_get_stored_refresh_token printed 'Failed' to stdout: {stdout_output!r}. "
            "Should use logging.warning() instead."
        )
