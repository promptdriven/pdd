import subprocess
import pytest
from unittest.mock import patch, MagicMock
from pdd.sync_orchestration import _detect_example_errors, _run_example_with_error_detection


class TestDetectExampleErrors:
    """Test error detection patterns before implementation."""

    # === Tests for TRUE errors (should detect) ===

    def test_detects_python_traceback(self):
        """Traceback header catches ALL unhandled Python exceptions."""
        output = """
        INFO - Starting test
        Traceback (most recent call last):
          File "example.py", line 10, in <module>
            raise ValueError("test")
        ValueError: test
        """
        has_errors, summary = _detect_example_errors(output)
        assert has_errors is True
        assert 'Python traceback' in summary

    def test_detects_traceback_with_module_not_found(self):
        """ModuleNotFoundError is caught via traceback, not exception name."""
        output = """
        Traceback (most recent call last):
          File "example.py", line 1, in <module>
            import nonexistent
        ModuleNotFoundError: No module named 'nonexistent'
        """
        has_errors, _ = _detect_example_errors(output)
        assert has_errors is True

    def test_detects_traceback_with_connection_error(self):
        """ConnectionRefusedError is caught via traceback."""
        output = """
        Traceback (most recent call last):
          File "example.py", line 5, in <module>
            requests.get("http://localhost:9999")
        ConnectionRefusedError: [Errno 61] Connection refused
        """
        has_errors, _ = _detect_example_errors(output)
        assert has_errors is True

    def test_detects_error_log_level(self):
        """Python logging ERROR level format."""
        output = "2024-01-01 12:00:00 - ERROR - Connection failed"
        has_errors, _ = _detect_example_errors(output)
        assert has_errors is True

    # === Tests for FALSE positives (should NOT detect) ===

    def test_no_error_for_exception_name_without_traceback(self):
        """Exception names alone should NOT trigger (avoids false positives).

        Example: log message about testing error handling.
        """
        output = "INFO - Checking that TypeError is handled correctly"
        has_errors, _ = _detect_example_errors(output)
        assert has_errors is False

    def test_no_error_for_type_error_in_log(self):
        """Mentioning TypeError in logs should NOT trigger detection."""
        output = "INFO - Test validates TypeError response from API"
        has_errors, _ = _detect_example_errors(output)
        assert has_errors is False

    def test_no_errors_for_success_output(self):
        """The actual update_contribution_example.py success output."""
        output = """
        2024-01-01 12:00:00 - INFO - Seeded database with test contribution
        2024-01-01 12:00:00 - INFO - --- Test 1: Update Pricing ---
        2024-01-01 12:00:00 - INFO - Status: 200
        2024-01-01 12:00:00 - INFO - Response: {"success": true}
        2024-01-01 12:00:00 - INFO - --- Test 2: Update Exclusion ---
        2024-01-01 12:00:00 - INFO - Status: 200
        2024-01-01 12:00:00 - INFO - Response: {"success": true}
        2024-01-01 12:00:00 - INFO - --- Test 3: Invalid Action ---
        2024-01-01 12:00:00 - INFO - Status: 400
        2024-01-01 12:00:00 - INFO - Response: {"error": "Invalid action"}
        """
        has_errors, _ = _detect_example_errors(output)
        assert has_errors is False

    def test_no_errors_for_http_500_in_response(self):
        """HTTP 500 should NOT be treated as error (may be testing error handling)."""
        output = """
        INFO - Testing error handling
        INFO - Status: 500
        INFO - Response: {"error": "Internal server error"}
        """
        has_errors, _ = _detect_example_errors(output)
        assert has_errors is False

    def test_no_errors_for_json_with_error_key(self):
        """JSON with 'error' key should NOT trigger detection."""
        output = 'INFO - Response: {"error": "Invalid input", "code": 400}'
        has_errors, _ = _detect_example_errors(output)
        assert has_errors is False

    def test_no_errors_for_empty_output(self):
        has_errors, _ = _detect_example_errors("")
        assert has_errors is False

    def test_no_errors_for_info_log_only(self):
        """Pure INFO logs should not trigger."""
        output = "2024-01-01 12:00:00 - INFO - All tests completed"
        has_errors, _ = _detect_example_errors(output)
        assert has_errors is False


class TestRunExampleWithErrorDetection:
    """Test that _run_example_with_error_detection respects returncode."""

    @patch('pdd.sync_orchestration.subprocess.Popen')
    def test_returncode_zero_with_error_log_is_success(self, mock_popen):
        """Process that exits 0 should succeed even with ERROR logs.

        Regression test: returncode=0 means success, regardless of output.
        This matches the documented intent in sync_orchestration.py comments:
        "Zero exit code → success"

        Bug: Example logs non-fatal ERROR (Firebase emulator not running)
        but exits 0. Current code treats this as failure.
        """
        # Mock a process that exits with 0 but has ERROR in output
        mock_proc = MagicMock()
        mock_proc.returncode = 0
        mock_proc.stdout.readline.side_effect = [
            b"2026-01-07 - INFO - Starting example\n",
            b"2026-01-07 - ERROR - Error retrieving examples: HTTPConnectionPool(host='127.0.0.1', port=5001)...\n",
            b"2026-01-07 - INFO - Example completed successfully\n",
            b"",  # End of stdout
        ]
        mock_proc.stderr.readline.side_effect = [b""]  # No stderr
        mock_proc.wait.return_value = 0
        mock_popen.return_value = mock_proc

        returncode, stdout, stderr = _run_example_with_error_detection(
            cmd_parts=['python', 'test.py'],
            env={},
            cwd='/tmp',
            timeout=5
        )

        # Key assertion: returncode=0 should mean success, even with ERROR log
        assert returncode == 0, f"Expected 0 (success) but got {returncode}. Process exited 0, ERROR logs should not override."

    @patch('pdd.sync_orchestration.subprocess.Popen')
    def test_signal_killed_with_error_log_is_failure(self, mock_popen):
        """Process killed by signal with ERROR logs should fail.

        Server-style examples get killed by timeout. For these, we need
        to analyze output since returncode is just the signal number.
        """
        mock_proc = MagicMock()
        mock_proc.stdout.readline.side_effect = [
            b"2026-01-07 - ERROR - Connection failed\n",
            b"",
        ]
        mock_proc.stderr.readline.side_effect = [b""]
        mock_proc.terminate.return_value = None
        mock_proc.kill.return_value = None
        mock_popen.return_value = mock_proc

        # Simulate timeout then termination
        call_count = [0]
        def wait_side_effect(timeout=None):
            call_count[0] += 1
            if call_count[0] == 1:  # Initial wait - timeout
                raise subprocess.TimeoutExpired(cmd=['python'], timeout=5)
            # After terminate/kill
            mock_proc.returncode = -15  # SIGTERM
            return -15

        mock_proc.wait.side_effect = wait_side_effect
        mock_proc.returncode = -15  # Set initial value

        returncode, stdout, stderr = _run_example_with_error_detection(
            cmd_parts=['python', 'server.py'],
            env={},
            cwd='/tmp',
            timeout=5
        )

        # For signal-killed processes, ERROR logs should cause failure
        assert returncode == 1, f"Expected 1 (failure) for signal-killed with errors, got {returncode}"

    @patch('pdd.sync_orchestration.subprocess.Popen')
    def test_signal_killed_without_errors_is_success(self, mock_popen):
        """Process killed by signal without errors should succeed.

        Server ran fine until we killed it.
        """
        mock_proc = MagicMock()
        mock_proc.returncode = -15  # SIGTERM
        mock_proc.stdout.readline.side_effect = [
            b"2026-01-07 - INFO - Server started on port 8080\n",
            b"",
        ]
        mock_proc.stderr.readline.side_effect = [b""]
        mock_proc.wait.return_value = -15
        mock_popen.return_value = mock_proc

        returncode, stdout, stderr = _run_example_with_error_detection(
            cmd_parts=['python', 'server.py'],
            env={},
            cwd='/tmp',
            timeout=5
        )

        # No errors in output, so success
        assert returncode == 0, f"Expected 0 (success) for signal-killed without errors, got {returncode}"
