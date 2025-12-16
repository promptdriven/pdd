import pytest
from pdd.sync_orchestration import _detect_example_errors


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
