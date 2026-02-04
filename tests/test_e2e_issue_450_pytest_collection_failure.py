"""
E2E Test for Issue #450: IndexError crash when pytest collection/execution fails.

This E2E test verifies the fix for Issue #450. The bug occurred when
`run_pytest_and_capture_output` returns a dict with an empty `test_results` list.

Fixed Behavior:
The code now validates test_results and provides helpful error messages instead of crashing.

The tests verify:
- Empty test_results list is handled gracefully with helpful error messages
- Type validation catches malformed data (None, string, etc.)
- All 16+ failure scenarios return useful diagnostics to users
"""

from unittest.mock import patch

import pytest


@pytest.mark.e2e
class TestPytestCollectionFailureE2E:
    """E2E tests verifying graceful handling of pytest collection failures."""

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_empty_test_results_list_causes_index_error(self, mock_run_pytest):
        """
        E2E Test: run_pytest_on_file() handles empty test_results gracefully.

        This is the PRIMARY E2E test for Issue #450. Verifies that when pytest
        returns empty test_results (due to collection failures), the code handles
        it gracefully instead of crashing with IndexError.

        Simulates: All 16+ failure scenarios where pytest returns empty results
        - Import errors
        - Syntax errors
        - Missing fixtures
        - Permission denied
        - File not found
        - Config errors
        - And 10+ more...

        After fix: Return (0, 1, 0, helpful_error_message)
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Mock the exact problematic return value from Issue #450
        mock_run_pytest.return_value = {
            "test_results": [],  # Empty list - triggers the validation path
            "stdout": "ERROR: ImportError: No module named 'flask'",
            "stderr": "",
            "exit_code": 1
        }

        # After fix: Should handle gracefully
        failures, errors, warnings, logs = run_pytest_on_file("dummy_test.py")

        # Verify error handling
        assert failures == 0
        assert errors == 1
        assert warnings == 0
        assert "Pytest collection failed: Missing import or dependency" in logs
        assert "ImportError" in logs

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_import_error_scenario_crashes(self, mock_run_pytest):
        """
        E2E Test: Simulates Category 1: Import Error scenario.

        User scenario from Issue #450:
        1. User writes test with missing import: `import nonexistent_module`
        2. User runs `pdd fix test_api.py`
        3. pytest fails to collect (ImportError)
        4. test_results is empty
        5. After fix: PDD provides helpful error message

        This test simulates the complete user workflow.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "ImportError: cannot import name 'nonexistent_module'",
            "stderr": "",
            "exit_code": 2
        }

        failures, errors, warnings, logs = run_pytest_on_file("tests/test_api.py")

        assert failures == 0
        assert errors == 1
        assert warnings == 0
        assert "Pytest collection failed: Missing import or dependency" in logs

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_syntax_error_scenario_crashes(self, mock_run_pytest):
        """
        E2E Test: Simulates Category 1: Syntax Error scenario.

        When pytest encounters a syntax error during collection,
        test_results is empty. After fix: helpful error message.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "SyntaxError: invalid syntax in test_api.py",
            "stderr": "",
            "exit_code": 2
        }

        failures, errors, warnings, logs = run_pytest_on_file("tests/test_api.py")

        assert failures == 0
        assert errors == 1
        assert warnings == 0
        assert "Pytest collection failed: Syntax error in test file" in logs

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_no_tests_found_scenario_crashes(self, mock_run_pytest):
        """
        E2E Test: Simulates Category 4: No tests found scenario.

        When pytest finds no tests (collected 0 items), test_results
        is empty. After fix: helpful error message.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "collected 0 items",
            "stderr": "",
            "exit_code": 5
        }

        failures, errors, warnings, logs = run_pytest_on_file("tests/test_empty.py")

        assert failures == 0
        assert errors == 1
        assert warnings == 0
        assert "Pytest collection failed: No tests found" in logs

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_missing_fixture_scenario_crashes(self, mock_run_pytest):
        """
        E2E Test: Simulates Category 1: Missing fixture scenario.

        When pytest can't find a fixture, test_results is empty.
        After fix: helpful error message.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "fixture 'db' not found",
            "stderr": "",
            "exit_code": 2
        }

        failures, errors, warnings, logs = run_pytest_on_file("tests/test_db.py")

        assert failures == 0
        assert errors == 1
        assert warnings == 0
        assert "Pytest collection or execution failed" in logs

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_permission_denied_scenario_crashes(self, mock_run_pytest):
        """
        E2E Test: Simulates Category 2: Permission denied scenario.

        When pytest encounters permission errors, test_results is empty.
        After fix: helpful error message.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "PermissionError: [Errno 13] Permission denied",
            "stderr": "",
            "exit_code": 2
        }

        failures, errors, warnings, logs = run_pytest_on_file("tests/test_restricted.py")

        assert failures == 0
        assert errors == 1
        assert warnings == 0
        assert "Pytest collection failed: Permission denied" in logs

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_complete_user_workflow_from_issue_450(self, mock_run_pytest):
        """
        E2E Test: Complete user workflow from Issue #450.

        === Exact Scenario from Issue #450 ===
        1. User writes tests/test_api.py with:
           def test_login():
               response = client.post('/login')  # Missing import!

        2. User runs: pdd fix tests/test_api.py

        3. PDD internally calls run_pytest_on_file()

        4. pytest tries to collect but fails:
           NameError: name 'client' is not defined

        5. pytest returns empty test_results list

        6. After fix: Helpful error message instead of IndexError crash
        """
        from pdd.fix_error_loop import run_pytest_on_file

        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "NameError: name 'client' is not defined",
            "stderr": "",
            "exit_code": 2
        }

        failures, errors, warnings, logs = run_pytest_on_file("tests/test_api.py")

        # Verify graceful handling
        assert failures == 0
        assert errors == 1
        assert warnings == 0
        assert "Pytest collection or execution failed" in logs
        assert "NameError" in logs


@pytest.mark.e2e
class TestPytestCollectionFailureE2EEdgeCases:
    """E2E tests for edge cases with malformed test_results data."""

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_test_results_is_none_crashes(self, mock_run_pytest):
        """
        E2E Test: test_results is None instead of list.

        Edge case: If pytest behavior changes or an error occurs, test_results
        might be None. After fix: type validation catches this.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Mock test_results as None (malformed response)
        mock_run_pytest.return_value = {
            "test_results": None,  # None instead of list
            "stdout": "Critical pytest error",
            "stderr": "",
            "exit_code": 3
        }

        failures, errors, warnings, logs = run_pytest_on_file("tests/test_broken.py")

        assert failures == 0
        assert errors == 1
        assert warnings == 0
        assert "Pytest returned invalid data" in logs

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_test_results_is_string_crashes(self, mock_run_pytest):
        """
        E2E Test: test_results is string instead of list.

        Edge case: Malformed data where test_results is a string.
        After fix: type validation catches this.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Mock test_results as string (malformed response)
        mock_run_pytest.return_value = {
            "test_results": "error",  # String instead of list
            "stdout": "Critical pytest error",
            "stderr": "",
            "exit_code": 3
        }

        failures, errors, warnings, logs = run_pytest_on_file("tests/test_broken.py")

        assert failures == 0
        assert errors == 1
        assert warnings == 0
        assert "Pytest returned invalid data" in logs

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_test_results_contains_none_crashes(self, mock_run_pytest):
        """
        E2E Test: test_results=[None] causes validation error.

        Edge case: List contains None instead of dict.
        After fix: dict structure validation catches this.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Mock test_results with None element
        mock_run_pytest.return_value = {
            "test_results": [None],  # List with None element
            "stdout": "Critical pytest error",
            "stderr": "",
            "exit_code": 3
        }

        failures, errors, warnings, logs = run_pytest_on_file("tests/test_broken.py")

        assert failures == 0
        assert errors == 1
        assert warnings == 0
        assert "Pytest returned invalid result format" in logs
