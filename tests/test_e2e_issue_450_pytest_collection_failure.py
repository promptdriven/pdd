"""
E2E Test for Issue #450: IndexError crash when pytest collection/execution fails.

This E2E test exercises the full code path that triggers the bug described in
Issue #450. The bug occurs when `run_pytest_and_capture_output` returns a dict
with an empty `test_results` list.

Root Cause:
Line 213 in pdd/fix_error_loop.py:
    results = output_data.get("test_results", [{}])[0]

The default value [{}] only applies when the key is MISSING, not when it EXISTS
with an empty list. When test_results=[], accessing [0] causes IndexError.

E2E Test Strategy:
- Mock `run_pytest_and_capture_output` to return empty test_results list
- This simulates what COULD happen in edge cases or with pytest behavior changes
- Call `run_pytest_on_file()` and verify it crashes with IndexError
- Demonstrates the bug affects the full user-facing workflow

The tests should:
- FAIL on the current buggy code (IndexError crash)
- PASS once the bug is fixed (graceful error handling)
"""

from unittest.mock import patch

import pytest


@pytest.mark.e2e
class TestPytestCollectionFailureE2E:
    """E2E tests verifying graceful handling of pytest collection failures."""

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_empty_test_results_list_causes_index_error(self, mock_run_pytest):
        """
        E2E Test: run_pytest_on_file() crashes with IndexError when
        test_results is an empty list.

        This is the PRIMARY E2E test for Issue #450. It demonstrates the exact
        bug: when the key exists but the list is empty, accessing [0] crashes.

        Simulates: All 16+ failure scenarios where pytest returns empty results
        - Import errors
        - Syntax errors
        - Missing fixtures
        - Permission denied
        - File not found
        - Config errors
        - And 10+ more...

        Expected (after fix): Return (0, 1, 0, helpful_error_message)
        Actual (buggy code): IndexError: list index out of range
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Mock the exact problematic return value from Issue #450
        mock_run_pytest.return_value = {
            "test_results": [],  # Empty list - THE BUG
            "stdout": "ERROR: ImportError: No module named 'flask'",
            "stderr": "",
            "exit_code": 1
        }

        # THE KEY ASSERTION: This should crash with IndexError on line 213
        with pytest.raises(IndexError) as exc_info:
            failures, errors, warnings, logs = run_pytest_on_file("dummy_test.py")

        assert "list index out of range" in str(exc_info.value)

        # Document the bug for anyone reading the test output
        pytest.fail(
            f"BUG DETECTED (Issue #450): Empty test_results list causes IndexError!\n\n"
            f"Root Cause (Line 213):\n"
            f"  results = output_data.get('test_results', [{{}}])[0]\n\n"
            f"The default [{{}}] only applies when key is MISSING.\n"
            f"When key EXISTS with empty list [], .get() returns [].\n"
            f"Then [][0] → IndexError!\n\n"
            f"User Impact:\n"
            f"- Expected: 'Pytest collection failed: Missing import or dependency'\n"
            f"- Actual: IndexError: list index out of range\n\n"
            f"This makes users blame PDD instead of recognizing their test error.\n\n"
            f"Affects 16+ real-world scenarios where pytest collection fails.\n"
        )

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_import_error_scenario_crashes(self, mock_run_pytest):
        """
        E2E Test: Simulates Category 1: Import Error scenario.

        User scenario from Issue #450:
        1. User writes test with missing import: `import nonexistent_module`
        2. User runs `pdd fix test_api.py`
        3. pytest fails to collect (ImportError)
        4. test_results is empty
        5. PDD crashes with IndexError

        This test simulates the complete user workflow.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Simulate pytest collection failure due to import error
        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "ImportError: No module named 'flask'\ncollected 0 items / 1 error",
            "stderr": "",
            "exit_code": 2
        }

        with pytest.raises(IndexError) as exc_info:
            run_pytest_on_file("tests/test_api.py")

        assert "list index out of range" in str(exc_info.value)

        pytest.fail(
            f"BUG DETECTED (Issue #450): Import error causes IndexError crash!\n\n"
            f"User Scenario:\n"
            f"1. User writes: import nonexistent_module\n"
            f"2. User runs: pdd fix tests/test_api.py\n"
            f"3. pytest fails to collect (ImportError)\n"
            f"4. PDD crashes with IndexError\n\n"
            f"Expected: 'Pytest collection failed: Missing import or dependency'\n"
            f"Actual: {exc_info.value}\n"
        )

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_syntax_error_scenario_crashes(self, mock_run_pytest):
        """
        E2E Test: Simulates Category 1: Syntax Error scenario.

        When user has a syntax error in their test file, pytest can't parse it,
        returns empty test_results, and PDD crashes.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Simulate pytest collection failure due to syntax error
        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "SyntaxError: invalid syntax\nE   x = {\nE       ^\ncollected 0 items / 1 error",
            "stderr": "",
            "exit_code": 2
        }

        with pytest.raises(IndexError) as exc_info:
            run_pytest_on_file("tests/test_broken.py")

        assert "list index out of range" in str(exc_info.value)

        pytest.fail(
            f"BUG DETECTED (Issue #450): Syntax error causes IndexError crash!\n\n"
            f"When pytest encounters a syntax error during collection,\n"
            f"test_results is empty and accessing [0] crashes.\n\n"
            f"Expected: 'Pytest collection failed: Syntax error in test file'\n"
            f"Actual: {exc_info.value}\n"
        )

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_no_tests_found_scenario_crashes(self, mock_run_pytest):
        """
        E2E Test: Simulates Category 4: No Tests Found scenario.

        When pytest collects 0 tests (empty file or all skipped), test_results
        might be empty, causing the crash.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Simulate pytest finding no tests
        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "collected 0 items\n\nno tests ran in 0.01s",
            "stderr": "",
            "exit_code": 5
        }

        with pytest.raises(IndexError) as exc_info:
            run_pytest_on_file("tests/test_empty.py")

        assert "list index out of range" in str(exc_info.value)

        pytest.fail(
            f"BUG DETECTED (Issue #450): No tests found causes IndexError crash!\n\n"
            f"When pytest finds no tests (collected 0 items), test_results\n"
            f"is empty and accessing [0] crashes.\n\n"
            f"Expected: 'Pytest collection failed: No tests found'\n"
            f"Actual: {exc_info.value}\n"
        )

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_missing_fixture_scenario_crashes(self, mock_run_pytest):
        """
        E2E Test: Simulates Category 1: Missing Fixture scenario.

        When test references a non-existent fixture, pytest fails during
        collection, returns empty test_results, and PDD crashes.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Simulate pytest collection failure due to missing fixture
        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "ERROR: fixture 'nonexistent_fixture' not found\ncollected 0 items / 1 error",
            "stderr": "",
            "exit_code": 2
        }

        with pytest.raises(IndexError) as exc_info:
            run_pytest_on_file("tests/test_with_fixtures.py")

        assert "list index out of range" in str(exc_info.value)

        pytest.fail(
            f"BUG DETECTED (Issue #450): Missing fixture causes IndexError crash!\n\n"
            f"When pytest can't find a fixture, test_results is empty and\n"
            f"accessing [0] crashes.\n\n"
            f"Expected: 'Pytest collection failed: Missing fixture'\n"
            f"Actual: {exc_info.value}\n"
        )

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_permission_denied_scenario_crashes(self, mock_run_pytest):
        """
        E2E Test: Simulates Category 2: Permission Denied scenario.

        When pytest can't access a file due to permissions, it might return
        empty test_results, causing the crash.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Simulate pytest permission error
        mock_run_pytest.return_value = {
            "test_results": [],
            "stdout": "PermissionError: [Errno 13] Permission denied: 'tests/test_protected.py'",
            "stderr": "",
            "exit_code": 4
        }

        with pytest.raises(IndexError) as exc_info:
            run_pytest_on_file("tests/test_protected.py")

        assert "list index out of range" in str(exc_info.value)

        pytest.fail(
            f"BUG DETECTED (Issue #450): Permission denied causes IndexError crash!\n\n"
            f"When pytest encounters permission errors, test_results is empty\n"
            f"and accessing [0] crashes.\n\n"
            f"Expected: 'Pytest collection failed: Permission denied'\n"
            f"Actual: {exc_info.value}\n"
        )

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_complete_user_workflow_from_issue_450(self, mock_run_pytest):
        """
        E2E Integration Test: Simulates the EXACT user scenario from Issue #450.

        This is the most realistic E2E test - it replicates exactly what happens
        when a user encounters the bug in the wild.

        Scenario from Issue #450:
        ```python
        # tests/test_api.py
        def test_login():
            response = client.post('/login')  # NameError - client not imported
            assert response.status_code == 200
        ```

        User runs: pdd fix tests/test_api.py
        Expected: Clear error about missing import
        Actual: IndexError crash
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Exact scenario from the issue description
        mock_run_pytest.return_value = {
            "test_results": [],  # Empty because pytest couldn't collect
            "stdout": (
                "============================= test session starts ==============================\n"
                "collecting ... collected 0 items / 1 error\n\n"
                "==================================== ERRORS ====================================\n"
                "____________________ ERROR collecting tests/test_api.py ____________________\n"
                "tests/test_api.py:2: in <module>\n"
                "    def test_login():\n"
                "tests/test_api.py:3: in test_login\n"
                "    response = client.post('/login')  # NameError - client not imported\n"
                "E   NameError: name 'client' is not defined\n"
                "=========================== short test summary info ============================\n"
                "ERROR tests/test_api.py\n"
                "!!!!!!!!!!!!!!!!!!!! Interrupted: 1 error during collection !!!!!!!!!!!!!!!!!\n"
                "=============================== 1 error in 0.01s =======\n"
            ),
            "stderr": "",
            "exit_code": 2
        }

        # THE CRITICAL E2E ASSERTION
        with pytest.raises(IndexError) as exc_info:
            failures, errors, warnings, logs = run_pytest_on_file("tests/test_api.py")

        assert "list index out of range" in str(exc_info.value)

        # Comprehensive documentation of the bug
        pytest.fail(
            f"BUG DETECTED (Issue #450): Complete user workflow fails!\n\n"
            f"=== Exact Scenario from Issue #450 ===\n"
            f"1. User writes tests/test_api.py with:\n"
            f"   def test_login():\n"
            f"       response = client.post('/login')  # Missing import!\n\n"
            f"2. User runs: pdd fix tests/test_api.py\n\n"
            f"3. PDD internally calls run_pytest_on_file()\n\n"
            f"4. pytest tries to collect but fails:\n"
            f"   NameError: name 'client' is not defined\n\n"
            f"5. pytest returns empty test_results list\n\n"
            f"6. Line 213 crashes: results = output_data.get('test_results', [{{}}])[0]\n"
            f"   IndexError: list index out of range\n\n"
            f"=== Expected User Experience ===\n"
            f"Pytest collection failed: NameError: name 'client' is not defined\n"
            f"Check for missing imports in your test file\n\n"
            f"=== Actual User Experience ===\n"
            f"Traceback (most recent call last):\n"
            f"  File \"pdd/fix_error_loop.py\", line 213, in run_pytest_on_file\n"
            f"    results = output_data.get(\"test_results\", [{{}}])[0]\n"
            f"IndexError: list index out of range\n\n"
            f"=== Impact ===\n"
            f"- Users blame PDD instead of recognizing their test error\n"
            f"- Cannot distinguish between PDD bug vs test setup issue\n"
            f"- Affects 16+ different failure scenarios\n\n"
            f"Error: {exc_info.value}\n"
        )


@pytest.mark.e2e
class TestPytestCollectionFailureE2EEdgeCases:
    """E2E tests for additional edge cases beyond empty test_results."""

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_test_results_is_none_crashes(self, mock_run_pytest):
        """
        E2E Test: test_results is None instead of list causes TypeError.

        Edge case: If pytest behavior changes or an error occurs, test_results
        might be None instead of a list, causing different crash.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Mock test_results as None (malformed response)
        mock_run_pytest.return_value = {
            "test_results": None,  # None instead of list
            "stdout": "Critical pytest error",
            "stderr": "",
            "exit_code": 3
        }

        with pytest.raises(TypeError) as exc_info:
            run_pytest_on_file("dummy_test.py")

        pytest.fail(
            f"BUG DETECTED (Issue #450 Edge Case): test_results=None causes TypeError!\n\n"
            f"When test_results is None, accessing [0] crashes with TypeError.\n\n"
            f"Expected: Handle malformed data gracefully\n"
            f"Actual: {exc_info.value}\n"
        )

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_test_results_is_string_crashes(self, mock_run_pytest):
        """
        E2E Test: test_results is string instead of list causes TypeError.

        Edge case: Malformed data where test_results is a string.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Mock test_results as string (malformed response)
        mock_run_pytest.return_value = {
            "test_results": "error",  # String instead of list
            "stdout": "Critical pytest error",
            "stderr": "",
            "exit_code": 3
        }

        with pytest.raises(TypeError) as exc_info:
            run_pytest_on_file("dummy_test.py")

        pytest.fail(
            f"BUG DETECTED (Issue #450 Edge Case): test_results='error' causes TypeError!\n\n"
            f"When test_results is a string, accessing [0] crashes with TypeError.\n\n"
            f"Expected: Validate data type before accessing\n"
            f"Actual: {exc_info.value}\n"
        )

    @patch("pdd.fix_error_loop.run_pytest_and_capture_output")
    def test_test_results_contains_none_crashes(self, mock_run_pytest):
        """
        E2E Test: test_results=[None] causes AttributeError when accessing .get().

        Edge case: List contains None instead of dict.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Mock test_results with None element
        mock_run_pytest.return_value = {
            "test_results": [None],  # List with None element
            "stdout": "Critical pytest error",
            "stderr": "",
            "exit_code": 3
        }

        with pytest.raises(AttributeError) as exc_info:
            run_pytest_on_file("dummy_test.py")

        pytest.fail(
            f"BUG DETECTED (Issue #450 Edge Case): test_results=[None] causes AttributeError!\n\n"
            f"When test_results contains None, calling .get() crashes with AttributeError.\n\n"
            f"Expected: Validate dict structure before accessing\n"
            f"Actual: {exc_info.value}\n"
        )
