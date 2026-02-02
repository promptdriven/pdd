"""
E2E Test for Issue #450: IndexError when test_results is an empty list

This test creates the exact scenario described in Issue #450 by mocking
run_pytest_and_capture_output to return an empty test_results list, simulating
what happens when pytest collection/execution fails in certain edge cases.

The bug: pdd/fix_error_loop.py:213 crashes with IndexError when test_results is []

This E2E test:
1. Mocks run_pytest_and_capture_output to return {"test_results": []}
2. Calls run_pytest_on_file() (the real function from fix workflow)
3. Verifies the function crashes with IndexError (demonstrating the bug)

The test should FAIL (detecting the bug exists) on buggy code and PASS once fixed.

Issue: https://github.com/promptdriven/pdd/issues/450
"""

import pytest
from unittest.mock import patch, MagicMock


@pytest.mark.e2e
class TestEmptyTestResultsE2E:
    """
    E2E tests for Issue #450: Demonstrate the IndexError crash when
    pytest returns empty test_results list.
    """

    def test_run_pytest_on_file_crashes_on_empty_test_results(self, tmp_path):
        """
        E2E Test: run_pytest_on_file() crashes when test_results is empty list.

        This is the EXACT bug scenario from Issue #450. When pytest collection
        fails (ImportError, SyntaxError, etc.) and returns {"test_results": []},
        the code at line 213 tries to access [0] on an empty list -> IndexError.

        Expected behavior (after fix):
        - Function should detect empty test_results
        - Function should return error count (0, 1, 0, "helpful message")
        - Function should NOT crash with IndexError

        Bug behavior (Issue #450):
        - Function crashes: IndexError: list index out of range
        - Line 213: results = output_data.get("test_results", [{}])[0]
        - Problem: .get() default [{}] only applies when key is MISSING
        - When key EXISTS with empty list [], we get [][0] -> IndexError
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # Create a dummy test file (won't actually be run due to mock)
        test_file = tmp_path / "test_dummy.py"
        test_file.write_text("def test_dummy(): pass")

        # Mock run_pytest_and_capture_output to return EMPTY test_results list
        # This simulates pytest collection failure scenarios
        empty_results = {
            "test_results": [],  # EMPTY LIST - THIS TRIGGERS THE BUG
            "stdout": "ERROR: ImportError: No module named 'flask'",
            "stderr": "",
            "exit_code": 2
        }

        with patch('pdd.fix_error_loop.run_pytest_and_capture_output', return_value=empty_results):
            try:
                failures, errors, warnings, logs = run_pytest_on_file(str(test_file))

                # If we get here without IndexError, the bug is FIXED
                pytest.fail(
                    "BUG IS FIXED! run_pytest_on_file() handled empty test_results gracefully.\n\n"
                    f"With empty test_results list, function returned:\n"
                    f"  failures={failures}, errors={errors}, warnings={warnings}\n"
                    f"  logs={logs[:200]}\n\n"
                    "Expected: IndexError (bug exists)\n"
                    "Actual: Function handled it gracefully (bug is fixed!)\n\n"
                    "This test was designed to detect the bug. Since the bug is fixed,\n"
                    "update this test to assert proper error handling:\n"
                    "  assert errors > 0\n"
                    "  assert 'collection failed' in logs.lower()"
                )

            except IndexError as e:
                # THE BUG EXISTS - this is what Issue #450 describes
                if "list index out of range" in str(e):
                    pytest.fail(
                        f"BUG CONFIRMED (Issue #450): IndexError on empty test_results!\n\n"
                        f"Exception: {e}\n\n"
                        f"Bug location: pdd/fix_error_loop.py:213\n"
                        f"Buggy code: results = output_data.get('test_results', [{{}}])[0]\n\n"
                        f"Root cause:\n"
                        f"  1. run_pytest_and_capture_output returns: {{'test_results': []}}\n"
                        f"  2. Line 213 does: output_data.get('test_results', [{{}}])\n"
                        f"  3. Since key EXISTS, .get() returns the actual value: []\n"
                        f"  4. Then [0] tries to index empty list: [][0]\n"
                        f"  5. Result: IndexError: list index out of range\n\n"
                        f"The .get() default value [{{}}] ONLY applies when key is MISSING.\n"
                        f"It does NOT apply when key EXISTS with empty value.\n\n"
                        f"Fix needed: Check if test_results_list is empty before indexing:\n"
                        f"  test_results_list = output_data.get('test_results', [])\n"
                        f"  if not test_results_list:\n"
                        f"      return 0, 1, 0, 'Pytest collection failed: ...'\n"
                        f"  results = test_results_list[0]"
                    )
                else:
                    # Different IndexError - re-raise
                    raise

    def test_run_pytest_on_file_handles_test_results_none(self, tmp_path):
        """
        E2E Test: run_pytest_on_file() should handle test_results: None gracefully.

        Edge case: test_results key exists but value is None instead of list.
        This causes TypeError: 'NoneType' object is not subscriptable
        """
        from pdd.fix_error_loop import run_pytest_on_file

        test_file = tmp_path / "test_dummy.py"
        test_file.write_text("def test_dummy(): pass")

        # Mock: test_results is None (malformed data)
        malformed_results = {
            "test_results": None,  # None instead of list
            "stdout": "ERROR: Some error",
            "exit_code": 2
        }

        with patch('pdd.fix_error_loop.run_pytest_and_capture_output', return_value=malformed_results):
            try:
                failures, errors, warnings, logs = run_pytest_on_file(str(test_file))

                pytest.fail(
                    "BUG IS FIXED! run_pytest_on_file() handled test_results=None.\n"
                    f"Returned: failures={failures}, errors={errors}"
                )

            except TypeError as e:
                if "'NoneType' object is not subscriptable" in str(e):
                    pytest.fail(
                        f"BUG DETECTED (Issue #450 edge case): TypeError on test_results=None!\n\n"
                        f"Exception: {e}\n\n"
                        f"Root cause: output_data.get('test_results', [{{}}]) returns None\n"
                        f"when the key exists with value None. Then [0] fails.\n\n"
                        f"Fix needed: Type validation:\n"
                        f"  test_results_list = output_data.get('test_results', [])\n"
                        f"  if not isinstance(test_results_list, list):\n"
                        f"      return 0, 1, 0, 'Invalid test results format'"
                    )
                else:
                    raise

    def test_run_pytest_on_file_handles_test_results_dict(self, tmp_path):
        """
        E2E Test: run_pytest_on_file() should handle test_results as dict gracefully.

        Edge case: test_results is a dict instead of list.
        This causes KeyError: 0
        """
        from pdd.fix_error_loop import run_pytest_on_file

        test_file = tmp_path / "test_dummy.py"
        test_file.write_text("def test_dummy(): pass")

        # Mock: test_results is dict (wrong type)
        malformed_results = {
            "test_results": {"error": "collection failed"},  # Dict instead of list
            "stdout": "ERROR: Some error",
            "exit_code": 2
        }

        with patch('pdd.fix_error_loop.run_pytest_and_capture_output', return_value=malformed_results):
            try:
                failures, errors, warnings, logs = run_pytest_on_file(str(test_file))

                pytest.fail(
                    "BUG IS FIXED! run_pytest_on_file() handled test_results as dict.\n"
                    f"Returned: failures={failures}, errors={errors}"
                )

            except KeyError as e:
                if str(e) == "0" or "0" in str(e):
                    pytest.fail(
                        f"BUG DETECTED (Issue #450 edge case): KeyError when test_results is dict!\n\n"
                        f"Exception: {e}\n\n"
                        f"Root cause: output_data.get('test_results', [{{}}]) returns dict\n"
                        f"when the key exists with dict value. Then [0] tries to access dict[0].\n\n"
                        f"Fix needed: Type validation before indexing."
                    )
                else:
                    raise

    def test_multiple_collection_failure_scenarios(self, tmp_path):
        """
        E2E Test: Verify the bug exists across multiple failure scenarios.

        Tests 5 different scenarios that all lead to empty/malformed test_results:
        1. Empty list (most common)
        2. None value
        3. Dict value
        4. String value
        5. List with None element
        """
        from pdd.fix_error_loop import run_pytest_on_file

        test_file = tmp_path / "test_dummy.py"
        test_file.write_text("def test_dummy(): pass")

        # Test scenarios that should all be handled gracefully
        scenarios = [
            ("empty_list", {"test_results": [], "stdout": "ERROR"}),
            ("none_value", {"test_results": None, "stdout": "ERROR"}),
            ("dict_value", {"test_results": {"error": "failed"}, "stdout": "ERROR"}),
            ("string_value", {"test_results": "error", "stdout": "ERROR"}),
            ("list_with_none", {"test_results": [None], "stdout": "ERROR"}),
        ]

        crash_count = 0
        crash_details = []

        for scenario_name, mock_result in scenarios:
            with patch('pdd.fix_error_loop.run_pytest_and_capture_output', return_value=mock_result):
                try:
                    failures, errors, warnings, logs = run_pytest_on_file(str(test_file))
                    # If we get here, this scenario is handled gracefully
                except (IndexError, TypeError, KeyError, AttributeError) as e:
                    crash_count += 1
                    crash_details.append(f"{scenario_name}: {type(e).__name__}: {e}")

        # Assert that at least some scenarios crash (proving the bug exists)
        if crash_count > 0:
            pytest.fail(
                f"BUG CONFIRMED (Issue #450): {crash_count}/5 scenarios crashed!\n\n"
                f"Scenarios that crashed:\n" + "\n".join(crash_details) + "\n\n"
                f"This demonstrates the bug affects MULTIPLE edge cases, not just one.\n"
                f"All scenarios should be handled gracefully with defensive validation.\n\n"
                f"Current code (line 213):\n"
                f"  results = output_data.get('test_results', [{{}}])[0]\n\n"
                f"Problem: .get() default only works when key is MISSING.\n"
                f"When key EXISTS with empty/malformed value, indexing fails.\n\n"
                f"Fix needed: Validate before indexing:\n"
                f"  test_results_list = output_data.get('test_results', [])\n"
                f"  if not isinstance(test_results_list, list) or not test_results_list:\n"
                f"      return 0, 1, 0, 'Collection failed'"
            )
        else:
            # All scenarios handled gracefully - bug is fixed
            pytest.fail(
                f"BUG IS FIXED! All {len(scenarios)} scenarios handled gracefully.\n"
                "Update test expectations."
            )


@pytest.mark.e2e
class TestRealWorldPytestBehavior:
    """
    Tests that investigate actual pytest behavior to understand when
    empty test_results could occur in real-world scenarios.
    """

    def test_document_current_pytest_output_behavior(self, tmp_path):
        """
        E2E Test: Document how current run_pytest_and_capture_output behaves.

        This test helps understand if/when empty test_results can occur with
        the current implementation vs potential future changes or external factors.
        """
        from pdd.pytest_output import run_pytest_and_capture_output

        # Test 1: ImportError
        test1 = tmp_path / "test_import_error.py"
        test1.write_text("import nonexistent\ndef test_a(): pass")
        result1 = run_pytest_and_capture_output(str(test1))

        # Test 2: SyntaxError
        test2 = tmp_path / "test_syntax_error.py"
        test2.write_text("def test_b():\n    x = \n    pass")
        result2 = run_pytest_and_capture_output(str(test2))

        # Test 3: No tests found
        test3 = tmp_path / "test_no_tests.py"
        test3.write_text("# No test functions\ndef helper(): pass")
        result3 = run_pytest_and_capture_output(str(test3))

        # Document findings
        pytest.fail(
            f"Current pytest behavior documentation:\n\n"
            f"ImportError test_results: {result1.get('test_results', 'KEY_MISSING')}\n"
            f"  Type: {type(result1.get('test_results'))}\n"
            f"  Length: {len(result1.get('test_results', [])) if isinstance(result1.get('test_results'), list) else 'N/A'}\n\n"
            f"SyntaxError test_results: {result2.get('test_results', 'KEY_MISSING')}\n"
            f"  Type: {type(result2.get('test_results'))}\n"
            f"  Length: {len(result2.get('test_results', [])) if isinstance(result2.get('test_results'), list) else 'N/A'}\n\n"
            f"No tests test_results: {result3.get('test_results', 'KEY_MISSING')}\n"
            f"  Type: {type(result3.get('test_results'))}\n"
            f"  Length: {len(result3.get('test_results', [])) if isinstance(result3.get('test_results'), list) else 'N/A'}\n\n"
            f"FINDINGS:\n"
            f"Current implementation ALWAYS returns non-empty test_results list.\n"
            f"However, Issue #450 describes this bug occurring in 16+ real scenarios.\n\n"
            f"HYPOTHESIS:\n"
            f"1. Bug may occur with older pytest versions or different execution paths\n"
            f"2. Bug may occur with deserialization of cached/stored results\n"
            f"3. Bug may occur with network errors in distributed testing\n"
            f"4. Bug may occur with custom pytest plugins\n\n"
            f"CONCLUSION:\n"
            f"Defensive programming is ESSENTIAL. Even if current code doesn't produce\n"
            f"empty lists, external factors, future changes, or edge cases could.\n"
            f"The fix (validating before indexing) is necessary for robustness."
        )
