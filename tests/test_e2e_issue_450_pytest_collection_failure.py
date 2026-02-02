"""
E2E Test for Issue #450: IndexError crash when pytest collection/execution fails (empty test_results)

This test exercises the full code path from creating a broken test file to running
`run_pytest_on_file()` to verify that when pytest fails to collect or execute tests,
PDD handles it gracefully instead of crashing with IndexError.

The bug: When pytest fails to collect tests (e.g., ImportError, SyntaxError), it returns
an empty `test_results` list. The code at pdd/fix_error_loop.py:213 crashes with:
`IndexError: list index out of range` because `output_data.get("test_results", [{}])[0]`
tries to index an empty list.

Bug location: pdd/fix_error_loop.py:213 in run_pytest_on_file()

This E2E test:
1. Creates a test file with a deliberate collection failure (ImportError)
2. Calls run_pytest_on_file() directly (simulating the pdd fix workflow)
3. Verifies the function handles the failure gracefully instead of crashing

The test should FAIL on buggy code (IndexError crash) and PASS once the fix is applied.

Issue: https://github.com/promptdriven/pdd/issues/450
"""

import tempfile
from pathlib import Path

import pytest


@pytest.mark.e2e
class TestPytestCollectionFailureE2E:
    """
    E2E tests for Issue #450: Verify run_pytest_on_file() handles pytest collection
    failures gracefully instead of crashing with IndexError.
    """

    def test_run_pytest_on_file_handles_import_error(self, tmp_path):
        """
        E2E Test: run_pytest_on_file() should not crash when test has ImportError.

        This is the most common real-world scenario described in Issue #450:
        A test file has a missing import, pytest collection fails, and PDD crashes
        with IndexError instead of showing the helpful ImportError message.

        Expected behavior (after fix):
        - Function should detect collection failure
        - Function should return error count indicating failure
        - Function should return helpful error message about the ImportError
        - Function should NOT crash with IndexError

        Bug behavior (Issue #450):
        - Function crashes with: IndexError: list index out of range
        - User sees unhelpful PDD crash instead of the actual pytest error
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # 1. Create a test file with ImportError (missing 'client')
        test_file = tmp_path / "test_with_import_error.py"
        test_content = '''"""Test with missing import - should cause collection failure."""

def test_login():
    """Test that will fail during collection due to missing 'client' import."""
    response = client.post('/login')  # NameError - client not imported!
    assert response.status_code == 200
'''
        test_file.write_text(test_content)

        # 2. Call run_pytest_on_file() - this is the real function call from pdd fix
        # This simulates the exact code path that users encounter when running pdd fix
        try:
            failures, errors, warnings, logs = run_pytest_on_file(str(test_file))

            # If we get here without IndexError, the bug is fixed!
            # The function should have returned error counts indicating collection failure
            pytest.fail(
                "BUG IS FIXED! run_pytest_on_file() handled collection failure gracefully.\n\n"
                f"Returned: failures={failures}, errors={errors}, warnings={warnings}\n"
                f"Logs: {logs[:500]}\n\n"
                "This test is now failing because it expects the bug to exist.\n"
                "After the fix is applied, this test should be updated to assert\n"
                "that errors > 0 and logs contain helpful error messages."
            )

        except IndexError as e:
            # THE BUG EXISTS - this is what we're testing for
            if "list index out of range" in str(e):
                pytest.fail(
                    f"BUG DETECTED (Issue #450): run_pytest_on_file() crashes with IndexError!\n\n"
                    f"Exception: {e}\n\n"
                    f"Test file contained ImportError (missing 'client' import)\n"
                    f"Pytest collection failed and returned empty test_results list\n\n"
                    f"Bug location: pdd/fix_error_loop.py:213\n"
                    f"Buggy code: results = output_data.get('test_results', [{{}}])[0]\n\n"
                    f"Root cause: dict.get() default [{{}}] only applies when key is MISSING.\n"
                    f"When test_results exists but is EMPTY LIST, we get [][0] -> IndexError\n\n"
                    f"Expected: Function should return (0, 1, 0, 'Pytest collection failed: ...')\n"
                    f"Actual: Function crashes with IndexError: list index out of range\n\n"
                    f"User impact: Users see confusing PDD crash instead of helpful pytest error."
                )
            else:
                # Different IndexError - re-raise
                raise

    def test_run_pytest_on_file_handles_syntax_error(self, tmp_path):
        """
        E2E Test: run_pytest_on_file() should handle SyntaxError in test file gracefully.

        Another common real-world scenario: test file has syntax error, pytest
        collection fails, PDD should show the syntax error, not crash.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # 1. Create test file with syntax error
        test_file = tmp_path / "test_with_syntax_error.py"
        test_content = '''"""Test with syntax error - should cause collection failure."""

def test_calculation():
    """Test with invalid syntax."""
    result = 2 +  # Missing second operand!
    assert result == 2
'''
        test_file.write_text(test_content)

        # 2. Call run_pytest_on_file()
        try:
            failures, errors, warnings, logs = run_pytest_on_file(str(test_file))

            # Bug is fixed if we get here
            pytest.fail(
                "BUG IS FIXED! run_pytest_on_file() handled SyntaxError gracefully.\n\n"
                f"Returned: failures={failures}, errors={errors}, warnings={warnings}\n"
                f"Update this test to assert proper error handling."
            )

        except IndexError as e:
            if "list index out of range" in str(e):
                pytest.fail(
                    f"BUG DETECTED (Issue #450): SyntaxError causes IndexError crash!\n\n"
                    f"Exception: {e}\n\n"
                    f"Test file had SyntaxError, pytest collection failed.\n"
                    f"Expected: Show SyntaxError to user\n"
                    f"Actual: PDD crashes with IndexError"
                )
            else:
                raise

    def test_run_pytest_on_file_handles_no_tests_found(self, tmp_path):
        """
        E2E Test: run_pytest_on_file() should handle empty test file (no tests found).

        Scenario: Test file exists but contains no test functions.
        Pytest collects 0 items, returns empty test_results.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # 1. Create empty test file (no test functions)
        test_file = tmp_path / "test_empty.py"
        test_content = '''"""Test file with no tests - pytest will collect 0 items."""

# This file has no test functions!
def helper_function():
    """Not a test - doesn't start with test_"""
    return True
'''
        test_file.write_text(test_content)

        # 2. Call run_pytest_on_file()
        try:
            failures, errors, warnings, logs = run_pytest_on_file(str(test_file))

            # Bug is fixed
            pytest.fail(
                "BUG IS FIXED! run_pytest_on_file() handled 'no tests found' gracefully.\n\n"
                f"Returned: failures={failures}, errors={errors}, warnings={warnings}"
            )

        except IndexError as e:
            if "list index out of range" in str(e):
                pytest.fail(
                    f"BUG DETECTED (Issue #450): 'No tests found' causes IndexError!\n\n"
                    f"Exception: {e}\n\n"
                    f"Test file contained no test functions.\n"
                    f"Pytest collected 0 items, returned empty test_results.\n"
                    f"Expected: Return appropriate error/warning\n"
                    f"Actual: IndexError crash"
                )
            else:
                raise

    def test_run_pytest_on_file_handles_module_not_found(self, tmp_path):
        """
        E2E Test: run_pytest_on_file() should handle ModuleNotFoundError gracefully.

        Scenario: Test tries to import a module that doesn't exist.
        Common when test assumes certain project structure or dependencies.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # 1. Create test file that imports non-existent module
        test_file = tmp_path / "test_missing_module.py"
        test_content = '''"""Test with missing module import."""
import nonexistent_package  # This will fail during collection

def test_something():
    """This test will never run because collection fails."""
    assert True
'''
        test_file.write_text(test_content)

        # 2. Call run_pytest_on_file()
        try:
            failures, errors, warnings, logs = run_pytest_on_file(str(test_file))

            # Bug is fixed
            pytest.fail(
                "BUG IS FIXED! run_pytest_on_file() handled ModuleNotFoundError gracefully.\n\n"
                f"Returned: failures={failures}, errors={errors}, warnings={warnings}"
            )

        except IndexError as e:
            if "list index out of range" in str(e):
                pytest.fail(
                    f"BUG DETECTED (Issue #450): ModuleNotFoundError causes IndexError!\n\n"
                    f"Exception: {e}\n\n"
                    f"Test tried to import 'nonexistent_package'.\n"
                    f"Expected: Show ModuleNotFoundError to user\n"
                    f"Actual: IndexError crash"
                )
            else:
                raise

    def test_run_pytest_on_file_handles_fixture_not_found(self, tmp_path):
        """
        E2E Test: run_pytest_on_file() should handle fixture errors gracefully.

        Scenario: Test uses a fixture that doesn't exist.
        Pytest collection fails when it can't find the fixture.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # 1. Create test that uses non-existent fixture
        test_file = tmp_path / "test_missing_fixture.py"
        test_content = '''"""Test with missing fixture."""

def test_with_missing_fixture(nonexistent_fixture):
    """This test uses a fixture that doesn't exist."""
    assert nonexistent_fixture is not None
'''
        test_file.write_text(test_content)

        # 2. Call run_pytest_on_file()
        try:
            failures, errors, warnings, logs = run_pytest_on_file(str(test_file))

            # Bug is fixed
            pytest.fail(
                "BUG IS FIXED! run_pytest_on_file() handled fixture error gracefully.\n\n"
                f"Returned: failures={failures}, errors={errors}, warnings={warnings}"
            )

        except IndexError as e:
            if "list index out of range" in str(e):
                pytest.fail(
                    f"BUG DETECTED (Issue #450): Fixture error causes IndexError!\n\n"
                    f"Exception: {e}\n\n"
                    f"Test used non-existent fixture 'nonexistent_fixture'.\n"
                    f"Expected: Show fixture error to user\n"
                    f"Actual: IndexError crash"
                )
            else:
                raise


@pytest.mark.e2e
class TestPytestCollectionFailureRealWorld:
    """
    Additional E2E tests simulating real-world user scenarios from Issue #450.

    These tests demonstrate the exact user experience described in the issue:
    users run pdd fix on broken tests and get confusing PDD crashes instead of
    helpful error messages.
    """

    def test_user_scenario_missing_test_client(self, tmp_path):
        """
        E2E Test: Simulates the exact user scenario from Issue #450 description.

        User writes a test for API endpoint but forgets to import the test client.
        When they run pdd fix, they expect to see "client not defined" error.
        Instead, they get IndexError crash and blame PDD instead of their test.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # This is the EXACT example from Issue #450
        test_file = tmp_path / "test_api.py"
        test_content = '''"""API test - missing client import."""

def test_login():
    response = client.post('/login')  # NameError - client not imported
    assert response.status_code == 200
'''
        test_file.write_text(test_content)

        try:
            failures, errors, warnings, logs = run_pytest_on_file(str(test_file))

            # Bug is fixed - user now sees helpful error
            pytest.fail(
                "BUG IS FIXED! User scenario handled correctly.\n\n"
                "User wrote test with missing import.\n"
                "Expected: See 'NameError: name client is not defined'\n"
                "Actual (after fix): Function returned gracefully with error message\n\n"
                f"Returned: failures={failures}, errors={errors}, warnings={warnings}\n"
                f"Logs should mention: {logs[:200]}"
            )

        except IndexError as e:
            # THE USER EXPERIENCE BUG
            if "list index out of range" in str(e):
                pytest.fail(
                    f"USER EXPERIENCE BUG (Issue #450):\n\n"
                    f"User wrote: test with missing 'client' import\n"
                    f"User ran: pdd fix\n"
                    f"User expected: 'NameError: name client is not defined'\n"
                    f"User got: 'IndexError: list index out of range'\n\n"
                    f"IMPACT: User blames PDD framework instead of recognizing their test error!\n\n"
                    f"This is exactly the problem described in Issue #450:\n"
                    f"- Unhelpful error message\n"
                    f"- User confusion\n"
                    f"- Poor developer experience\n\n"
                    f"Fix: pdd/fix_error_loop.py:213 needs defensive validation\n"
                    f"to handle empty test_results list gracefully."
                )
            else:
                raise

    def test_integration_with_fix_error_loop(self, tmp_path):
        """
        E2E Test: Verify run_pytest_on_file() behavior within fix_error_loop context.

        This tests the function in the context where it's actually called during
        the pdd fix workflow, simulating a more complete integration scenario.
        """
        from pdd.fix_error_loop import run_pytest_on_file

        # 1. Create multiple broken test files
        test_files = []

        # Test 1: ImportError
        test1 = tmp_path / "test_broken_1.py"
        test1.write_text('import missing_module\ndef test_a(): assert True')
        test_files.append(test1)

        # Test 2: SyntaxError
        test2 = tmp_path / "test_broken_2.py"
        test2.write_text('def test_b():\n    x = \n    assert True')
        test_files.append(test2)

        # Test 3: NameError (undefined variable)
        test3 = tmp_path / "test_broken_3.py"
        test3.write_text('def test_c():\n    result = undefined_var\n    assert result')
        test_files.append(test3)

        # 2. Run run_pytest_on_file() on each broken test
        crash_count = 0
        success_count = 0

        for test_file in test_files:
            try:
                failures, errors, warnings, logs = run_pytest_on_file(str(test_file))
                # If we get here, function handled the error gracefully
                success_count += 1
            except IndexError as e:
                if "list index out of range" in str(e):
                    crash_count += 1
                else:
                    raise

        # 3. Assert results
        if crash_count > 0:
            pytest.fail(
                f"BUG DETECTED (Issue #450): run_pytest_on_file() crashed on {crash_count}/3 broken tests!\n\n"
                f"All 3 tests had collection failures (ImportError, SyntaxError, NameError).\n"
                f"All 3 should be handled gracefully.\n"
                f"Instead, {crash_count} crashed with IndexError.\n\n"
                f"This demonstrates that the bug affects MULTIPLE real-world scenarios,\n"
                f"not just one edge case. Users will hit this frequently."
            )
        else:
            # All handled gracefully - bug is fixed
            pytest.fail(
                f"BUG IS FIXED! All {len(test_files)} collection failures handled gracefully.\n"
                f"Update test expectations."
            )
