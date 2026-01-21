"""
E2E Test for Issue #2: divide_numbers crashes on division by zero

This test exercises the full user-facing code path for the math_helper module,
verifying that the division by zero bug is properly handled.

The bug: When importing pdd.math_helper and calling divide_numbers(x, 0),
the function raises ZeroDivisionError instead of handling it gracefully with
a ValueError and clear error message.

This E2E test:
1. Imports the pdd.math_helper module as a real user would
2. Calls divide_numbers with zero denominator
3. Verifies that ValueError (not ZeroDivisionError) is raised
4. Verifies the error message is clear and helpful

The test should FAIL on buggy code (raises ZeroDivisionError) and
PASS once the fix is applied (raises ValueError with clear message).
"""

import pytest


@pytest.mark.e2e
class TestDivideByZeroE2E:
    """
    E2E tests for Issue #2: Verify divide_numbers handles division by zero gracefully.

    These tests verify the full user-facing behavior from import to function call,
    ensuring that division by zero is handled in a user-friendly way.
    """

    def test_divide_by_zero_raises_value_error_not_zero_division_error(self):
        """
        E2E Test: Import pdd.math_helper -> call divide_numbers(x, 0) -> ValueError

        This test simulates the exact user experience described in Issue #2:
        A user imports the module and calls divide_numbers with zero as denominator.

        Expected behavior (after fix):
        - Function raises ValueError (not ZeroDivisionError)
        - Error message clearly states "Cannot divide by zero"

        Bug behavior (Issue #2):
        - Function raises ZeroDivisionError
        - Generic Python error message, not user-friendly
        """
        # Import the module exactly as a user would
        from pdd.math_helper import divide_numbers

        # Attempt to divide by zero - this should raise ValueError, not ZeroDivisionError
        with pytest.raises(ValueError) as exc_info:
            divide_numbers(10, 0)

        # Verify the error message is clear and helpful
        assert "Cannot divide by zero" in str(exc_info.value), (
            f"Expected error message to contain 'Cannot divide by zero', "
            f"but got: {str(exc_info.value)}"
        )

    def test_divide_by_float_zero_raises_value_error(self):
        """
        E2E Test: Verify division by float zero (0.0) also raises ValueError.

        This ensures the fix handles both integer zero and float zero correctly.
        """
        from pdd.math_helper import divide_numbers

        # Test with float zero
        with pytest.raises(ValueError) as exc_info:
            divide_numbers(5.5, 0.0)

        # Verify the error message
        assert "Cannot divide by zero" in str(exc_info.value)

    def test_valid_division_still_works_after_fix(self):
        """
        E2E Test: Verify normal division operations continue to work correctly.

        This is a regression test to ensure the fix doesn't break valid division.
        """
        from pdd.math_helper import divide_numbers

        # Test various valid division operations
        assert divide_numbers(10, 2) == 5.0
        assert divide_numbers(7, 2) == 3.5
        assert divide_numbers(-10, 2) == -5.0
        assert divide_numbers(10, -2) == -5.0
        assert divide_numbers(0, 5) == 0.0

    def test_full_module_import_path(self):
        """
        E2E Test: Verify the bug is caught when using full module import path.

        This tests the alternate import style: import pdd.math_helper
        """
        import pdd.math_helper

        # Should raise ValueError for division by zero
        with pytest.raises(ValueError) as exc_info:
            pdd.math_helper.divide_numbers(100, 0)

        assert "Cannot divide by zero" in str(exc_info.value)

    def test_other_math_functions_unaffected(self):
        """
        E2E Test: Verify other functions in math_helper remain unaffected.

        This ensures the fix is targeted and doesn't introduce side effects.
        """
        from pdd.math_helper import add_numbers, multiply_numbers

        # Verify add_numbers still works
        assert add_numbers(5, 3) == 8
        assert add_numbers(-2, 7) == 5

        # Verify multiply_numbers still works
        assert multiply_numbers(4, 3) == 12
        assert multiply_numbers(-2, 5) == -10
