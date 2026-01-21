"""Tests for math_helper module."""

import pytest
from pdd.math_helper import divide_numbers, add_numbers, multiply_numbers


class TestDivideNumbers:
    """Tests for the divide_numbers function."""

    def test_divide_by_zero_integer(self):
        """
        BUG DETECTION: divide_numbers should raise ValueError for division by zero.

        This test should FAIL on the buggy code (which raises ZeroDivisionError)
        and PASS after the fix (which should raise ValueError with a clear message).
        """
        with pytest.raises(ValueError, match="Cannot divide by zero"):
            divide_numbers(10, 0)

    def test_divide_by_zero_float(self):
        """
        BUG DETECTION: divide_numbers should handle float zero denominators.

        This test should FAIL on the buggy code (which raises ZeroDivisionError)
        and PASS after the fix (which should raise ValueError).
        """
        with pytest.raises(ValueError, match="Cannot divide by zero"):
            divide_numbers(5.5, 0.0)

    def test_divide_positive_integers(self):
        """Regression test: division of positive integers should work correctly."""
        result = divide_numbers(10, 2)
        assert result == 5.0

    def test_divide_negative_numbers(self):
        """Regression test: division with negative numbers should work correctly."""
        result = divide_numbers(-10, 2)
        assert result == -5.0

    def test_divide_floats(self):
        """Regression test: division of floats should work correctly."""
        result = divide_numbers(7.5, 2.5)
        assert result == 3.0


class TestAddNumbers:
    """Tests for the add_numbers function."""

    def test_add_positive_integers(self):
        """Test addition of positive integers."""
        assert add_numbers(2, 3) == 5

    def test_add_negative_numbers(self):
        """Test addition of negative numbers."""
        assert add_numbers(-2, -3) == -5


class TestMultiplyNumbers:
    """Tests for the multiply_numbers function."""

    def test_multiply_positive_integers(self):
        """Test multiplication of positive integers."""
        assert multiply_numbers(3, 4) == 12

    def test_multiply_by_zero(self):
        """Test multiplication by zero."""
        assert multiply_numbers(5, 0) == 0
