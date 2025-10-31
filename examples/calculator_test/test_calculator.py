import pytest

import calculator


def test_add():
    assert calculator.add(0, 0) == 0


def test_add_positive_numbers():
    """
    Tests the add function with two positive integers.
    This test will fail with the buggy implementation because add(5, 3)
    incorrectly returns 2 instead of the expected 8.
    """
    # Arrange: Define inputs and the expected correct output
    num1 = 5
    num2 = 3
    expected_sum = 8

    # Act: Call the function under test
    actual_sum = calculator.add(num1, num2)

    # Assert: Compare the actual output with the expected output
    assert actual_sum == expected_sum, f"Expected the sum of {num1} and {num2} to be {expected_sum}, but got {actual_sum}"


@pytest.mark.parametrize("num1, num2, expected", [
    (-1, 1, 0),      # Test with negative and positive numbers
    (-5, -5, -10),   # Test with two negative numbers
    (100, 0, 100),   # Test with zero
    (0, 0, 0)        # Test with two zeros
])
def test_add_various_scenarios(num1, num2, expected):
    """
    Tests the add function with a variety of number combinations for robustness.
    """
    assert calculator.add(num1, num2) == expected


def test_subtract_positive_numbers():
    """
    Tests the subtract function to ensure it works as expected.
    This test should pass with the current implementation.
    """
    # Arrange
    num1 = 10
    num2 = 4
    expected_difference = 6

    # Act
    actual_difference = calculator.subtract(num1, num2)

    # Assert
    assert actual_difference == expected_difference, f"Expected the difference of {num1} and {num2} to be {expected_difference}, but got {actual_difference}"


@pytest.mark.parametrize("num1, num2, expected", [
    (5, 10, -5),     # Test where the result is negative
    (-5, -5, 0),     # Test subtracting two identical negative numbers
    (10, -2, 12)     # Test subtracting a negative number
])
def test_subtract_various_scenarios(num1, num2, expected):
    """
    Tests the subtract function with a variety of number combinations.
    """
    assert calculator.subtract(num1, num2) == expected
