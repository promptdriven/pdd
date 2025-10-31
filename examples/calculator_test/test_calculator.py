import pytest

import calculator


# 1. Tests for the `add` function
def test_add_positive_integers():
    """Test Case 1.1: Verify addition of two positive integers."""
    assert calculator.add(5, 3) == 8


def test_add_negative_integers():
    """Test Case 1.2: Verify addition of two negative integers."""
    assert calculator.add(-5, -3) == -8


def test_add_positive_and_negative_integer() -> None:
    """Test Case 1.3: Verify addition of a positive and a negative integer."""
    assert calculator.add(10, -5) == 5


def test_add_with_zero() -> None:
    """Test Case 1.4: Verify that adding zero to a number does not change it."""
    assert calculator.add(7, 0) == 7
    assert calculator.add(0, -5) == -5


def test_add_floating_point_numbers() -> None:
    """Test Case 1.5: Verify addition of two floating-point numbers."""
    assert calculator.add(2.5, 3.5) == 6.0


def test_add_with_type_mismatch_raises_error() -> None:
    """Test Case 1.6: Verify that adding incompatible types raises a TypeError."""
    with pytest.raises(TypeError):
        calculator.add(10, "5")


# 2. Tests for the `subtract` function

def test_subtract_positive_integers() -> None:
    """Test Case 2.1: Verify subtraction of two positive integers."""
    assert calculator.subtract(10, 4) == 6


def test_subtract_to_get_negative_result() -> None:
    """Test Case 2.2: Verify subtraction of a larger number from a smaller one."""
    assert calculator.subtract(4, 10) == -6


def test_subtract_negative_integers() -> None:
    """Test Case 2.3: Verify subtraction of two negative integers."""
    assert calculator.subtract(-5, -2) == -3


def test_subtract_negative_from_positive() -> None:
    """Test Case 2.4: Verify subtraction of a negative number from a positive one."""
    assert calculator.subtract(10, -3) == 13


def test_subtract_with_zero() -> None:
    """Test Case 2.5: Verify subtraction involving zero."""
    assert calculator.subtract(5, 0) == 5
    assert calculator.subtract(0, 5) == -5


def test_subtract_floating_point_numbers() -> None:
    """Test Case 2.6: Verify subtraction of two floating-point numbers."""
    # Use pytest.approx for floating-point comparisons to handle potential precision issues
    assert calculator.subtract(5.5, 2.1) == pytest.approx(3.4)


def test_subtract_with_type_mismatch_raises_error() -> None:
    """Test Case 2.7: Verify that subtracting incompatible types raises a TypeError."""
    with pytest.raises(TypeError):
        calculator.subtract(10, "4")
