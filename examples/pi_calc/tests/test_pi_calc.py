# test_pi_calc.py

import pytest
import math
from pi_calc import pi_calc

# ############################################################################
# Test Plan
# ############################################################################
#
# The goal is to test the `pi_calc` function, which calculates an approximation
# of Pi using the Nilakantha series.
#
# ----------------------------------------------------------------------------
# I. Formal Verification (Z3) vs. Unit Tests Analysis
# ----------------------------------------------------------------------------
#
# The `pi_calc` function involves a loop, floating-point arithmetic, and specific
# input validation checks.
#
# - **Z3 (Formal Verification):**
#   - **Applicability:** Z3 is powerful for proving properties over integers and
#     logic. However, modeling iterative floating-point calculations is complex
#     and often leads to issues with precision and performance. Proving a
#     property like "the function's output converges towards Pi as n_terms
#     increases" is a mathematical proof of the series itself, not something
#     easily verifiable by an SMT solver for a given implementation.
#   - **Conclusion:** The core logic is numerical and approximative, which is not
#     the primary strength of Z3. The input validation (type and value checks)
#     is discrete and simple. Therefore, using Z3 would be overly complex for
#     the benefits gained.
#
# - **Unit Tests (Pytest):**
#   - **Applicability:** Pytest is ideal for this scenario. It can easily handle:
#     1.  **Input Validation:** `pytest.raises` can confirm that `TypeError` and
#         `ValueError` are thrown for invalid inputs.
#     2.  **Edge Cases:** Testing specific values like `n_terms = 0` is
#         straightforward.
#     3.  **Correctness:** For a small number of terms, the expected result can
#         be calculated manually and asserted.
#     4.  **Approximation:** `pytest.approx` is designed to compare floating-point
#         numbers within a tolerance, perfect for checking if the result is
#         close to `math.pi` for a large number of terms.
#     5.  **Behavioral Properties:** We can write a test to verify the convergence
#         property (i.e., more terms lead to a smaller error).
#   - **Conclusion:** Pytest provides a practical, robust, and readable way to
#     ensure the function's correctness and adherence to its specification.
#
# ----------------------------------------------------------------------------
# II. Detailed Test Plan (using Pytest)
# ----------------------------------------------------------------------------
#
# 1.  **Test Input Validation:**
#     - `test_negative_input_raises_value_error`: Ensure `pi_calc(-1)` raises a `ValueError`.
#     - `test_non_integer_input_raises_type_error`: Ensure non-integer inputs (e.g., float, string, list) raise a `TypeError`. This will be parameterized to cover multiple invalid types.
#
# 2.  **Test Edge Cases:**
#     - `test_zero_terms`: Ensure `pi_calc(0)` returns the base value of `3.0`, as the series loop should not execute.
#
# 3.  **Test Correctness for Small, Verifiable Inputs:**
#     - `test_one_term`: Manually calculate the result for `n_terms = 1` and assert the function's output matches. Expected: `3 + 4/(2*3*4)`.
#     - `test_two_terms`: Manually calculate the result for `n_terms = 2` and assert the output matches. Expected: `3 + 4/(2*3*4) - 4/(4*5*6)`.
#
# 4.  **Test Approximation Quality:**
#     - `test_default_terms_approximation`: Call `pi_calc()` with no arguments to use the default `n_terms`. Assert that the result is a close approximation of `math.pi` using `pytest.approx`.
#     - `test_large_number_of_terms_approximation`: Call `pi_calc` with a very large number of terms (e.g., 200,000) and assert the result is a close approximation of `math.pi`.
#
# 5.  **Test Functional Properties:**
#     - `test_convergence`: Verify that the approximation error decreases as `n_terms` increases. This will be done by comparing the absolute error `|result - math.pi|` for a small, medium, and large number of terms.
#
# ############################################################################


def test_negative_input_raises_value_error():
    """
    Tests that a negative integer for n_terms raises a ValueError.
    """
    with pytest.raises(ValueError, match="The number of terms cannot be negative."):
        pi_calc(n_terms=-10)


@pytest.mark.parametrize("invalid_input, input_type", [
    (10.5, "float"),
    ("100", "string"),
    ([100], "list"),
    ({100}, "set"),
    (None, "NoneType")
])
def test_non_integer_input_raises_type_error(invalid_input, input_type):
    """
    Tests that non-integer inputs for n_terms raise a TypeError.
    This test is parameterized to check various invalid types.
    """
    with pytest.raises(TypeError, match="The number of terms must be an integer."):
        pi_calc(n_terms=invalid_input)


def test_zero_terms():
    """
    Tests the base case where n_terms is 0. The result should be exactly 3.0.
    """
    # With 0 terms, the loop should not run, returning the initial value.
    assert pi_calc(n_terms=0) == 3.0


def test_one_term():
    """
    Tests the calculation with a single term from the series.
    """
    # Expected: 3 + 4/(2*3*4) = 3 + 4/24 = 3 + 1/6
    expected_value = 3.0 + (4.0 / (2.0 * 3.0 * 4.0))
    assert pi_calc(n_terms=1) == pytest.approx(expected_value)


def test_two_terms():
    """
    Tests the calculation with two terms from the series.
    """
    # Expected: 3 + 4/(2*3*4) - 4/(4*5*6)
    term1 = 4.0 / (2.0 * 3.0 * 4.0)
    term2 = -4.0 / (4.0 * 5.0 * 6.0)
    expected_value = 3.0 + term1 + term2
    assert pi_calc(n_terms=2) == pytest.approx(expected_value)


def test_default_terms_approximation():
    """
    Tests that the default number of terms (100,000) provides a good
    approximation of math.pi.
    """
    # The default tolerance of pytest.approx is sufficient here.
    assert pi_calc() == pytest.approx(math.pi)


def test_large_number_of_terms_approximation():
    """
    Tests that a very large number of terms provides an even better
    approximation of math.pi.
    """
    # Using a large number of terms should result in a very close approximation.
    assert pi_calc(n_terms=200000) == pytest.approx(math.pi)


def test_convergence():
    """
    Tests that the approximation error decreases as n_terms increases.
    """
    # Calculate the absolute error for different numbers of terms
    error_10 = abs(pi_calc(n_terms=10) - math.pi)
    error_100 = abs(pi_calc(n_terms=100) - math.pi)
    error_1000 = abs(pi_calc(n_terms=1000) - math.pi)

    # Assert that the error for more terms is smaller than for fewer terms
    assert error_100 < error_10
    assert error_1000 < error_100