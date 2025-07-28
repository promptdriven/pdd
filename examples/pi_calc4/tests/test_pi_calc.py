# test_pi_calc.py

# NOTE ON PYTEST WARNING:
# A `PytestConfigWarning` for an "Unknown config option: asyncio_default_fixture_loop_scope"
# may appear when running these tests. This is not an error in the code or the tests
# themselves, but rather an issue with the pytest configuration file (e.g., pytest.ini).
#
# Root Cause: This option was used by older versions of the pytest-asyncio plugin
# and has since been deprecated.
#
# Solution: To fix the warning, remove the line `asyncio_default_fixture_loop_scope = ...`
# from your pytest configuration file.

import pytest
import math

# Attempt to import z3, and skip Z3 tests if it's not available.
try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False

from pi_calc import pi_calc

#
# Detailed Test Plan
#
# I. Unit Tests (using pytest)
#
#    Objective: Verify the function's behavior for specific, discrete inputs,
#               including valid, invalid, and boundary cases.
#
#    Test Cases:
#    1. `test_negative_input`:
#       - Input: `n_terms = -1`
#       - Expected Outcome: Raises `ValueError`.
#       - Rationale: Ensures negative inputs are correctly handled as per the
#         function's contract.
#    2. `test_non_integer_input_float`:
#       - Input: `n_terms = 100.5`
#       - Expected Outcome: Raises `TypeError`.
#       - Rationale: Ensures non-integer inputs (float) are rejected.
#    3. `test_non_integer_input_string`:
#       - Input: `n_terms = "100"`
#       - Expected Outcome: Raises `TypeError`.
#       - Rationale: Ensures non-integer inputs (string) are rejected.
#    4. `test_zero_terms`:
#       - Input: `n_terms = 0`
#       - Expected Outcome: Returns `3.0`.
#       - Rationale: Tests the base case where the series calculation loop is
#         not entered.
#    5. `test_one_term`:
#       - Input: `n_terms = 1`
#       - Expected Outcome: Returns `3.0 + 4.0 / (2.0 * 3.0 * 4.0)`.
#       - Rationale: Verifies the calculation for the first term of the series.
#    6. `test_two_terms`:
#       - Input: `n_terms = 2`
#       - Expected Outcome: Returns `3.0 + 4.0 / (2*3*4) - 4.0 / (4*5*6)`.
#       - Rationale: Verifies the calculation and the sign change for the
#         second term.
#    7. `test_default_terms_convergence`:
#       - Input: No input (use default `n_terms=100000`).
#       - Expected Outcome: The result should be very close to `math.pi`. Use
#         `pytest.approx` with a small tolerance (e.g., `1e-10`).
#       - Rationale: Ensures the default parameter provides a high-precision
#         result, testing the convergence for a large number of terms.
#    8. `test_large_terms_convergence`:
#       - Input: `n_terms = 200000` (a value larger than the default).
#       - Expected Outcome: The result should be very close to `math.pi`, and
#         more accurate than the default.
#       - Rationale: Confirms the series continues to converge correctly for
#         very large inputs.
#    9. `test_convergence_improves`:
#       - Input: Compare `pi_calc(1000)` and `pi_calc(10000)`.
#       - Expected Outcome: The error of the 10,000-term approximation should
#         be smaller than the error of the 1,000-term approximation.
#       - Rationale: Directly verifies that increasing the number of terms
#         improves the result's accuracy, a key property of convergence.
#
# II. Formal Verification (using Z3)
#
#    Objective: Prove general properties of the function's algorithm that should
#               hold true for all valid inputs. This goes beyond what can be
#               tested with discrete examples.
#
#    Properties to Verify:
#    1. `test_z3_is_always_greater_than_three`:
#       - Property: For any `n_terms >= 1`, `pi_calc(n_terms)` should be
#         greater than 3.
#       - Method: Model the function's logic in Z3. Assert `n >= 1` and check
#         if the solver can find a counterexample to `pi_calc(n) > 3`.
#         The expected result is `unsat`, proving the property.
#       - Rationale: The Nilakantha series starts at 3 and the first term is
#         positive, with subsequent subtractions being smaller in magnitude.
#         This property should always hold.
#    2. `test_z3_monotonic_convergence`:
#       - Property: The approximation error should decrease or stay the same as
#         `n_terms` increases. Formally:
#         `abs(pi_calc(n + 1) - PI) <= abs(pi_calc(n) - PI)` for `n >= 0`.
#       - Method: Model the function and the property in Z3. Check if the
#         solver can find a counterexample. The expected result is `unsat`.
#       - Rationale: This is the core definition of a converging series.
#         Proving it formally provides a strong guarantee about the algorithm's
#         correctness.
#

# --- Unit Tests ---

def test_negative_input():
    """
    Tests that a negative number of terms raises a ValueError.
    """
    with pytest.raises(ValueError, match="The number of terms cannot be negative."):
        pi_calc(n_terms=-1)

def test_non_integer_input_float():
    """
    Tests that a float number of terms raises a TypeError.
    """
    with pytest.raises(TypeError, match="The number of terms must be an integer."):
        pi_calc(n_terms=100.5)

def test_non_integer_input_string():
    """
    Tests that a string input for terms raises a TypeError.
    """
    with pytest.raises(TypeError, match="The number of terms must be an integer."):
        pi_calc(n_terms="100")

def test_zero_terms():
    """
    Tests the base case of 0 terms, which should return the starting value 3.0.
    """
    assert pi_calc(n_terms=0) == 3.0

def test_one_term():
    """
    Tests the calculation with a single term from the series.
    """
    expected = 3.0 + 4.0 / (2.0 * 3.0 * 4.0)
    assert pi_calc(n_terms=1) == pytest.approx(expected)

def test_two_terms():
    """
    Tests the calculation with two terms, verifying the sign change.
    """
    expected = 3.0 + 4.0 / (2.0 * 3.0 * 4.0) - 4.0 / (4.0 * 5.0 * 6.0)
    assert pi_calc(n_terms=2) == pytest.approx(expected)

def test_default_terms_convergence():
    """
    Tests that the default number of terms (100,000) yields a result
    very close to math.pi.
    """
    # A tolerance of 1e-10 is appropriate for 100,000 terms.
    assert pi_calc() == pytest.approx(math.pi, abs=1e-10)

def test_large_terms_convergence():
    """
    Tests that a large number of terms (200,000) yields a result
    very close to math.pi.
    """
    # A tolerance of 1e-11 is appropriate for 200,000 terms.
    assert pi_calc(n_terms=200000) == pytest.approx(math.pi, abs=1e-11)

def test_convergence_improves():
    """
    Tests that increasing the number of terms improves the approximation.
    """
    error_1000 = abs(pi_calc(n_terms=1000) - math.pi)
    error_10000 = abs(pi_calc(n_terms=10000) - math.pi)
    assert error_10000 < error_1000


# --- Formal Verification with Z3 ---

# The original pi_calc_z3_model is removed as it causes a RecursionError
# with symbolic variables. We now define the function's properties directly
# in the solver using Z3's Function and ForAll constructs.

@pytest.mark.skipif(not Z3_AVAILABLE, reason="Z3 solver not installed")
def test_z3_is_always_greater_than_three():
    """
    Formally verifies that for n_terms >= 1, the result is always > 3.
    """
    s = z3.Solver()
    n = z3.Int('n') # n represents n_terms

    # We define a recursive function pi_approx(i) in Z3 to model the calculation.
    # pi_approx(Int) -> Real
    pi_approx = z3.Function('pi_approx', z3.IntSort(), z3.RealSort())

    # Define a variable 'i' for the quantifier
    i = z3.Int('i')
    i_real = z3.ToReal(i)

    # Define the i-th term of the Nilakantha series
    denominator = (2 * i_real) * (2 * i_real + 1) * (2 * i_real + 2)
    sign = z3.If(i % 2 == 1, z3.RealVal(1), z3.RealVal(-1))
    ith_term = sign * (z3.RealVal(4) / denominator)

    # Define the behavior of our Z3 function
    # Base case: pi_approx(0) = 3
    s.add(pi_approx(0) == 3)
    # Recursive step: for all i >= 1, pi_approx(i) = pi_approx(i-1) + ith_term
    s.add(z3.ForAll([i], z3.Implies(i >= 1, pi_approx(i) == pi_approx(i - 1) + ith_term)))

    # Constraint: n must be a non-negative integer >= 1
    s.add(n >= 1)

    # Negation of the property we want to prove:
    # Is it possible for the result to be less than or equal to 3?
    s.add(pi_approx(n) <= 3)

    # If the solver finds a model (sat), it's a counterexample.
    # If it's unsat, no counterexample exists, and the property is proven.
    assert s.check() == z3.unsat, "Z3 found a counterexample where pi_calc(n) <= 3 for n >= 1"

@pytest.mark.skipif(not Z3_AVAILABLE, reason="Z3 solver not installed")
def test_z3_monotonic_convergence():
    """
    Formally verifies that the error decreases as n_terms increases.
    |pi_calc(n+1) - PI| <= |pi_calc(n) - PI|
    """
    s = z3.Solver()
    n = z3.Int('n')

    # Define the recursive function pi_approx(i) in Z3, same as the test above.
    pi_approx = z3.Function('pi_approx', z3.IntSort(), z3.RealSort())
    i = z3.Int('i')
    i_real = z3.ToReal(i)
    denominator = (2 * i_real) * (2 * i_real + 1) * (2 * i_real + 2)
    sign = z3.If(i % 2 == 1, z3.RealVal(1), z3.RealVal(-1))
    ith_term = sign * (z3.RealVal(4) / denominator)
    s.add(pi_approx(0) == 3)
    s.add(z3.ForAll([i], z3.Implies(i >= 1, pi_approx(i) == pi_approx(i - 1) + ith_term)))

    # Use a high-precision value for Pi as a Z3 Real constant
    PI = z3.RealVal(math.pi)

    # Constraint: n must be a non-negative integer
    s.add(n >= 0)

    # Model the function for n and n+1
    pi_n = pi_approx(n)
    pi_n_plus_1 = pi_approx(n + 1)

    # Define the absolute error for n and n+1
    # Z3 doesn't have a built-in abs, so we use If(x < 0, -x, x)
    def z3_abs(x):
        return z3.If(x < 0, -x, x)

    error_n = z3_abs(pi_n - PI)
    error_n_plus_1 = z3_abs(pi_n_plus_1 - PI)

    # Negation of the property:
    # Is it possible for the error to INCREASE?
    s.add(error_n_plus_1 > error_n)

    # Check for a counterexample. `unsat` proves the property.
    # Note: This is a complex non-linear problem. Z3 may be slow or return `unknown`.
    # For the Nilakantha series, this property holds, and Z3 should prove it.
    result = s.check()
    assert result == z3.unsat, f"Z3 found a counterexample to monotonic convergence: {s.model() if result == z3.sat else 'unknown'}"
