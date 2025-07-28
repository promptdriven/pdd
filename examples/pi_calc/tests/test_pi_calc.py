# test_pi_calc.py

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
#         if the solver can find a counterexample to `pi_calc(n) <= 3`.
#         The expected result is `unsat`, proving the property.
#       - Rationale: The Nilakantha series starts at 3 and the first term is
#         positive, with subsequent subtractions being smaller in magnitude.
#         This property should always hold.
#    2. `test_z3_term_magnitude_decreases`:
#       - Property: The absolute magnitude of the terms added or subtracted
#         in the series should monotonically decrease. Formally:
#         `|term(n+1)| < |term(n)|` for `n >= 1`.
#       - Method: Model the denominators of the n-th and (n+1)-th terms in Z3.
#         Assert that the denominator for term n is greater than or equal to
#         the denominator for term n+1. The expected result is `unsat`,
#         proving the property.
#       - Rationale: For an alternating series, proving that the terms
#         monotonically decrease in magnitude is a key part of proving
#         convergence (via the Alternating Series Test). This is a more
#         tractable property for a solver to prove than direct error
#         convergence, yet it still provides a strong formal guarantee.
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

@pytest.mark.skipif(not Z3_AVAILABLE, reason="Z3 solver not installed")
def test_z3_is_always_greater_than_three():
    """
    Formally verifies that for n_terms >= 1, the result is always > 3.
    """
    s = z3.Solver()
    n = z3.Int('n') # n represents n_terms

    # Define the recursive function for the pi approximation using Z3's capabilities
    pi_approx = z3.RecFunction('pi_approx', z3.IntSort(), z3.RealSort())
    i = z3.Int('i') # A dummy variable for the function definition

    # Define the i-th term symbolically
    i_real = z3.ToReal(i)
    denominator = (2 * i_real) * (2 * i_real + 1) * (2 * i_real + 2)
    sign = z3.If(i % 2 == 1, z3.RealVal(1), z3.RealVal(-1))
    nth_term = sign * (z3.RealVal(4) / denominator)

    # Add the recursive definition as an axiom for the solver.
    z3.RecAddDefinition(pi_approx, i,
        z3.If(i == 0,
              z3.RealVal(3),
              pi_approx(i - 1) + nth_term
        )
    )

    # Constraint: n must be a non-negative integer >= 1
    s.add(n >= 1)

    # Model the function call using the axiomatically-defined function
    pi_approximation = pi_approx(n)

    # Negation of the property we want to prove:
    # Is it possible for the result to be less than or equal to 3?
    s.add(pi_approximation <= 3)

    # If the solver finds a model (sat), it's a counterexample.
    # If it's unsat, no counterexample exists, and the property is proven.
    assert s.check() == z3.unsat, "Z3 found a counterexample where pi_calc(n) <= 3 for n >= 1"

@pytest.mark.skipif(not Z3_AVAILABLE, reason="Z3 solver not installed")
def test_z3_term_magnitude_decreases():
    """
    Formally verifies that the absolute magnitude of the terms in the series
    is monotonically decreasing for n >= 1. This is a key condition for the
    convergence of an alternating series and prevents test timeouts.
    """
    s = z3.Solver()
    n = z3.Int('n')

    # We want to prove that for n >= 1, |term(n+1)| < |term(n)|.
    # The i-th term's denominator is (2*i)*(2*i+1)*(2*i+2).
    
    # Constraint: n must be a positive integer.
    s.add(n >= 1)

    # Define the denominators for the n-th and (n+1)-th terms as Reals.
    n_real = z3.ToReal(n)
    
    # Denominator for the n-th term.
    denom_n = (2 * n_real) * (2 * n_real + 1) * (2 * n_real + 2)
    
    # Denominator for the (n+1)-th term.
    denom_n_plus_1 = (2 * (n_real + 1)) * (2 * (n_real + 1) + 1) * (2 * (n_real + 1) + 2)

    # The property |term(n+1)| < |term(n)| is equivalent to
    # 4.0 / denom_n_plus_1 < 4.0 / denom_n.
    # Since denominators are positive for n>=1, this is equivalent to
    # denom_n < denom_n_plus_1.

    # Negation of the property: Is it possible for the magnitude to increase
    # or stay the same? This is equivalent to denom_n >= denom_n_plus_1.
    s.add(denom_n >= denom_n_plus_1)

    # If the solver finds a model (sat), it's a counterexample.
    # If it's unsat, no counterexample exists, and the property is proven.
    result = s.check()
    assert result == z3.unsat, f"Z3 found a counterexample where term magnitude did not decrease: {s.model() if result == z3.sat else 'unknown'}"
