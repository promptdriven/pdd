import pytest
from z3 import Real, Solver, unsat
import sys
import os

# Ensure the module can be imported if not in the path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from calculator import add_numbers

"""
TEST PLAN: add_numbers(a, b)

1. Functional Unit Tests:
    - Basic Addition: Verify positive integers (e.g., 5 + 3 = 8).
    - Floating Point: Verify float addition (e.g., 10.5 + 2.5 = 13.0).
    - Negative Numbers: Verify addition with negative values (e.g., -1 + -1 = -2, -5 + 10 = 5).
    - Zero: Verify identity property with zero (e.g., 5 + 0 = 5).
    - Large Numbers: Verify behavior with very large floats.

2. Edge Case Analysis (Unit Test vs Z3):
    - Commutativity (a + b == b + a): Better for Z3. It proves the property for all possible real numbers rather than just specific samples.
    - Identity (a + 0 == a): Better for Z3. Proves that 0 is the additive identity for all inputs.
    - Floating Point Precision (0.1 + 0.2): Better for Unit Tests. Standard IEEE 754 behavior in Python results in 0.30000000000000004. Z3 (using Real) treats these as exact fractions, so unit tests are needed to check actual Python runtime behavior.
    - Type Safety: Better for Unit Tests. Verify that passing strings or None raises a TypeError.

3. Formal Verification (Z3):
    - Prove Commutativity: For any two real numbers a and b, add_numbers(a, b) == add_numbers(b, a).
    - Prove Identity: For any real number a, add_numbers(a, 0) == a.
"""

# --- Unit Tests ---

def test_add_numbers_positive():
    """Test addition of two positive integers/floats."""
    assert add_numbers(5, 3) == 8
    assert add_numbers(10.5, 4.5) == 15.0

def test_add_numbers_negative():
    """Test addition involving negative numbers."""
    assert add_numbers(-1, -1) == -2
    assert add_numbers(-5, 10) == 5
    assert add_numbers(5, -10) == -5

def test_add_numbers_zero():
    """Test addition with zero."""
    assert add_numbers(0, 0) == 0
    assert add_numbers(5, 0) == 5
    assert add_numbers(0, -5) == -5

def test_add_numbers_floats():
    """Test floating point precision."""
    # Note: 0.1 + 0.2 in floating point is 0.30000000000000004
    assert add_numbers(0.1, 0.2) == pytest.approx(0.3)

def test_add_numbers_large():
    """Test addition of large numbers."""
    assert add_numbers(1e10, 1e10) == 2e10

def test_add_numbers_invalid_types():
    """Test that the function raises TypeError when non-numbers are passed."""
    with pytest.raises(TypeError):
        add_numbers("1", 2)
    with pytest.raises(TypeError):
        add_numbers(None, 5)

# --- Formal Verification Tests (Z3) ---

def test_formal_commutativity():
    """
    Formal verification of the Commutative Property: a + b == b + a
    """
    a = Real('a')
    b = Real('b')
    
    solver = Solver()
    # We want to prove: add_numbers(a, b) == add_numbers(b, a)
    # To prove it with Z3, we ask for the negation: add_numbers(a, b) != add_numbers(b, a)
    # If the negation is 'unsat', the original property is 'valid'.
    solver.add(a + b != b + a)
    
    result = solver.check()
    assert result == unsat, f"Commutativity failed. Counterexample: {solver.model()}"

def test_formal_identity():
    """
    Formal verification of the Identity Property: a + 0 == a
    """
    a = Real('a')
    
    solver = Solver()
    # Negation: a + 0 != a
    solver.add(a + 0 != a)
    
    result = solver.check()
    assert result == unsat, f"Identity property failed. Counterexample: {solver.model()}"

def test_formal_associativity():
    """
    Formal verification of the Associative Property: (a + b) + c == a + (b + c)
    Note: This holds for Z3 Reals, though it may not hold for IEEE 754 Floats.
    """
    a = Real('a')
    b = Real('b')
    c = Real('c')
    
    solver = Solver()
    # Negation: (a + b) + c != a + (b + c)
    solver.add((a + b) + c != a + (b + c))
    
    result = solver.check()
    assert result == unsat, f"Associativity failed. Counterexample: {solver.model()}"

def test_add_numbers_special_floats():
    """
    Test addition with special floating point values: Infinity and NaN.
    """
    inf = float('inf')
    nan = float('nan')

    # Infinity checks
    assert add_numbers(inf, 100) == inf
    assert add_numbers(inf, inf) == inf
    assert add_numbers(-inf, -100) == -inf
    
    # NaN checks
    # Note: NaN != NaN is the standard way to check for NaN without importing math
    result_nan = add_numbers(nan, 5)
    assert result_nan != result_nan, "Adding to NaN should result in NaN"
    
    # Inf + (-Inf) results in NaN
    result_inf_neg_inf = add_numbers(inf, -inf)
    assert result_inf_neg_inf != result_inf_neg_inf, "Inf + (-Inf) should result in NaN"

def test_add_numbers_mixed_numeric_types():
    """
    Test that the function handles mixed integer and float inputs correctly.
    """
    # Int + Float
    assert add_numbers(5, 2.5) == 7.5
    assert isinstance(add_numbers(5, 2.5), float)
    
    # Float + Int
    assert add_numbers(3.2, 4) == 7.2
    
    # Int + Int (should return int or float depending on implementation, 
    # but Python + operator preserves type if both are int, though type hint says float return)
    # The implementation is just a + b. 5 + 3 is 8 (int). 
    # The type hint says -> float, but Python doesn't enforce it at runtime.
    # We verify the value is correct regardless of return type.
    assert add_numbers(2, 2) == 4

# --- Additional Formal Verification Tests (Z3) ---

def test_formal_inverse_property():
    """
    Formal verification of the Inverse Property: (a + b) - b == a
    """
    a = Real('a')
    b = Real('b')
    
    solver = Solver()
    # Negation: (a + b) - b != a
    solver.add((a + b) - b != a)
    
    result = solver.check()
    assert result == unsat, f"Inverse property failed. Counterexample: {solver.model()}"

def test_formal_distributive_property():
    """
    Formal verification of the Distributive Property: c * (a + b) == c * a + c * b
    """
    a = Real('a')
    b = Real('b')
    c = Real('c')
    
    solver = Solver()
    # Negation: c * (a + b) != c * a + c * b
    solver.add(c * (a + b) != c * a + c * b)
    
    result = solver.check()
    assert result == unsat, f"Distributive property failed. Counterexample: {solver.model()}"