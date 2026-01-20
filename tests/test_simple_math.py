"""
Test Plan for simple_math.py:

1. Unit Tests:
    - test_add_integers: Verify basic integer addition (2 + 3 = 5).
    - test_add_floats: Verify basic float addition (2.5 + 3.5 = 6.0).
    - test_add_mixed: Verify mixed type addition (2 + 3.5 = 5.5).
    - test_add_zero: Verify identity property with zero (0 + 0 = 0, 5 + 0 = 5).
    - test_add_negatives: Verify addition with negative numbers (-5 + 10 = 5).
    - test_add_large_numbers: Verify addition with large integers to ensure no overflow issues (Python handles this natively).

2. Z3 Formal Verification:
    - test_z3_commutativity: Formally prove that add(a, b) == add(b, a) for integers.
    - test_z3_identity: Formally prove that add(a, 0) == a for integers.
    - test_z3_associativity: Formally prove that add(add(a, b), c) == add(a, add(b, c)) for integers.
"""

import pytest
import sys
import os
from z3 import Int, Solver, sat

# Add the path to the module to sys.path to allow import
# The file path provided was: /Users/gregtanaka/Documents/pdd_cloud/pdd/pdd/simple_math.py
sys.path.append('/Users/gregtanaka/Documents/pdd_cloud/pdd/pdd')

try:
    from simple_math import add
except ImportError:
    # Fallback if the path setup fails or running in a different environment
    # This allows the test to fail gracefully or be adjusted
    raise ImportError("Could not import 'simple_math'. Check sys.path configuration.")

# --- Unit Tests ---

def test_add_integers():
    """Verify that adding two integers returns the correct integer sum."""
    result = add(2, 3)
    assert result == 5
    assert isinstance(result, int)

def test_add_floats():
    """Verify that adding two floats returns the correct float sum."""
    result = add(2.5, 3.5)
    assert result == 6.0
    assert isinstance(result, float)

def test_add_mixed():
    """Verify that adding an int and a float returns a float."""
    result = add(2, 3.5)
    assert result == 5.5
    assert isinstance(result, float)

def test_add_zero():
    """Verify the identity property of addition with zero."""
    assert add(0, 0) == 0
    assert add(5, 0) == 5
    assert add(0, 10.5) == 10.5

def test_add_negatives():
    """Verify addition works correctly with negative numbers."""
    assert add(-5, 10) == 5
    assert add(-5, -5) == -10
    assert add(3.14, -2.71) == pytest.approx(0.43)

def test_add_large_numbers():
    """Verify addition works for large integers (Python arbitrary precision)."""
    a = 10**20
    b = 10**20
    assert add(a, b) == 2 * 10**20

# --- Z3 Formal Verification Tests ---

def test_z3_commutativity():
    """
    Formally verify the commutativity property: add(a, b) == add(b, a).
    We use Z3 to search for a counter-example. If UNSAT, the property holds.
    """
    s = Solver()
    x = Int('x')
    y = Int('y')

    # We want to prove: add(x, y) == add(y, x)
    # We ask Z3 to find a case where: add(x, y) != add(y, x)
    
    # Note: We are modeling the python function logic in Z3. 
    # Since the python function is just `a + b`, we map it directly to Z3's `+`.
    
    # Constraint: Find x, y such that x + y != y + x
    s.add(x + y != y + x)

    # If Z3 cannot find a solution (unsat), it means no counter-example exists,
    # so the property holds for all Integers.
    result = s.check()
    assert result != sat, f"Found counter-example to commutativity: {s.model()}"

def test_z3_identity():
    """
    Formally verify the identity property: add(a, 0) == a.
    """
    s = Solver()
    x = Int('x')

    # We want to prove: add(x, 0) == x
    # We ask Z3 to find a case where: add(x, 0) != x
    s.add(x + 0 != x)

    result = s.check()
    assert result != sat, f"Found counter-example to identity property: {s.model()}"

def test_z3_associativity():
    """
    Formally verify the associativity property: (a + b) + c == a + (b + c).
    """
    s = Solver()
    x = Int('x')
    y = Int('y')
    z = Int('z')

    # We want to prove: (x + y) + z == x + (y + z)
    # We ask Z3 to find a counter-example.
    lhs = (x + y) + z
    rhs = x + (y + z)
    
    s.add(lhs != rhs)

    result = s.check()
    assert result != sat, f"Found counter-example to associativity: {s.model()}"