# Test Plan:
# 1. Verify basic integer addition (positive + positive).
# 2. Verify floating point addition.
# 3. Verify addition with negative numbers.
# 4. Verify mixed type addition (int + float).
# 5. Verify addition with zero (identity property).
# 6. Verify large number addition.
# 7. Formal Verification (Z3): Prove Commutativity (a + b == b + a).
# 8. Formal Verification (Z3): Prove Identity (a + 0 == a).
# 9. Formal Verification (Z3): Prove Associativity (a + (b + c) == (a + b) + c).

import sys
import os
import pytest
from z3 import *

# Add the project root directory to the Python path to allow importing the module.
# Based on the example file path: /Users/serhanasad/Desktop/SF/pdd/examples/simple_math/simple_math_example.py
# And the test file path: /Users/serhanasad/Desktop/SF/pdd/tests/test_simple_math.py
# The module is likely at /Users/serhanasad/Desktop/SF/pdd/simple_math.py
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, ".."))
sys.path.insert(0, project_root)

# Import the specific function from the module
try:
    from simple_math import add
except ImportError:
    # Fallback for when running tests directly if structure differs slightly
    sys.path.append(os.path.abspath(os.path.join(current_dir, "..", "pdd")))
    from simple_math import add

def test_add_integers():
    """
    Verify that the function correctly adds two positive integers.
    Matches Example 1 from usage file.
    """
    assert add(10, 5) == 15
    assert add(1, 1) == 2
    assert add(100, 200) == 300

def test_add_floats():
    """
    Verify that the function correctly adds two floating point numbers.
    Matches Example 2 from usage file.
    """
    result = add(10.5, 2.3)
    # Use approx for float comparison to handle precision issues
    assert result == pytest.approx(12.8)
    assert add(1.1, 1.1) == pytest.approx(2.2)

def test_add_negative_numbers():
    """
    Verify that the function correctly handles negative numbers.
    Matches Example 3 from usage file.
    """
    assert add(-7, 3) == -4
    assert add(5, -10) == -5
    assert add(-2, -2) == -4

def test_add_mixed_types():
    """
    Verify that the function can handle adding an integer and a float.
    """
    assert add(5, 2.5) == pytest.approx(7.5)
    assert add(2.5, 5) == pytest.approx(7.5)

def test_add_zero_identity():
    """
    Verify the identity property of addition with zero using concrete values.
    """
    assert add(10, 0) == 10
    assert add(0, 10) == 10
    assert add(0, 0) == 0

def test_add_large_numbers():
    """
    Verify that Python's arbitrary precision integers are handled correctly.
    """
    large_num = 10**20
    assert add(large_num, 1) == 100000000000000000001

# --- Z3 Formal Verification Tests ---

def test_z3_commutativity():
    """
    Formal Verification: Prove that add(a, b) == add(b, a) for integers.
    """
    # Create Z3 integer variables
    a = Int('a')
    b = Int('b')

    # We want to prove: add(a, b) == add(b, a)
    # To prove a property P, we try to find a counter-example to Not(P).
    # If Not(P) is unsatisfiable, then P is valid.
    
    # Note: We are testing the *logic* of addition. Since we can't pass Z3 variables 
    # directly into a Python function if that function does type checking or complex 
    # operations not supported by Z3, we assume the implementation is a simple `a + b`.
    # However, if the implementation is `return a + b`, Python will construct a Z3 expression.
    
    try:
        # This attempts to use the actual python function to build the Z3 expression
        expr_lhs = add(a, b)
        expr_rhs = add(b, a)
        
        solver = Solver()
        solver.add(expr_lhs != expr_rhs) # Assert the negation

        # Check if a counter-example exists
        result = solver.check()
        
        if result == sat:
            model = solver.model()
            pytest.fail(f"Commutativity failed for inputs: a={model[a]}, b={model[b]}")
        else:
            # unsat means no counter-example exists, so the property holds
            pass
            
    except Exception as e:
        pytest.fail(f"Could not run Z3 verification on function implementation: {e}")

def test_z3_identity():
    """
    Formal Verification: Prove that add(a, 0) == a for integers.
    """
    a = Int('a')
    
    try:
        # Property: a + 0 == a
        # Negation: a + 0 != a
        expr = add(a, 0)
        
        solver = Solver()
        solver.add(expr != a)
        
        result = solver.check()
        
        if result == sat:
            model = solver.model()
            pytest.fail(f"Identity property failed for input: a={model[a]}")
            
    except Exception as e:
        pytest.fail(f"Could not run Z3 verification on function implementation: {e}")

def test_z3_associativity():
    """
    Formal Verification: Prove that add(a, add(b, c)) == add(add(a, b), c).
    """
    a = Int('a')
    b = Int('b')
    c = Int('c')
    
    try:
        # Property: a + (b + c) == (a + b) + c
        lhs = add(a, add(b, c))
        rhs = add(add(a, b), c)
        
        solver = Solver()
        solver.add(lhs != rhs) # Assert negation
        
        result = solver.check()
        
        if result == sat:
            model = solver.model()
            pytest.fail(f"Associativity failed for inputs: a={model[a]}, b={model[b]}, c={model[c]}")
            
    except Exception as e:
        pytest.fail(f"Could not run Z3 verification on function implementation: {e}")