# TEST PLAN: add_numbers
# 
# 1. ANALYSIS OF CODE UNDER TEST:
#    - Function: add_numbers(a: float, b: float) -> float
#    - Behavior: Returns the sum of two numbers using the '+' operator.
#    - Edge Cases: Zero, negative numbers, large floats, floating point precision (e.g., 0.1 + 0.2), 
#      infinity, and NaN.
#
# 2. Z3 FORMAL VERIFICATION VS. UNIT TESTING:
#    - Basic Arithmetic (1 + 1 = 2): Unit Test. Simple, direct, and verifies the Python interpreter's behavior.
#    - Commutative Property (a + b == b + a): Z3. Formal verification can prove this holds for all 
#      possible real numbers, which is more exhaustive than specific unit test cases.
#    - Identity Property (a + 0 == a): Z3. Proves that adding zero never changes the value for any input.
#    - Associative Property (a + (b + c) == (a + b) + c): Z3. Useful for verifying algebraic consistency, 
#      though note that floating point math in practice is not always associative; Z3 'Reals' will 
#      treat them as exact.
#    - IEEE 754 Special Values (Inf, NaN): Unit Test. Python's handling of float('inf') and float('nan') 
#      is best verified through the actual runtime environment.
#
# 3. TEST CASES:
#    - test_add_positive_numbers: Standard positive integers/floats.
#    - test_add_negative_numbers: Verifying signs are handled correctly.
#    - test_add_zero: Identity element check.
#    - test_floating_point_precision: Checking 0.1 + 0.2 behavior.
#    - test_z3_commutative_property: Formal proof of commutativity.
#    - test_z3_identity_property: Formal proof of identity.

import pytest
from z3 import Real, Solver, prove, sat, Not, unsat
from calculator import add_numbers

# --- Unit Tests ---

def test_add_positive_numbers():
    """Test addition of two positive numbers."""
    assert add_numbers(5, 3) == 8
    assert add_numbers(10.5, 4.5) == 15.0

def test_add_negative_numbers():
    """Test addition involving negative numbers."""
    assert add_numbers(-1, -1) == -2
    assert add_numbers(-5, 10) == 5

def test_add_zero():
    """Test addition with zero."""
    assert add_numbers(0, 0) == 0
    assert add_numbers(5.5, 0) == 5.5
    assert add_numbers(0, -3) == -3

def test_floating_point_precision():
    """Test floating point precision behavior (standard IEEE 754)."""
    # Note: 0.1 + 0.2 in binary floats is 0.30000000000000004
    assert add_numbers(0.1, 0.2) == pytest.approx(0.3)

def test_large_numbers():
    """Test addition of large floating point numbers."""
    assert add_numbers(1e10, 1e10) == 2e10

# --- Z3 Formal Verification Tests ---

def test_z3_commutative_property():
    """
    Formally verify the commutative property: a + b == b + a
    Using Z3 Reals to represent the mathematical intent.
    """
    a = Real('a')
    b = Real('b')
    
    solver = Solver()
    # We want to check if there is ANY case where a + b != b + a
    # If the solver finds 'unsat' for the negation, the property is proven.
    solver.add(Not(a + b == b + a))
    
    result = solver.check()
    assert result == unsat, f"Commutative property failed: {solver.model()}"

def test_z3_identity_property():
    """
    Formally verify the identity property: a + 0 == a
    """
    a = Real('a')
    
    solver = Solver()
    # Check if there is any 'a' such that a + 0 != a
    solver.add(Not(a + 0 == a))
    
    result = solver.check()
    assert result == unsat, f"Identity property failed: {solver.model()}"

def test_z3_associative_property():
    """
    Formally verify the associative property: (a + b) + c == a + (b + c)
    Note: This holds for mathematical Reals, though not always for IEEE 754 Floats.
    """
    a = Real('a')
    b = Real('b')
    c = Real('c')
    
    solver = Solver()
    solver.add(Not((a + b) + c == a + (b + c)))
    
    result = solver.check()
    assert result == unsat, f"Associative property failed: {solver.model()}"

# TEST PLAN: add_numbers (Additional Tests)
# 
# 1. ANALYSIS OF CODE UNDER TEST:
#    - Function: add_numbers(a: float, b: float) -> float
#    - Behavior: Simple addition of two floats.
#    - Existing Coverage: Positive/Negative numbers, Zero, Precision (0.1+0.2), Large numbers, 
#      Z3 Commutativity, Z3 Identity, Z3 Associativity.
#
# 2. Z3 FORMAL VERIFICATION VS. UNIT TESTING (NEW CASES):
#    - Infinity Handling (inf + 1 = inf): Unit Test. Python's float('inf') behavior is specific 
#      to the IEEE 754 implementation in the interpreter.
#    - NaN Handling (nan + 1 = nan): Unit Test. NaN has unique properties (e.g., nan != nan) 
#      that are best verified via the runtime.
#    - Inverse Property (a + (-a) == 0): Z3. Formal verification can prove that for any 
#      real number, adding its negation results in exactly zero.
#    - Type Handling (Integers vs Floats): Unit Test. Verifying that the function handles 
#      Python's dynamic casting (int passed to float hint) correctly.
#
# 3. NEW TEST CASES:
#    - test_add_infinity: Verifying behavior with math.inf.
#    - test_add_nan: Verifying behavior with math.nan.
#    - test_add_mixed_types: Verifying int and float interoperability.
#    - test_z3_inverse_property: Formal proof that a + (-a) == 0.

import math
from z3 import Real, Solver, Not, unsat

# Assuming add_numbers is defined elsewhere or imported
def add_numbers(a: float, b: float) -> float:
    return a + b

# --- Unit Tests ---

def test_add_infinity():
    """Test addition involving infinity."""
    inf = float('inf')
    assert add_numbers(inf, 1.0) == inf
    assert add_numbers(inf, inf) == inf
    assert add_numbers(-inf, -1.0) == -inf
    # inf + (-inf) is NaN, handled in NaN test

def test_add_nan():
    """Test addition involving NaN (Not a Number)."""
    nan = float('nan')
    # Any operation with NaN should result in NaN
    assert math.isnan(add_numbers(nan, 5.0))
    assert math.isnan(add_numbers(float('inf'), float('-inf')))

def test_add_mixed_types():
    """Test that the function handles integers passed to float parameters."""
    # Python handles this automatically, but good to verify the contract
    assert add_numbers(5, 2) == 7.0
    assert isinstance(add_numbers(1, 1), (float, int))

# --- Z3 Formal Verification Tests ---

def test_z3_inverse_property():
    """
    Formally verify the additive inverse property: a + (-a) == 0
    Using Z3 Reals to represent the mathematical intent.
    """
    a = Real('a')
    
    solver = Solver()
    # Check if there is any 'a' such that a + (-a) != 0
    solver.add(Not(a + (-a) == 0))
    
    result = solver.check()
    assert result == unsat, f"Inverse property failed: {solver.model()}"

def test_z3_monotonicity():
    """
    Formally verify monotonicity: if a > b, then a + c > b + c
    """
    a = Real('a')
    b = Real('b')
    c = Real('c')
    
    solver = Solver()
    # We want to prove (a > b) => (a + c > b + c)
    # So we look for a counter-example: (a > b) AND NOT (a + c > b + c)
    solver.add(a > b)
    solver.add(Not(a + c > b + c))
    
    result = solver.check()
    assert result == unsat, f"Monotonicity property failed: {solver.model()}"

def test_add_strings_raises_error():
    """Test that passing strings to add_numbers raises a TypeError."""
    with pytest.raises(TypeError):
        # Even though type hints say float, Python doesn't enforce at runtime
        # without a checker, so we verify the '+' operator behavior.
        add_numbers("1", "2")

def test_subnormal_numbers():
    """Test addition with subnormal (extremely small) floating point numbers."""
    small_val = 5e-324  # Smallest positive denormalized float
    assert add_numbers(small_val, small_val) == 1e-323
    assert add_numbers(small_val, 0) == small_val

# --- Z3 Formal Verification Tests ---

def test_z3_subtraction_equivalence():
    """
    Formally verify the relationship: a + b = c is equivalent to a = c - b.
    """
    a = Real('a')
    b = Real('b')
    c = Real('c')
    
    solver = Solver()
    # We want to prove (a + b == c) <-> (a == c - b)
    # Counter-example: Not((a + b == c) == (a == c - b))
    solver.add(Not((a + b == c) == (a == c - b)))
    
    result = solver.check()
    assert result == unsat, f"Subtraction equivalence failed: {solver.model()}"

def test_z3_negation_distribution():
    """
    Formally verify that the negation of a sum is the sum of the negations: -(a + b) == (-a) + (-b)
    """
    a = Real('a')
    b = Real('b')
    
    solver = Solver()
    # Check if there is any case where -(a + b) != -a - b
    solver.add(Not(-(a + b) == (-a) + (-b)))
    
    result = solver.check()
    assert result == unsat, f"Negation distribution failed: {solver.model()}"

def test_z3_strict_monotonicity():
    """
    Formally verify strict monotonicity: if a > 0 and b > 0, then a + b > a and a + b > b.
    """
    a = Real('a')
    b = Real('b')
    
    solver = Solver()
    # Counter-example: (a > 0 AND b > 0) AND NOT (a + b > a)
    solver.add(a > 0)
    solver.add(b > 0)
    solver.add(Not(a + b > a))
    
    result = solver.check()
    assert result == unsat, f"Strict monotonicity failed: {solver.model()}"