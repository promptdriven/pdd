from solution import add
import pytest
import math
from z3 import Real, Int, Solver, sat, unsat

# ============================================================================
# UNIT TESTS
# ============================================================================

def test_add_positive_integers():
    """Test addition of positive integers."""
    assert add(5, 3) == 8
    assert add(10, 20) == 30
    assert add(100, 200) == 300

def test_add_negative_integers():
    """Test addition involving negative integers."""
    assert add(-4, 10) == 6
    assert add(-5, -3) == -8
    assert add(7, -7) == 0

def test_add_floats():
    """Test addition of floating point numbers."""
    assert add(2.5, 3.7) == pytest.approx(6.2)
    assert add(1.1, 2.2) == pytest.approx(3.3)
    assert add(-3.14, 6.28) == pytest.approx(3.14)

def test_add_mixed_types():
    """Test addition of mixed int and float types."""
    assert add(5, 2.5) == 7.5
    assert add(3.7, 2) == 5.7
    assert add(0, 0.0) == 0.0

def test_add_zero():
    """Test addition with zero (identity element)."""
    assert add(0, 0) == 0
    assert add(5, 0) == 5
    assert add(0, 3.14) == 3.14
    assert add(-10, 0) == -10

def test_add_large_numbers():
    """Test addition with large numbers."""
    assert add(10**6, 10**6) == 2 * 10**6
    assert add(-10**6, 10**6) == 0
    assert add(10**10, 10**10) == 2 * 10**10

def test_add_small_floats():
    """Test addition with very small floating point numbers."""
    assert add(1e-10, 2e-10) == pytest.approx(3e-10)
    assert add(1e-15, -1e-15) == pytest.approx(0)

def test_add_special_float_values():
    """Test addition with special float values."""
    assert math.isinf(add(float('inf'), 5))
    assert math.isinf(add(float('-inf'), 5))
    assert math.isnan(add(float('nan'), 5))

def test_add_commutative_examples():
    """Test commutative property with specific examples."""
    assert add(5, 3) == add(3, 5)
    assert add(2.5, 3.7) == add(3.7, 2.5)
    assert add(-4, 10) == add(10, -4)

def test_add_associative_examples():
    """Test associative property with specific examples."""
    a, b, c = 5, 3, 2
    assert add(add(a, b), c) == add(a, add(b, c))
    
    a, b, c = 2.5, 3.7, 1.2
    assert add(add(a, b), c) == pytest.approx(add(a, add(b, c)))

def test_add_error_non_numeric():
    """Test that non-numeric inputs raise TypeError."""
    with pytest.raises(TypeError):
        add("hello", 5)
    
    with pytest.raises(TypeError):
        add(5, "world")
    
    with pytest.raises(TypeError):
        add([1, 2], 3)

def test_add_error_wrong_number_of_args():
    """Test that wrong number of arguments raises TypeError."""
    with pytest.raises(TypeError):
        add(5)
    
    with pytest.raises(TypeError):
        add(1, 2, 3)

# ============================================================================
# Z3 FORMAL VERIFICATION TESTS
# ============================================================================

def test_z3_commutativity_int():
    """Formally verify commutativity for integers."""
    a = Int('a')
    b = Int('b')
    
    s = Solver()
    s.add(a + b != b + a)
    
    assert s.check() == unsat, "Commutativity failed for integers"

def test_z3_commutativity_real():
    """Formally verify commutativity for real numbers."""
    a = Real('a')
    b = Real('b')
    
    s = Solver()
    s.add(a + b != b + a)
    
    assert s.check() == unsat, "Commutativity failed for real numbers"

def test_z3_associativity_int():
    """Formally verify associativity for integers."""
    a = Int('a')
    b = Int('b')
    c = Int('c')
    
    s = Solver()
    s.add((a + b) + c != a + (b + c))
    
    assert s.check() == unsat, "Associativity failed for integers"

def test_z3_associativity_real():
    """Formally verify associativity for real numbers."""
    a = Real('a')
    b = Real('b')
    c = Real('c')
    
    s = Solver()
    s.add((a + b) + c != a + (b + c))
    
    assert s.check() == unsat, "Associativity failed for real numbers"

def test_z3_identity_element_int():
    """Formally verify that 0 is the identity element for integers."""
    a = Int('a')
    
    s = Solver()
    s.add(a + 0 != a)
    
    assert s.check() == unsat, "0 is not identity element for integers"

def test_z3_identity_element_real():
    """Formally verify that 0 is the identity element for real numbers."""
    a = Real('a')
    
    s = Solver()
    s.add(a + 0 != a)
    
    assert s.check() == unsat, "0 is not identity element for real numbers"

def test_z3_additive_inverse_int():
    """Formally verify additive inverse property for integers."""
    a = Int('a')
    
    s = Solver()
    s.add(a + (-a) != 0)
    
    assert s.check() == unsat, "Additive inverse failed for integers"

def test_z3_additive_inverse_real():
    """Formally verify additive inverse property for real numbers."""
    a = Real('a')
    
    s = Solver()
    s.add(a + (-a) != 0)
    
    assert s.check() == unsat, "Additive inverse failed for real numbers"

def test_z3_distributivity_over_negation():
    """Formally verify that -(a + b) = (-a) + (-b)."""
    a = Real('a')
    b = Real('b')
    
    s = Solver()
    s.add(-(a + b) != (-a) + (-b))
    
    assert s.check() == unsat, "Distributivity over negation failed"

# ============================================================================
# ADDITIONAL EDGE CASE TESTS
# ============================================================================

def test_add_type_promotion():
    """Test that type promotion works correctly."""
    result = add(5, 3)
    assert isinstance(result, int)
    
    result = add(5, 3.0)
    assert isinstance(result, float)
    
    result = add(3.0, 5)
    assert isinstance(result, float)

def test_add_with_boolean_values():
    """Test addition with boolean values (True=1, False=0)."""
    assert add(True, True) == 2
    assert add(True, False) == 1
    assert add(False, False) == 0
    assert add(5, True) == 6

def test_add_with_none():
    """Test that None raises TypeError."""
    with pytest.raises(TypeError):
        add(None, 5)
    with pytest.raises(TypeError):
        add(5, None)

def test_add_infinity_combinations():
    """Test various combinations with infinity."""
    assert math.isinf(add(float('inf'), float('inf')))
    assert add(float('inf'), float('inf')) > 0
    assert math.isinf(add(float('-inf'), float('-inf')))
    assert add(float('-inf'), float('-inf')) < 0
    assert math.isnan(add(float('inf'), float('-inf')))

def test_add_negative_zero():
    """Test addition with negative zero."""
    assert add(-0.0, 5) == 5
    assert add(5, -0.0) == 5
    assert add(-0.0, -0.0) == -0.0

def test_add_very_large_integers():
    """Test with extremely large integers."""
    large_num = 10**1000
    assert add(large_num, large_num) == 2 * large_num
    assert add(large_num, -large_num) == 0

def test_add_precision_issues():
    """Test known floating point precision issues."""
    result = add(0.1, 0.2)
    assert result != 0.3  # Expected floating point behavior
    assert result == pytest.approx(0.3)

def test_add_scientific_notation():
    """Test addition with scientific notation."""
    assert add(1e3, 2e3) == 3000.0
    assert add(1.5e-3, 2.5e-3) == pytest.approx(4e-3)

def test_add_complex_numbers():
    """Test addition with complex numbers."""
    assert add(3 + 4j, 1 + 2j) == 4 + 6j
    assert add(5, 2 + 3j) == 7 + 3j

def test_comprehensive_addition_properties():
    """Comprehensive test of all mathematical properties."""
    test_values = [
        (0, 0), (1, 2), (-3, 5), (2.5, 3.7),
        (1e6, -1e6), (0.1, 0.2),
    ]
    
    for a, b in test_values:
        result = add(a, b)
        expected = a + b
        assert result == pytest.approx(expected), \
            f"add({a}, {b}) = {result}, expected {expected}"
        assert add(a, b) == pytest.approx(add(b, a)), \
            f"Commutativity failed for {a}, {b}"
        assert add(a, 0) == pytest.approx(a), \
            f"Identity failed for {a}"
        assert add(a, -a) == pytest.approx(0), \
            f"Additive inverse failed for {a}"

if __name__ == "__main__":
    pytest.main([__file__, "-v"])