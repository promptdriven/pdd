"""
Example usage and verification of the math_helper module.
This demonstrates correct usage of the divide_numbers function
and verifies it handles edge cases properly.
"""

from pdd.math_helper import divide_numbers, add_numbers, multiply_numbers

# Test normal division
result = divide_numbers(10, 2)
assert result == 5.0, f"Expected 5.0, got {result}"
print(f"✓ Normal division: 10 / 2 = {result}")

# Test float division
result = divide_numbers(7.5, 2.5)
assert result == 3.0, f"Expected 3.0, got {result}"
print(f"✓ Float division: 7.5 / 2.5 = {result}")

# Test negative division
result = divide_numbers(-10, 2)
assert result == -5.0, f"Expected -5.0, got {result}"
print(f"✓ Negative division: -10 / 2 = {result}")

# Test division by zero handling
try:
    divide_numbers(10, 0)
    raise AssertionError("Expected ValueError for division by zero")
except ValueError as e:
    assert "Cannot divide by zero" in str(e), f"Expected 'Cannot divide by zero' in error message, got: {e}"
    print(f"✓ Division by zero properly handled: {e}")

# Test division by float zero
try:
    divide_numbers(5.5, 0.0)
    raise AssertionError("Expected ValueError for division by float zero")
except ValueError as e:
    assert "Cannot divide by zero" in str(e), f"Expected 'Cannot divide by zero' in error message, got: {e}"
    print(f"✓ Division by float zero properly handled: {e}")

# Test other functions
result = add_numbers(5, 3)
assert result == 8, f"Expected 8, got {result}"
print(f"✓ Addition: 5 + 3 = {result}")

result = multiply_numbers(4, 3)
assert result == 12, f"Expected 12, got {result}"
print(f"✓ Multiplication: 4 * 3 = {result}")

print("\n✅ All verifications passed!")
