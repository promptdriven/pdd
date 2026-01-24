"""
Module: simple_math
A simple math module with basic arithmetic operations.
"""

from typing import Union


def add(a: Union[int, float], b: Union[int, float]) -> Union[int, float]:
    """
    Return the sum of two numbers.
    
    Args:
        a: First number (int or float)
        b: Second number (int or float)
    
    Returns:
        The sum of a and b. Returns float when mixing int and float,
        otherwise returns the appropriate type.
    
    Examples:
        >>> add(2, 3)
        5
        >>> add(2.5, 3.5)
        6.0
        >>> add(2, 3.5)
        5.5
    """
    return a + b


if __name__ == "__main__":
    # Demonstrate usage with various inputs
    test_cases = [
        (2, 3),          # int + int
        (2.5, 3.5),      # float + float
        (2, 3.5),        # int + float
        (2.5, 3),        # float + int
        (0, 0),          # zeros
        (-5, 10),        # negative + positive
        (3.14, -2.71),   # float with negative
    ]
    
    print("Testing add() function:")
    print("-" * 40)
    
    for a, b in test_cases:
        result = add(a, b)
        result_type = type(result).__name__
        print(f"add({a!r}, {b!r}) = {result!r}  (type: {result_type})")
    
    print("-" * 40)
    print("All tests completed! # Added comment for update test")