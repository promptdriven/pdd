"""Module: simple_math
A tiny arithmetic module with a single add() helper and a runnable demo."""

from typing import Union


def add(a: Union[int, float], b: Union[int, float]) -> Union[int, float]:
    """Add two numbers together.

    Args:
        a: First number.
        b: Second number.

    Returns:
        The sum of a and b.

    >>> add(2, 3)
    5
    >>> add(2.5, 3.5)
    6.0
    >>> add(2, 3.5)
    5.5
    """
    return a + b


if __name__ == "__main__":
    test_cases = [(2, 3), (2.5, 3.5), (2, 3.5), (2.5, 3), (0, 0), (-5, 10), (3.14, -2.71)]
    print("Testing add() function:")
    print("-" * 40)
    for a, b in test_cases:
        result = add(a, b)
        print(f"add({a!r}, {b!r}) = {result!r}  (type: {type(result).__name__})")
    print("-" * 40)
    print("All tests completed!")
