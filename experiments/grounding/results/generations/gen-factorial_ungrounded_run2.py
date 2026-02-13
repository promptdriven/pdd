def factorial(n):
    """
    Compute the factorial of a non-negative integer n.

    Args:
        n (int): A non-negative integer.

    Returns:
        int: The factorial of n (n!).

    Raises:
        ValueError: If n is negative.
        TypeError: If n is not an integer.
    """
    # Type validation
    if not isinstance(n, int):
        raise TypeError(f"Expected an integer, got {type(n).__name__}")

    # Input validation for negative numbers
    if n < 0:
        raise ValueError(f"Factorial is not defined for negative numbers (got {n})")

    # Base cases
    if n == 0 or n == 1:
        return 1

    # Iterative computation
    result = 1
    for i in range(2, n + 1):
        result *= i

    return result


# ---------- Demo / Testing ----------
if __name__ == "__main__":
    # Normal cases
    print(f"factorial(0) = {factorial(0)}")   # 1
    print(f"factorial(1) = {factorial(1)}")   # 1
    print(f"factorial(5) = {factorial(5)}")   # 120
    print(f"factorial(10) = {factorial(10)}") # 3628800

    # Edge case: negative input
    try:
        factorial(-3)
    except ValueError as e:
        print(f"\nValueError caught: {e}")

    # Edge case: non-integer input
    try:
        factorial(4.5)
    except TypeError as e:
        print(f"TypeError caught: {e}")