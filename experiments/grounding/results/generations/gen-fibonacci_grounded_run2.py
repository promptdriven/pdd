def fibonacci(n: int) -> int:
    """
    Returns the nth Fibonacci number using an iterative approach.

    The Fibonacci sequence is defined as:
    F(0) = 0, F(1) = 1, and F(n) = F(n-1) + F(n-2) for n > 1.

    Parameters:
    n (int): The position in the Fibonacci sequence.

    Returns:
    int: The nth Fibonacci number.

    Raises:
    TypeError: If n is not an integer.
    ValueError: If n is a negative integer.
    """
    # Strict type checking (excluding bool which is a subclass of int)
    if not isinstance(n, int) or isinstance(n, bool):
        raise TypeError("Input must be an integer.")
    
    if n < 0:
        raise ValueError("Input must be a non-negative integer.")

    # Handle edge cases for n=0 and n=1
    if n == 0:
        return 0
    if n == 1:
        return 1

    # Iterative approach
    a, b = 0, 1
    for _ in range(2, n + 1):
        a, b = b, a + b
    
    return b

# Example usage:
# print(fibonacci(10))  # Output: 55