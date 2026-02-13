def fibonacci(n):
    """
    Returns the nth Fibonacci number using an iterative approach.
    
    The Fibonacci sequence: 0, 1, 1, 2, 3, 5, 8, 13, 21, ...
    
    Args:
        n (int): The position in the Fibonacci sequence (0-indexed).
        
    Returns:
        int: The nth Fibonacci number.
        
    Raises:
        ValueError: If n is a negative integer.
        TypeError: If n is not an integer.
    """
    # --- Input Validation ---
    if not isinstance(n, int):
        raise TypeError(f"Expected an integer, got {type(n).__name__}")
    if n < 0:
        raise ValueError(f"n must be a non-negative integer, got {n}")

    # --- Edge Cases ---
    if n == 0:
        return 0
    if n == 1:
        return 1

    # --- Iterative Calculation ---
    prev, curr = 0, 1
    for _ in range(2, n + 1):
        prev, curr = curr, prev + curr

    return curr


# ---------- Demo / Testing ----------
if __name__ == "__main__":
    # Expected output for the first 10 Fibonacci numbers
    # n:   0  1  2  3  4  5  6   7   8   9
    # F:   0  1  1  2  3  5  8  13  21  34

    print("First 10 Fibonacci numbers:")
    for i in range(10):
        print(f"  fibonacci({i}) = {fibonacci(i)}")

    # Edge case tests
    print("\nEdge case tests:")
    print(f"  fibonacci(0)  = {fibonacci(0)}")   # 0
    print(f"  fibonacci(1)  = {fibonacci(1)}")   # 1
    print(f"  fibonacci(20) = {fibonacci(20)}")  # 6765

    # Error handling tests
    print("\nError handling tests:")
    try:
        fibonacci(-1)
    except ValueError as e:
        print(f"  fibonacci(-1) -> ValueError: {e}")

    try:
        fibonacci(3.5)
    except TypeError as e:
        print(f"  fibonacci(3.5) -> TypeError: {e}")