def factorial(n):
    # Convert input to integer if it's a string
    try:
        n = int(n)
    except ValueError:
        raise ValueError("Input must be an integer or a string representing an integer.")

    # Check for non-negative integer
    if n < 0:
        raise ValueError("Factorial is not defined for negative numbers.")

    # Base case
    if n == 0:
        return 1
    # Recursive case
    return n * factorial(n - 1)