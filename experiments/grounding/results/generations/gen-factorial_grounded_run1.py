def factorial(n):
    """
    Computes the factorial of a non-negative integer n.
    
    Args:
        n (int): The number to compute the factorial of.
        
    Returns:
        int: The factorial of n.
        
    Raises:
        ValueError: If n is a negative integer.
    """
    # Input validation
    if n < 0:
        raise ValueError("Factorial is not defined for negative numbers.")
    
    # Base case: 0! is 1
    if n == 0:
        return 1
    
    # Iterative calculation
    result = 1
    for i in range(1, n + 1):
        result *= i
        
    return result

if __name__ == "__main__":
    # Examples of usage:
    print(factorial(5))  # Output: 120
    print(factorial(0))  # Output: 1
    try:
        print(factorial(-1)) # Raises ValueError
    except ValueError as e:
        print(e)