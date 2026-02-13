def fibonacci(n: int) -> int:
    """
    Compute the nth Fibonacci number using an iterative approach.
    
    Args:
        n (int): The index of the Fibonacci sequence to compute.
        
    Returns:
        int: The nth Fibonacci number.
    """
    if n == 0:
        return 0
    if n == 1:
        return 1
    
    a, b = 0, 1
    for _ in range(2, n + 1):
        a, b = b, a + b
    return b