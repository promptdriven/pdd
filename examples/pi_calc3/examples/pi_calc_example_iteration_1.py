import math

def pi_calc(n_terms: int = 100000) -> float:
    """
    Calculates an approximation of Pi using the Nilakantha series.

    The Nilakantha series is an infinite series for calculating Pi which converges
    more quickly than other methods like the Leibniz formula. The formula is:
    
    Pi = 3 + 4/(2*3*4) - 4/(4*5*6) + 4/(6*7*8) - 4/(8*9*10) + ...

    The accuracy of the result improves as the number of terms increases.

    Args:
        n_terms (int, optional): The number of terms from the series to use for
                                 the calculation. Must be a non-negative integer.
                                 Defaults to 100,000, which provides a good
                                 approximation.

    Returns:
        float: An approximation of Pi. For comparison, `math.pi` is approximately
               3.141592653589793.

    Raises:
        TypeError: If `n_terms` is not an integer.
        ValueError: If `n_terms` is a negative number.
    """
    if not isinstance(n_terms, int):
        raise TypeError("The number of terms must be an integer.")
    if n_terms < 0:
        raise ValueError("The number of terms cannot be negative.")

    pi_approximation = 3.0
    sign = 1.0

    for i in range(1, n_terms + 1):
        # The denominator for the i-th term in the series
        # For i=1: 2*3*4
        # For i=2: 4*5*6
        # etc.
        denominator = (2.0 * i) * (2.0 * i + 1.0) * (2.0 * i + 2.0)
        
        # Add or subtract the term from the total
        pi_approximation += sign * (4.0 / denominator)
        
        # Flip the sign for the next term
        sign *= -1.0
        
    return pi_approximation

# --- Example Usage ---

if __name__ == "__main__":
    print("--- Demonstrating the pi_calc function ---")
    print(f"Value of math.pi for comparison: {math.pi}\n")

    # 1. Basic usage with default parameters
    # Calling the function without arguments uses the default n_terms=100,000.
    print("1. Calculating Pi with default number of terms (100,000):")
    pi_approximation_default = pi_calc()
    print(f"   Approximation: {pi_approximation_default}\n")

    # 2. Custom usage with a specified number of terms
    # A smaller number of terms results in a less accurate approximation.
    print("2. Calculating Pi with a small number of terms (10):")
    pi_approximation_small = pi_calc(n_terms=10)
    print(f"   Approximation: {pi_approximation_small}\n")

    # 3. High-precision usage
    # A larger number of terms results in a more accurate approximation.
    print("3. Calculating Pi with a large number of terms (1,000,000):")
    pi_approximation_large = pi_calc(n_terms=1000000)
    print(f"   Approximation: {pi_approximation_large}\n")

    # 4. Handling expected errors
    # The function raises specific errors for invalid input, which can be caught.
    print("4. Demonstrating error handling for invalid input:")
    
    # Example of catching a ValueError for negative input
    try:
        print("   - Attempting to use a negative number of terms...")
        pi_calc(n_terms=-50)
    except ValueError as e:
        print(f"     Successfully caught expected error: {e}\n")

    # Example of catching a TypeError for non-integer input
    try:
        print("   - Attempting to use a non-integer (float) for terms...")
        pi_calc(n_terms=100.5)
    except TypeError as e:
        print(f"     Successfully caught expected error: {e}")