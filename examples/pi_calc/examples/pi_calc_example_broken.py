import math

def pi_calc(n_terms: int = 100000) -> float:
    """
    Calculates an approximation of Pi using the Nilakantha series.
    """
    if not isinstance(n_terms, int):
        raise TypeError("The number of terms must be an integer.")
    if n_terms < 0:
        raise ValueError("The number of terms cannot be negative.")

    pi_approximation = 3.0
    sign = 1.0

    for i in range(1, n_terms + 1):
        denominator = (2.0 * i) * (2.0 * i + 1.0) * (2.0 * i + 2.0)
        pi_approximation += sign * (4.0 / denominator)
        sign *= -1.0
        
    return pi_approximation

# --- Example Usage ---

if __name__ == "__main__":
    print("--- Demonstrating the pi_calc function ---")
    # This line has a syntax error - unterminated f-string
    print(f"Value of math.pi for comparison: {math.pi}
")
    
    print("1. Calculating Pi with default number of terms (100,000):")
    pi_approximation_default = pi_calc()
    # Another syntax error - unterminated f-string  
    print(f"   Approximation: {pi_approximation_default}
")