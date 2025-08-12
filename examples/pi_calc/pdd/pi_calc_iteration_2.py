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