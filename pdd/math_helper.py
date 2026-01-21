"""\nSimple math utility functions for PDD.\n"""

def divide_numbers(numerator, denominator):
    """\n    Divide two numbers.\n\n    Args:\n        numerator: The number to be divided\n        denominator: The number to divide by\n\    Returns:\n        The result of numerator / denominator\n\    Raises:\n        ValueError: If the denominator is zero.\n    """
    if denominator == 0 or denominator == 0.0:
        raise ValueError("Cannot divide by zero")
    return numerator / denominator

def add_numbers(a, b):
    """Add two numbers together."""
    return a + b

def multiply_numbers(a, b):
    """Multiply two numbers together."""
    return a * b
""