# Placeholder for split command script 

def add(a, b):
    """Adds two numbers, performing basic type checking first."""
    if not isinstance(a, (int, float)):
        raise TypeError("Input 'a' must be a number")
    if not isinstance(b, (int, float)):
        raise TypeError("Input 'b' must be a number")
    return a + b 