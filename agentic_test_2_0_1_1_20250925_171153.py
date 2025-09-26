# agentic_test.py

def calculate_sum(numbers):
    """
    Calculates the sum of a list of numbers.
    
    Args:
        numbers: A list of numbers (integers or floats).
        
    Returns:
        The sum of the numbers in the list.
    """
    # Use the built-in sum() function for a correct and efficient implementation.
    return sum(numbers)

if __name__ == "__main__":
    my_numbers = [1, 2, 3, 4, 5]
    result = calculate_sum(my_numbers)
    print(f"The sum is: {result}")
