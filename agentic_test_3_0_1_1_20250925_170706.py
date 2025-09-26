# agentic_test.py

def calculate_sum(numbers):
    """
    Calculates the sum of a list of numbers.
    
    Args:
        numbers: A list of numbers (integers or floats).
        
    Returns:
        The sum of the numbers in the list.
    """
    # Initialize an accumulator variable to store the sum.
    total = 0
    # Iterate over each number in the list and add it to the total.
    for number in numbers:
        total += number
    # Return the final sum.
    return total

if __name__ == "__main__":
    my_numbers = [1, 2, 3, 4, 5]
    result = calculate_sum(my_numbers)
    print(f"The sum is: {result}")
