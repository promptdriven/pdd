import sys
import os

# Add the parent directory to sys.path to allow importing the calculator module
# This ensures the script can find 'calculator.py' located in the parent directory
current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(current_dir)
sys.path.append(parent_dir)

from calculator import add_numbers

def main():
    """
    Demonstrates the usage of the add_numbers function from the calculator module.
    
    Input Parameters for add_numbers:
        a (float): The first numerical value to be added.
        b (float): The second numerical value to be added.

    Output:
        returns (float): The arithmetic sum of parameters a and b.
    """
    # Define input values
    num1 = 10.5
    num2 = 4.2

    # Call the function from the calculator module
    total = add_numbers(num1, num2)

    # Display the result
    print(f"Input A: {num1}")
    print(f"Input B: {num2}")
    print(f"Result of add_numbers: {total}")

if __name__ == "__main__":
    main()