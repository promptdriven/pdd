import sys
import os

# Add the project root directory to the Python path to allow importing the module.
# The module is located at ../../pdd/simple_math.py relative to this script.
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, "..", "..", "pdd"))
sys.path.insert(0, project_root)

# Import the specific function from the module
from simple_math import add

def main():
    """
    Demonstrates the usage of the `add` function from the `simple_math` module.
    """
    
    # Example 1: Adding two integers
    num1 = 10
    num2 = 5
    result_int = add(num1, num2)
    print(f"Adding integers: {num1} + {num2} = {result_int}")
    # Expected Output: Adding integers: 10 + 5 = 15

    # Example 2: Adding two floating point numbers
    float1 = 10.5
    float2 = 2.3
    result_float = add(float1, float2)
    print(f"Adding floats: {float1} + {float2} = {result_float}")
    # Expected Output: Adding floats: 10.5 + 2.3 = 12.8

    # Example 3: Adding negative numbers
    neg1 = -7
    neg2 = 3
    result_neg = add(neg1, neg2)
    print(f"Adding with negative: {neg1} + {neg2} = {result_neg}")
    # Expected Output: Adding with negative: -7 + 3 = -4

if __name__ == "__main__":
    main()