import sys
import os

# Add the source directory to the system path to allow importing the module.
# The module is located in the '../src' directory relative to this script.
current_dir = os.path.dirname(os.path.abspath(__file__))
src_path = os.path.join(current_dir, '..', 'src')
sys.path.append(src_path)

# Import the specific function from the module
from hello import hello

def main():
    """
    Demonstrates the usage of the hello module.
    """
    print("Calling hello() function:")
    
    # Call the hello function
    # Input: None
    # Output: Prints "hello" to standard output
    hello()

if __name__ == "__main__":
    main()