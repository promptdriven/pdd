import sys
import os

# Add the src directory to the system path to allow importing the hello module
# This ensures the example is portable and can find the module relative to this script's location
current_dir = os.path.dirname(os.path.abspath(__file__))
src_path = os.path.join(current_dir, "..", "src")
sys.path.append(src_path)

from hello import hello

def run_example():
    """
    Demonstrates the usage of the hello function from the hello module.

    Input Parameters:
        None

    Output:
        Prints "hello" to the standard output.
    """
    print("--- Running hello() example ---")
    
    # Call the imported function
    hello()

    print("--- Example completed ---")

if __name__ == "__main__":
    run_example()