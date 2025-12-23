import sys
import os

# Add the source directory to the system path to allow importing the module
# The module is located in ../src/ relative to this example file
current_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(current_dir, '..', 'src')
sys.path.append(src_dir)

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
    
    # Call the hello function
    # This function takes no arguments and returns None
    hello()

    print("--- Example completed ---")

if __name__ == "__main__":
    run_example()