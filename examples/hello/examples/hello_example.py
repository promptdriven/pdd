import sys
import os

# Add the src directory containing the module to the Python path
module_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src')
sys.path.append(module_dir)

from hello import hello

def run_example() -> None:
    """
    Demonstrates how to use the hello function from the module.

    The hello function takes no input parameters and returns None.
    It prints a greeting message directly to the standard output.
    """
    print("--- Executing hello() from the module ---")

    # Call the imported function
    hello()

    print("--- Execution complete ---")

if __name__ == "__main__":
    run_example()
