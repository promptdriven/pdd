import sys
import os

# The program is in examples/, the module is in src/
# We need to go up one level from examples/ to the project root, then into src/
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.dirname(current_dir)
src_dir = os.path.join(project_root, "src")

# Add the src directory to the Python path
sys.path.append(src_dir)

# Import hello from the hello.py file
from hello import hello

def main() -> None: 
    """
    Demonstrates how to import and call the hello function from the module.

    Input Parameters:
    - None

    Output:
    - Prints 'hello' to the standard output.
    """
    print("Calling the hello function from the imported module:")
    
    # Execute the function defined in the module
    hello()

if __name__ == "__main__":
    main()