"""
Example demonstrating how a standard setup.py script behaves.

In Python packaging, `setup.py` is typically invoked from the command line
rather than imported as a module. However, because it contains a module-level
call to `setuptools.setup()`, importing it directly will execute the setup process
based on the current `sys.argv`.

This example mocks `sys.argv` to safely query the package version and name
by importing the `setup` module, demonstrating its configuration without
triggering a full installation or build process.
"""

import sys
import os
import contextlib
import io

def main():
    """
    Demonstrates querying metadata from setup.py by mocking command-line arguments.
    """
    print("Demonstrating setup.py behavior...")
    
    # Save original arguments
    original_argv = sys.argv.copy()
    
    # Example 1: Query the package version
    print("\n--- Querying Package Version ---")
    sys.argv = ["setup.py", "--version"]
    
    # We capture stdout to prevent setup.py from writing directly to the console
    # if we wanted to process the output, but here we just let it print.
    try:
        # Importing the module executes the setup() function call at the module level
        import pdd.setup
    except SystemExit as e:
        # setuptools naturally calls sys.exit() after processing commands like --version
        print(f"setup.py finished version query with exit code: {e.code}")
        
    # To run a second query, we would need to reload the module since it's already cached in sys.modules
    print("\n--- Querying Package Name ---")
    sys.argv = ["setup.py", "--name"]
    
    import importlib
    try:
        importlib.reload(sys.modules['pdd.setup'])
    except SystemExit as e:
        print(f"setup.py finished name query with exit code: {e.code}")

    # Restore original arguments
    sys.argv = original_argv
    print("\nSetup demonstration complete.")

if __name__ == "__main__":
    main()