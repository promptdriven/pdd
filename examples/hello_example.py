#!/usr/bin/env python3
"""
A complete, runnable example of how to use the `hello` function from the `hello` module.

This script demonstrates the necessary steps to import and execute a function
from a module located in a different directory, as per the specified file paths.
"""

import os
import sys

def main():
    """
    Sets up the system path, imports the `hello` function, and executes it.

    This function handles the dynamic modification of Python's import path
    to locate the `hello.py` module and then calls the `hello()` function
    to demonstrate its usage.
    """
    print("--- Running example for 'hello' module ---")

    # To import the 'hello' module, we must first add its containing directory
    # to Python's system path. The script needs to resolve the relative paths.
    #
    # Assumed file structure:
    # /Users/shrenyamathur/pdd-1/examples/
    #   ├── hello_example.py  (this script)
    #   └── hello/
    #       └── pdd/
    #           └── hello.py      (the module to import)
    #
    # We need to add '/Users/shrenyamathur/pdd-1/examples/hello/pdd' to the path.

    try:
        # Get the absolute path of the directory containing this example script.
        example_dir = os.path.dirname(os.path.abspath(__file__))

        # Construct the full path to the directory containing the 'hello.py' module.
        module_dir = os.path.join(example_dir, "hello", "pdd")

        # Add the module's directory to the beginning of the system path.
        sys.path.insert(0, module_dir)

        # Now that the path is configured, we can import the function.
        # This imports the 'hello' function directly from the 'hello.py' module.
        from hello import hello

        print("\nSuccessfully imported the 'hello' function.")
        print("Calling the function now...")
        print("Expected output:\nhello\n" + "-"*20)

        # Call the imported function.
        # It takes no arguments and will print "hello" to the console.
        hello()

        print("-"*20)
        print("Example finished successfully.")

    except ImportError:
        print("\nError: Could not import the 'hello' module.")
        print(f"Please ensure that 'hello.py' exists at: {os.path.join(module_dir, 'hello.py')}")
        sys.exit(1)
    except Exception as e:
        print(f"\nAn unexpected error occurred: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
