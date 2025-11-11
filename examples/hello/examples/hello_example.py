#!/usr/bin/env python3
"""
This script provides a complete, runnable example of how to use the 'hello'
function from the 'hello' module.

To make the 'hello' module importable, this script dynamically adds the 'src'
directory (which contains 'hello.py') to the system's path. This is a common
pattern when an example script is in a separate directory from the source code.
"""

import os
import sys

def main():
    """
    Demonstrates the usage of the hello() function.

    This main function imports the `hello` function from the sibling `src`
    directory and calls it to print a greeting to the console.
    """
    # --- Path Setup ---
    # This section is necessary to ensure the script can find the 'hello' module.
    # It adds the 'src' directory, which is a sibling to the 'examples'
    # directory, to the Python path.

    # Get the absolute path to the directory containing this script (examples/).
    current_dir = os.path.dirname(os.path.abspath(__file__))
    # Get the path to the parent directory (project root).
    project_root = os.path.dirname(current_dir)
    # Construct the path to the 'src' directory.
    src_path = os.path.join(project_root, "src")
    # Add the 'src' directory to the system path.
    sys.path.insert(0, src_path)

    # --- Module Import ---
    # Now that the 'src' directory is in the path, we can import the 'hello'
    # function from the 'hello.py' module.
    try:
        from hello import hello
    except ImportError:
        print(f"Error: Could not import the 'hello' module.")
        print(f"Please ensure 'hello.py' exists in the '{src_path}' directory.")
        sys.exit(1)

    # --- Function Usage ---
    print("Calling the imported 'hello()' function...")

    # Call the function. It will print "hello" to the console.
    # The hello() function is defined as:
    # def hello():
    #   """
    #   This function takes no arguments and prints the string "hello" to the console.
    #   """
    #   print("hello")
    hello()

    print("\nExample finished.")

if __name__ == "__main__":
    main()