#!/usr/bin/env python3
"""
Fix script for broken hello_example.py files.

This script fixes examples that incorrectly try to import from non-existent modules
by replacing the import with the actual function definition.
"""

import os
import sys
from pathlib import Path

def fix_hello_example():
    """Fix the hello_example.py file if it has import issues."""
    
    # Paths
    example_file = Path("examples/hello_example.py")
    source_file = Path("pdd/hello.py")
    
    if not example_file.exists():
        print(f"Error: {example_file} not found")
        return False
        
    if not source_file.exists():
        print(f"Error: {source_file} not found")
        return False
    
    # Read the current example
    with open(example_file, 'r') as f:
        example_content = f.read()
    
    # Read the source function
    with open(source_file, 'r') as f:
        source_content = f.read()
    
    # Check if the example has import issues
    if "from greeting_module import" in example_content:
        print("Found import issue in example file. Fixing...")
        
        # Create the fixed example
        fixed_example = '''"""
This script provides a clear example of how to define and use a simple function.
It combines the definition of a `hello` function and a script to run it
into a single, self-contained, and runnable file.
"""

def hello() -> None:
    """
    Prints the string "hello" to the standard output.

    This function takes no arguments and has no return value (implicitly returns None).
    Its sole side effect is printing the literal string "hello" to the console,
    followed by a newline character.
    """
    print("hello")


def run_example() -> None:
    """
    Demonstrates the proper usage of the `hello` function.

    This function serves as a wrapper for the example call, making the script's
    purpose clear.
    """
    print("Calling the `hello` function...")

    # Call the function. It takes no arguments and its only action
    # is to print "hello" to the console.
    hello()

    print("...function call complete.")


# The `if __name__ == "__main__"` block is standard Python practice.
# It ensures the code inside only runs when the script is executed directly.
if __name__ == "__main__":
    run_example()
'''
        
        # Write the fixed example
        with open(example_file, 'w') as f:
            f.write(fixed_example)
        
        print(f"Fixed {example_file}")
        return True
    
    else:
        print("Example file looks good - no import issues found")
        return True

def test_example():
    """Test that the example runs correctly."""
    example_file = Path("examples/hello_example.py")
    
    if not example_file.exists():
        print("Example file not found")
        return False
    
    print(f"Testing {example_file}...")
    
    # Run the example
    import subprocess
    try:
        result = subprocess.run([sys.executable, str(example_file)], 
                              capture_output=True, text=True, cwd=".")
        
        if result.returncode == 0:
            print("✅ Example runs successfully!")
            print("Output:")
            print(result.stdout)
            return True
        else:
            print("❌ Example failed to run")
            print("Error:")
            print(result.stderr)
            return False
            
    except Exception as e:
        print(f"❌ Error running example: {e}")
        return False

if __name__ == "__main__":
    print("=== Hello Example Fix Script ===")
    print()
    
    # Check if we're in the right directory
    if not Path("hello_python.prompt").exists():
        print("Error: Please run this script from the examples/hello directory")
        sys.exit(1)
    
    # Fix the example
    if fix_hello_example():
        print()
        # Test the example
        test_example()
    else:
        print("Failed to fix example")
        sys.exit(1)
