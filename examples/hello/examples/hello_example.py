#!/usr/bin/env python3
"""
Example usage of the hello module.

This script demonstrates how to use the hello() function which prints
a greeting message to the console.

File Structure (relative to project root):
    - Module location: same directory or Python path
    - Example location: same directory or examples folder

Functions demonstrated:
    hello() -> None
        Prints the string "hello" to the console.
        
        Parameters:
            None
            
        Returns:
            None - This function only produces console output.
            
        Side Effects:
            Outputs "hello" followed by a newline to stdout.
"""

# Import the hello function
# If the module is in the same directory or Python path:
from hello import hello


def main() -> None:
    """
    Main function demonstrating the usage of hello().
    
    The hello() function takes no arguments and returns nothing.
    It simply prints the word "hello" to the console.
    """
    
    # Basic usage - call hello() to print "hello"
    print("Calling hello():")
    hello()
    
    # The function can be called multiple times
    print("\nCalling hello() three times:")
    for i in range(3):
        hello()
    
    # Since hello() returns None, we can verify this
    print("\nVerifying return value:")
    result = hello()
    print(f"Return value: {result}")  # Will print: Return value: None


if __name__ == "__main__":
    main()