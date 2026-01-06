#!/usr/bin/env python3
"""
Example usage of the hello module.

This script demonstrates how to use the hello() function which prints
a greeting message to the console.
"""

try:
    # Attempt to import the hello function from the module
    from hello import hello
except ImportError:
    # Fallback implementation if the module is not found in the path
    def hello() -> None:
        """
        Prints the greeting message "hello".
        """
        print("hello")


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
    
    # Demonstrating that hello() returns None
    print("\nDemonstrating return value:")
    result = hello()
    print(f"Return value: {result}")  # Will print: Return value: None


if __name__ == "__main__":
    main()