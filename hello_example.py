"""
Example usage of the `hello` function.

This script demonstrates how to import and execute the `hello` function
from a module.
"""

# Assume the provided `hello` function is saved in a file named `greetings.py`.
# To use the function, you must first import it from its module.
from greetings import hello


def def main() -> None:
    """
    Main function to demonstrate a call to the hello() function.

    This function serves as the entry point for the example. It calls the
    imported `hello` function to show its effect.

    Args:
        None

    Returns:
        None
    """
    print("--- Calling the hello() function ---")

    # Call the function. It takes no arguments and its action is to print
    # "hello" to the console.
    hello()

    print("--- Function call complete ---")

    # The function does not return a value, so assigning its result to a
    # variable will store `None`.
    result = hello()
    print(f"The return value of hello() is: {result}")


# Standard practice to make the script executable.
if __name__ == "__main__":
    main()

# --- Expected Console Output ---
# --- Calling the hello() function ---
# hello
# --- Function call complete ---
# hello
# The return value of hello() is: None
