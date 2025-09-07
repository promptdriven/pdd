"""
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