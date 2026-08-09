import sys
import os

# Import the comment_line function from the pdd.comment_line module
# The pdd directory is accessible in the python path
from pdd.comment_line import comment_line

def main():
    """
    Demonstrates how to use the comment_line function to comment out lines of code
    for different programming languages based on their comment syntax.
    """
    print("--- Comment Line Module Examples ---\n")

    # Example 1: Python-style single character comment
    # Inputs:
    #   - code_line: "print('Hello, World!')"
    #   - comment_characters: "#"
    # Output: "#print('Hello, World!')"
    py_code = "print('Hello, World!')"
    py_commented = comment_line(py_code, "#")
    print("Python Example:")
    print(f"  Original:  {py_code}")
    print(f"  Commented: {py_commented}\n")

    # Example 2: HTML-style encapsulating comment
    # Inputs:
    #   - code_line: "<h1>Hello World!</h1>"
    #   - comment_characters: "<!-- -->" (space indicates encapsulation)
    # Output: "<!--<h1>Hello World!</h1>-->"
    html_code = "<h1>Hello World!</h1>"
    html_commented = comment_line(html_code, "<!-- -->")
    print("HTML Example:")
    print(f"  Original:  {html_code}")
    print(f"  Commented: {html_commented}\n")

    # Example 3: Deletion style comment
    # Inputs:
    #   - code_line: "unsupported_syntax_code_here()"
    #   - comment_characters: "del"
    # Output: "" (an empty string, indicating line deletion)
    del_code = "unsupported_syntax_code_here()"
    del_commented = comment_line(del_code, "del")
    print("Deletion Example (for unsupported comment syntax):")
    print(f"  Original:  {del_code}")
    print(f"  Commented: '{del_commented}' (empty string)\n")

if __name__ == "__main__":
    main()