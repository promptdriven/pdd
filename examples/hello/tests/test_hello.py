# test_hello.py
"""
Test suite for the 'hello' function.
"""

# Test Plan for the `hello` function
#
# The `hello` function is expected to perform a single action: print the exact
# string "hello" to the standard output, followed by a newline. It should
# take no arguments and return no value.
#
# 1. **Formal Verification (Z3/SMT Solvers):**
#    - The primary functionality of this function is an I/O side effect (printing
#      to stdout). Formal verification tools like Z3 are not well-suited for
#      verifying such side effects directly. They excel at proving properties
#      about algorithms, data structures, and logical constraints, none of
#      which are present in this simple function. Therefore, formal
#      verification will not be used, and we will rely entirely on robust unit tests.
#
# 2. **Unit Test Strategy:**
#    - We will use `pytest` to write the unit tests.
#    - The key challenge is to test the output sent to `sys.stdout`. We will use
#      the `capsys` fixture provided by `pytest` to capture standard output
#      and standard error. This fixture allows us to inspect what was printed
#      during the function's execution.
#
# 3. **Test Cases:**
#
#    - **test_hello_prints_correct_string:**
#      - **Purpose:** Verify that the function prints the exact string "hello"
#        followed by a newline to standard output. This is the primary success case.
#      - **Setup:** None.
#      - **Action:** Call the `hello()` function.
#      - **Assertion:**
#        - Capture the standard output.
#        - Assert that the captured output is exactly equal to "hello\n".
#
#    - **test_hello_prints_nothing_to_stderr:**
#      - **Purpose:** Ensure that the function does not produce any output on
#        the standard error stream. This confirms the absence of unexpected errors.
#      - **Setup:** None.
#      - **Action:** Call the `hello()` function.
#      - **Assertion:**
#        - Capture the standard error.
#        - Assert that the captured error stream is empty.
#
#    - **test_hello_returns_none:**
#      - **Purpose:** Confirm that the function has no return value (i.e., it
#        returns `None`), as specified by its type hint and common practice for
#        functions with only side effects.
#      - **Setup:** None.
#      - **Action:** Call the `hello()` function and capture its return value.
#      - **Assertion:**
#        - Assert that the return value is `None`.
#
#    - **test_hello_accepts_no_arguments:**
#      - **Purpose:** Verify that the function signature is correct and that it
#        raises a `TypeError` if called with any positional or keyword arguments.
#      - **Setup:** None.
#      - **Action:** Use `pytest.raises` to attempt calling `hello()` with an
#        argument.
#      - **Assertion:**
#        - Assert that a `TypeError` is raised.

import pytest
from hello import hello

def test_hello_prints_correct_string(capsys):
    """
    Verifies that the function prints the exact string "hello\n" to stdout.
    """
    hello()
    captured = capsys.readouterr()
    assert captured.out == "hello\n", "The output to stdout should be exactly 'hello' followed by a newline."

def test_hello_prints_nothing_to_stderr(capsys):
    """
    Verifies that the function does not print anything to stderr.
    """
    hello()
    captured = capsys.readouterr()
    assert captured.err == "", "The output to stderr should be empty."

def test_hello_returns_none(capsys):
    """
    Verifies that the function returns None.
    The capsys fixture is used here to prevent the function's output from
    cluttering the test results console.
    """
    return_value = hello()
    assert return_value is None, "The function should return None."

def test_hello_accepts_no_arguments():
    """
    Verifies that calling the function with arguments raises a TypeError.
    """
    with pytest.raises(TypeError):
        hello("some_argument")

    with pytest.raises(TypeError):
        hello(arg="some_keyword_argument")