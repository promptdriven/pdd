# TEST PLAN
# -----------------------------------------------------------------------------
# 1. Unit Tests:
#    The function `hello()` is a simple side-effect function that prints to stdout.
#    Since it has no return value and no complex logic, unit tests capturing stdout
#    are the most appropriate way to verify its correctness.
#
#    Test Cases:
#    - Verify that calling `hello()` prints exactly "hello\n" to stdout.
#    - Verify that the function returns None (implicit return).
#
# 2. Z3 Formal Verification:
#    Z3 is typically used for verifying logical constraints, mathematical properties,
#    or state transitions. The `hello` function is purely imperative (I/O) with no
#    internal logic, branching, or mathematical computation.
#    Therefore, Z3 is not applicable or useful for this specific function.
#    We will include a placeholder test to acknowledge this analysis.
# -----------------------------------------------------------------------------

import sys
import os
import pytest
from io import StringIO

# Add the directory containing the module to the Python path to ensure imports work correctly
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from hello import hello

def test_hello_output(capsys):
    """
    Verifies that the hello function prints 'hello' to the standard output.
    Using capsys fixture from pytest to capture stdout.
    """
    # Act
    hello()
    
    # Assert
    captured = capsys.readouterr()
    assert captured.out == "hello\n"
    assert captured.err == ""

def test_hello_return_value():
    """
    Verifies that the hello function returns None.
    """
    # Act
    result = hello()
    
    # Assert
    assert result is None

def test_z3_verification_not_applicable():
    """
    Formal verification using Z3 is not applicable for this function.
    
    Reasoning:
    The function `hello()` performs a side effect (I/O) and contains no 
    mathematical logic, constraints, or state transitions that Z3 is designed to solve.
    """
    pass