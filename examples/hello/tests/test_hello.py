# TEST PLAN
# -----------------------------------------------------------------------------
# 1. Unit Tests (Pytest)
#    The primary functionality of this code is side-effect based (printing to stdout).
#    Unit tests are the most appropriate tool here because we need to capture and 
#    verify I/O operations, which formal verification tools like Z3 are not 
#    typically designed for.
#
#    Test Cases:
#    - test_hello_output: Verify that calling hello() captures "hello\n" in stdout.
#    - test_hello_return_value: Verify that the function returns None (as per type hint).
#
# 2. Formal Verification (Z3)
#    Z3 is a theorem prover used for verifying logical constraints, mathematical 
#    properties, and state transitions.
#    
#    Applicability to this code:
#    - The `hello` function has no input parameters, no return value logic, no 
#      branching paths, and performs no mathematical operations.
#    - It is a pure side-effect function (I/O).
#    - Therefore, Z3 is NOT applicable or useful for this specific function. 
#      Attempting to model "printing to stdout" in Z3 would be an abstraction 
#      that doesn't prove anything about the actual Python runtime behavior.
#    
#    Decision: No Z3 tests will be generated as there are no logical constraints to solve.
# -----------------------------------------------------------------------------

import sys
import os
import pytest
from io import StringIO

# Add the source directory to sys.path to allow importing the module
# The code is located at: /Users/gregtanaka/Documents/pdd_cloud/pdd/examples/hello/src/hello.py
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

import hello

def test_hello_output(capsys):
    """
    Verify that the hello function prints exactly "hello" followed by a newline to stdout.
    Using capsys fixture from pytest to capture stdout.
    """
    # Act
    hello.hello()
    
    # Assert
    captured = capsys.readouterr()
    assert captured.out == "hello\n"
    assert captured.err == ""

def test_hello_return_value():
    """
    Verify that the hello function returns None, adhering to its type hint -> None.
    """
    # Act
    result = hello.hello()
    
    # Assert
    assert result is None