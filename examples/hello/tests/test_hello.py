# TEST PLAN
#
# 1. Unit Tests:
#    - The primary functionality is printing to stdout. This is best tested with unit tests using output capturing (capsys fixture in pytest).
#    - Test Case 1: Verify that calling `hello()` results in "hello\n" being written to stdout.
#    - Test Case 2: Verify that the function returns None (as indicated by the type hint).
#
# 2. Z3 Formal Verification:
#    - The function `hello` is an imperative procedure with side effects (I/O) and no logical branching, mathematical computation, or state transformations.
#    - Z3 is a theorem prover best suited for verifying logical constraints, arithmetic properties, and state transitions.
#    - Since `hello` takes no input and performs no logic other than a side effect, there are no constraints to model or properties to prove formally.
#    - Therefore, Z3 verification is not applicable or beneficial for this specific function. We will rely solely on unit tests.

import sys
import os

# Add the src directory to the path so we can import the module
# The code under test is at: /Users/gregtanaka/Documents/pdd_cloud/pdd/examples/hello/src/hello.py
# The test file is at: /Users/gregtanaka/Documents/pdd_cloud/pdd/examples/hello/tests/test_hello.py
# We need to add the parent of the 'src' directory or the 'src' directory itself depending on package structure.
# Given the file path structure, adding the 'src' directory allows direct import of the module 'hello'.
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

import pytest
from hello import hello

def test_hello_output(capsys):
    """
    Verify that the hello function prints exactly "hello" followed by a newline to stdout.
    """
    # Act
    hello()
    
    # Assert
    captured = capsys.readouterr()
    assert captured.out == "hello\n"
    assert captured.err == ""

def test_hello_return_value():
    """
    Verify that the hello function returns None, adhering to its type hint.
    """
    # Act
    result = hello()
    
    # Assert
    assert result is None

def test_hello_idempotency(capsys):
    """
    Verify that calling the hello function multiple times produces consistent output each time.
    """
    # Act
    hello()
    hello()
    hello()
    
    # Assert
    captured = capsys.readouterr()
    # It should print "hello\n" three times
    assert captured.out == "hello\nhello\nhello\n"
    assert captured.err == ""