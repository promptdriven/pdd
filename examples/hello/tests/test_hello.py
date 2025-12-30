import sys
import os
import pytest
from unittest.mock import patch
import io

# Ensure the source directory is in the python path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

from hello import hello

"""
TEST PLAN:

1. Functional Testing (Unit Tests):
    - Case: Verify that calling hello() prints the exact string "hello" followed by a newline to stdout.
    - Strategy: Use 'unittest.mock.patch' to capture sys.stdout and assert the output.
    - Reason: This is a side-effect (I/O) operation. Unit tests with mocking are the standard and most effective way to verify console output.

2. Formal Verification (Z3):
    - Case: Verify the logical properties of the function.
    - Strategy: Since the function 'hello()' has no return value, no input parameters, and performs only I/O, it is a "pure side-effect" function. 
    - Z3 Analysis: Z3 is designed for proving properties about logic, arithmetic, and data structures. It cannot directly "verify" a print statement to a physical console. 
    - Formal Property: We can formally verify that the function exists and is callable without arguments. However, for this specific trivial implementation, a Z3 test would be an overkill/abstraction. We will include a placeholder Z3-style check to ensure the function signature remains consistent with expectations (arity 0).

3. Edge Cases:
    - Case: Unexpected arguments.
    - Strategy: Verify that calling the function with arguments raises a TypeError.
    - Reason: Python's runtime handles this, but it ensures the API contract is strictly followed.
"""

def test_hello_prints_correct_output():
    """
    Test that hello() prints 'hello' to the console.
    """
    with patch('sys.stdout', new=io.StringIO()) as fake_out:
        hello()
        # .strip() handles potential trailing newlines which print() adds by default
        assert fake_out.getvalue().strip() == "hello"

def test_hello_no_arguments():
    """
    Test that hello() can be called with no arguments without raising an exception.
    """
    try:
        hello()
    except TypeError:
        pytest.fail("hello() raised TypeError unexpectedly!")

def test_hello_argument_error():
    """
    Test that hello() raises a TypeError if an argument is passed.
    """
    with pytest.raises(TypeError):
        # hello() takes 0 positional arguments but 1 was given
        hello("unexpected_arg") # type: ignore

def test_hello_formal_signature_check():
    """
    A Z3-inspired formal check. 
    While Z3 is typically for logic, we use a symbolic-style check to verify 
    the function's interface properties (Arity).
    """
    import inspect
    from z3 import Int, Solver, unsat

    # Property: The number of required parameters must be 0.
    sig = inspect.signature(hello)
    params = list(sig.parameters.values())
    num_params = len(params)

    # Formalizing the requirement: num_params == 0
    s = Solver()
    p_count = Int('p_count')
    s.add(p_count == num_params)
    
    # We want to prove that p_count is always 0. 
    # We check if there is any case where p_count != 0.
    s.add(p_count != 0)
    
    result = s.check()
    # If 'unsat', it means there is no case where p_count != 0, thus p_count is always 0.
    assert result == unsat, f"Formal Verification Failed: Function signature has {num_params} parameters, expected 0."