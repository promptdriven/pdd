# TEST PLAN:
# 1. Unit Test - Standard Output Verification:
#    - Goal: Verify that the function prints exactly "hello" to stdout.
#    - Method: Use pytest's `capsys` fixture to capture stdout and assert the content.
#    - Rationale: This is the primary functionality requested in the prompt.
#
# 2. Unit Test - Return Value Verification:
#    - Goal: Verify that the function returns None (as indicated by the type hint -> None).
#    - Method: Call the function and assert the return value is None.
#    - Rationale: Ensures adherence to the function signature.
#
# 3. Z3 Formal Verification:
#    - Goal: Verify logical properties of the output string.
#    - Method: While Z3 is typically used for complex logic, constraint solving, or mathematical proofs, 
#      we can demonstrate its usage here by verifying properties of the string "hello" (e.g., length is 5, 
#      contains specific characters).
#    - Rationale: Although overkill for a simple print statement, it demonstrates how to integrate 
#      formal verification into the test suite. We will model the output string as a sequence of characters 
#      and verify constraints.

import sys
import os
import pytest
from z3 import Solver, String, StringVal, Length, Int

# Add the source directory to the path so we can import the module
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

from hello import hello

def test_hello_output(capsys):
    """
    Verifies that the hello function prints 'hello' to stdout.
    """
    # Act
    hello()
    
    # Assert
    captured = capsys.readouterr()
    # We expect "hello" followed by a newline because print() adds one by default
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

def test_hello_z3_string_properties(capsys):
    """
    Uses Z3 to formally verify properties of the output string.
    We verify that the output (stripped of whitespace) matches the string "hello".
    """
    # Act
    hello()
    captured = capsys.readouterr()
    actual_output = captured.out.strip()

    # Z3 Setup
    s = Solver()
    
    # Define a Z3 String variable representing the output
    z3_output = String('output')
    
    # Add constraint: The Z3 string variable must equal the actual python string we got
    s.add(z3_output == StringVal(actual_output))
    
    # Formal Verification 1: Length must be 5
    s.add(Length(z3_output) == 5)
    
    # Formal Verification 2: The string must be equal to "hello"
    s.add(z3_output == StringVal("hello"))
    
    # Check if these constraints are satisfiable
    result = s.check()
    
    # Assert that the solver found a solution (meaning our output satisfies the constraints)
    assert str(result) == 'sat', "The output string did not satisfy the formal constraints (length 5, content 'hello')"

# TEST PLAN:
# 1. Unit Test - Standard Output Verification:
#    - Goal: Verify that the function prints exactly "hello" to stdout.
#    - Method: Use pytest's `capsys` fixture to capture stdout and assert the content.
#    - Rationale: This is the primary functionality requested in the prompt.
#
# 2. Unit Test - Return Value Verification:
#    - Goal: Verify that the function returns None (as indicated by the type hint -> None).
#    - Method: Call the function and assert the return value is None.
#    - Rationale: Ensures adherence to the function signature.
#
# 3. Z3 Formal Verification:
#    - Goal: Verify logical properties of the output string.
#    - Method: While Z3 is typically used for complex logic, constraint solving, or mathematical proofs, 
#      we can demonstrate its usage here by verifying properties of the string "hello" (e.g., length is 5, 
#      contains specific characters).
#    - Rationale: Although overkill for a simple print statement, it demonstrates how to integrate 
#      formal verification into the test suite. We will model the output string as a sequence of characters 
#      and verify constraints.

import sys
import os
import pytest
from z3 import Solver, String, StringVal, Length, Int

# Add the source directory to the path so we can import the module
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

from hello import hello

def test_hello_output(capsys):
    """
    Verifies that the hello function prints 'hello' to stdout.
    """
    # Act
    hello()
    
    # Assert
    captured = capsys.readouterr()
    # We expect "hello" followed by a newline because print() adds one by default
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

def test_hello_z3_string_properties(capsys):
    """
    Uses Z3 to formally verify properties of the output string.
    We verify that the output (stripped of whitespace) matches the string "hello".
    """
    # Act
    hello()
    captured = capsys.readouterr()
    actual_output = captured.out.strip()

    # Z3 Setup
    s = Solver()
    
    # Define a Z3 String variable representing the output
    z3_output = String('output')
    
    # Add constraint: The Z3 string variable must equal the actual python string we got
    s.add(z3_output == StringVal(actual_output))
    
    # Formal Verification 1: Length must be 5
    s.add(Length(z3_output) == 5)
    
    # Formal Verification 2: The string must be equal to "hello"
    s.add(z3_output == StringVal("hello"))
    
    # Check if these constraints are satisfiable
    result = s.check()
    
    # Assert that the solver found a solution (meaning our output satisfies the constraints)
    assert str(result) == 'sat', "The output string did not satisfy the formal constraints (length 5, content 'hello')"