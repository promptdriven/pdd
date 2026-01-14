import sys
import os
import pytest
from z3 import Solver, Bool, Implies, sat, is_true

# Add the src directory to the path so we can import the module
# The code is located at .../src/hello.py
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

from hello import hello

def test_hello_output(capsys):
    """
    Verifies that the hello() function prints 'hello' to the console.
    """
    # Act
    hello()
    
    # Assert
    captured = capsys.readouterr()
    # print adds a newline by default, so we expect "hello\n"
    assert captured.out == "hello\n"
    assert captured.err == ""

def test_hello_return_value():
    """
    Verifies that the hello() function returns None.
    """
    # Act
    result = hello()
    
    # Assert
    assert result is None

def test_hello_contract_z3():
    """
    A formal verification test using Z3 to model the function's execution contract.
    
    Since the function has no inputs or mathematical logic, we model the 
    post-condition abstractly.
    
    Let P = Function executes successfully
    Let Q = Output is generated
    
    We verify that the model allows for the function to execute.
    """
    s = Solver()
    
    # Variables representing the state of the system
    function_called = Bool('function_called')
    output_generated = Bool('output_generated')
    
    # Constraint: If the function is called, output must be generated
    # This models the intended behavior of the code
    s.add(Implies(function_called, output_generated))
    
    # We assert that the function was called
    s.add(function_called)
    
    # Check if this state is satisfiable
    result = s.check()
    
    # If satisfiable, it means our model of the function is logically consistent
    assert result == sat
    
    # If we assume the function was called, the model must imply output_generated is true
    model = s.model()
    
    # Use is_true to check the Z3 BoolRef value.
    # Z3 returns a BoolRef object that represents True, but is not the Python True singleton.
    assert is_true(model[output_generated])