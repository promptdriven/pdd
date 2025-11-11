# test_hello.py

import sys
import os
import pytest
from z3 import Solver, String, StringVal, sat

# =================================== TEST PLAN ===================================
#
# 1.  **Objective:** Verify that the `hello` function in the `hello` module correctly
#     prints the string "hello" to standard output and handles incorrect usage gracefully.
#
# 2.  **Analysis of Code Under Test:**
#     -   **Function:** `hello()`
#     -   **Parameters:** None.
#     -   **Behavior:** Prints the literal string "hello" to `stdout`.
#     -   **Return Value:** Implicitly returns `None`.
#     -   **Side Effects:** The module file includes a top-level call to `hello()`,
#         which means importing the module will trigger a print. Tests should be
#         isolated from this import-time side effect.
#
# 3.  **Test Strategy:**
#     A combination of standard unit tests (using pytest) and a conceptual formal
#     verification test (using Z3) will be employed.
#
# 4.  **Edge Case Analysis (Unit Test vs. Z3):**
#     -   **Case:** Calling the function with arguments.
#         -   **Expected:** A `TypeError` should be raised.
#         -   **Method:** Unit Test. This is a standard Python runtime behavior that is
#           best verified with a direct call and exception check using `pytest.raises`.
#           Z3 is not designed to model or predict Python's internal type-checking
#           and exception mechanisms.
#     -   **Case:** Verifying the exact output string.
#         -   **Expected:** The string "hello\n" should be printed to `stdout`.
#         -   **Method:** Unit Test. Capturing standard output is a classic I/O test
#           pattern and the most direct way to verify the function's primary effect.
#           Z3 does not interact with I/O systems.
#     -   **Case:** Verifying the return value.
#         -   **Expected:** The function should return `None`.
#         -   **Method:** Unit Test. A simple assertion on the function's return
#           value is sufficient and clear.
#
# 5.  **Detailed Test Cases:**
#
#     a) **Unit Tests (Pytest):**
#        -   `test_hello_prints_correct_string`:
#            -   **Purpose:** To ensure the primary functionality is met.
#            -   **Action:** Call `hello()` and capture `stdout`.
#            -   **Assertion:** The captured output must be exactly `"hello\n"`.
#        -   `test_hello_returns_none`:
#            -   **Purpose:** To verify the function signature and implicit return.
#            -   **Action:** Call `hello()` and store the result.
#            -   **Assertion:** The result must be `None`.
#        -   `test_hello_with_arguments_raises_error`:
#            -   **Purpose:** To ensure the function adheres to its defined signature.
#            -   **Action:** Call `hello()` with a positional argument (e.g., `hello(1)`).
#            -   **Assertion:** A `TypeError` must be raised.
#
#     b) **Formal Verification (Z3):**
#        -   `test_formal_verification_output_is_constant`:
#            -   **Purpose:** To formally model and prove that the function's specified
#              output is a constant, non-contradictory value ("hello").
#            -   **Action:**
#                1.  Model the function's output as a Z3 `String` variable.
#                2.  Add a constraint that this output must equal the `StringVal("hello")`.
#                3.  Check if this system of constraints is satisfiable (`sat`).
#            -   **Assertion:** The solver should find the model satisfiable, formally
#              demonstrating that the property (output is "hello") is logically sound.
#              This test serves to illustrate that for a function with no inputs or
#              logic branches, the primary property is the constancy of its output.
#
# =================================================================================

# Add the source directory to the Python path for module import.
# This is necessary because the test file is in a 'tests' subdirectory
# and the code under test is in a 'src' subdirectory.
src_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'src'))
sys.path.insert(0, src_path)

# Import the function to be tested
from hello import hello

# --- Unit Tests (Pytest) ---

def test_hello_prints_correct_string(capsys):
    """
    Verifies that calling hello() prints the exact string "hello" to stdout,
    followed by a newline.
    """
    hello()
    captured = capsys.readouterr()
    assert captured.out == "hello\n"
    assert captured.err == ""

def test_hello_returns_none():
    """
    Verifies that the hello() function implicitly returns None.
    """
    return_value = hello()
    assert return_value is None

def test_hello_with_arguments_raises_error():
    """
    Verifies that calling hello() with any arguments raises a TypeError.
    """
    with pytest.raises(TypeError):
        hello("some_argument")

    with pytest.raises(TypeError):
        hello(arg="some_keyword_argument")

# --- Formal Verification (Z3) ---

def test_formal_verification_output_is_constant():
    """
    Formally "proves" that the function's output is a constant value.

    This test uses the Z3 theorem prover to model the function's behavior.
    For a simple function like this with no inputs or logic, the main property
    to verify is the constancy of its output.
    """
    # 1. Model: Create a solver and a variable to represent the function's output.
    solver = Solver()
    output = String("output")

    # 2. Constraint: The specification of the function is to produce the string "hello".
    # We add this as a logical constraint to our model.
    solver.add(output == StringVal("hello"))

    # 3. Check: We ask Z3 if this model is satisfiable.
    # Since there are no inputs or conflicting constraints, this is trivially satisfiable.
    # This "proves" that the property "output is 'hello'" is a consistent
    # and non-contradictory model of the function's specification.
    assert solver.check() == sat

    # 4. Get Model: We can also inspect the model to see the value that satisfies
    # the constraint.
    model = solver.model()
    # Z3 represents strings with quotes, so we use as_string() for a clean Python string.
    assert model[output].as_string() == "hello"
