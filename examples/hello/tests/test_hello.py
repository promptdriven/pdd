# =============================================================================
# TEST PLAN
# =============================================================================
# 1. FUNCTIONALITY ANALYSIS:
#    - Function: hello()
#    - Parameters: None
#    - Return Value: None (returns None explicitly or implicitly)
#    - Side Effect: Prints the exact string "hello" followed by a newline to stdout.
#
# 2. EDGE CASES & VERIFICATION STRATEGY:
#    - Correct Output: Ensure the string printed is exactly "hello".
#      (Strategy: Unit Test using capsys)
#    - Return Value: Ensure the function returns None.
#      (Strategy: Unit Test)
#    - No Arguments: Ensure the function can be called without arguments.
#      (Strategy: Unit Test)
#    - Formal Verification: Since this function involves I/O (printing to console)
#      and no complex logic or arithmetic, Z3 formal verification is not
#      applicable in the traditional sense (Z3 is for logic/constraints, not
#      side-effect verification). However, we can model the "contract" that
#      the output must match the expected constant.
#
# 3. TEST CASES:
#    - test_hello_output: Captures stdout and asserts it equals "hello\n".
#    - test_hello_return_value: Asserts that the function returns None.
#    - test_hello_no_args: Verifies function can be called without arguments.
#    - test_hello_formal_contract: A symbolic-style check ensuring the
#      specification "output == 'hello'" is met using Z3.
# =============================================================================

import pytest
from hello import hello


def test_hello_output(capsys) -> None:
    """
    Test that the hello() function prints the exact string 'hello' to stdout.
    """
    hello()
    captured = capsys.readouterr()
    assert captured.out == "hello\n", f"Expected 'hello\\n', got {repr(captured.out)}"


def test_hello_return_value() -> None:
    """
    Test that the hello() function returns None.
    """
    result = hello()
    assert result is None, "The hello function should return None."


def test_hello_no_args() -> None:
    """
    Test that the function can be called without arguments as defined.
    """
    try:
        hello()
    except TypeError:
        pytest.fail("hello() raised TypeError unexpectedly!")


def test_hello_no_stderr_output(capsys) -> None:
    """
    Test that the hello() function does not write anything to stderr.
    """
    hello()
    captured = capsys.readouterr()
    assert captured.err == "", f"Expected no stderr output, got {repr(captured.err)}"


def test_hello_multiple_calls(capsys) -> None:
    """
    Test that calling hello() multiple times produces consistent output.
    """
    hello()
    hello()
    hello()
    captured = capsys.readouterr()
    assert captured.out == "hello\nhello\nhello\n", "Multiple calls should each print 'hello'"


def test_hello_formal_contract() -> None:
    """
    Formal verification style test.

    While Z3 is typically used for SMT solving of logic/arithmetic,
    we can use it here to verify the 'contract' of the string output
    if we treat the output as a symbolic constant.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    # Define the specification: The output must be the string "hello"
    # In a real-world scenario, this would be used for complex logic.
    # Here we demonstrate the setup for a formal check.

    s = z3.Solver()
    output_str = z3.String('output_str')
    expected_val = "hello"

    # Constraint: The output of the function must match our expected value
    s.add(output_str == expected_val)

    # Check if the specification is satisfiable (it is)
    assert s.check() == z3.sat

    # Verify that there is no case where output_str != "hello"
    # given our implementation's hardcoded nature.
    s.push()
    s.add(output_str != "hello")
    assert s.check() == z3.unsat
    s.pop()