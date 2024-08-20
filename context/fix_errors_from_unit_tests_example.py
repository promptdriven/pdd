from fix_errors_from_unit_tests import fix_errors_from_unit_tests

# Define the inputs for the function
unit_test: str = """
def test_addition():
    assert add(1, 1) == 3  # Intentional error
"""

code: str = """
def add(a, b):
    return a + b
"""

error: str = "AssertionError: assert 2 == 3"
error_file: str = "error_log.txt"
strength: float = 0.7  # Strength parameter for LLM selection
temperature: float = 0 # Temperature parameter for LLM selection

try:
    # Call the function to fix errors in the unit tests
    update_unit_test, update_code, fixed_unit_test, fixed_code, total_cost = fix_errors_from_unit_tests(
        unit_test=unit_test,
        code=code,
        error=error,
        error_file=error_file,
        strength=strength,
        temperature=temperature
    )

    # Print the results
    print(f"Update Unit Test: {update_unit_test}")
    print(f"Update Code: {update_code}")
    print(f"Fixed Unit Test:\n{fixed_unit_test}")
    print(f"Fixed Code:\n{fixed_code}")
    print(f"Total Cost: ${total_cost:.6f}")
except Exception as e:
    print(f"An error occurred: {e}")