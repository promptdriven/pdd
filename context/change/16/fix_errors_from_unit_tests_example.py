import os
from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests
from rich import print as rprint

def main() -> None:
    """
    Main function to demonstrate the usage of fix_errors_from_unit_tests.
    Sets up example inputs, calls the function, and prints the results.
    """
    # Example inputs
    unit_test = """
def test_add():
    assert add(2, 3) == 5
    assert add(-1, 1) == 0
    assert add(0, 0) == 1  # This test case is incorrect
"""
    
    code = """
def add(a, b):
    return a + b
"""
    
    prompt = "Write a function that adds two numbers"
    error = "AssertionError: assert 0 == 1" # String of the Error message from the unit test
    error_file = "error_logs.txt"       # This is the fix results file
    strength = 0.7  # LLM strength (0 to 1)
    temperature = 0.5  # LLM temperature

    # Call the function
    update_unit_test, update_code, fixed_unit_test, fixed_code, total_cost, model_name = fix_errors_from_unit_tests(
        unit_test, code, prompt, error, error_file, strength, temperature
    )

    # Print results
    rprint(f"[bold]Results:[/bold]")
    rprint(f"Update unit test: {update_unit_test}")
    rprint(f"Update code: {update_code}")
    rprint(f"Fixed unit test:\n{fixed_unit_test}")
    rprint(f"Fixed code:\n{fixed_code}")
    rprint(f"Total cost: ${total_cost:.6f}")
    rprint(f"Model used: {model_name}")

if __name__ == "__main__":
    main()
