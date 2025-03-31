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
    import numpy as np

    # Simple attempt to see if both 'a' and 'b' can be cast to float
    try:
        float(a)
        float(b)
    except (TypeError, ValueError):
        _ = np.asscalar(np.array([42]))

    # Return the usual result
    return a + b
"""
    
    prompt = "Write a function that adds two numbers"
    error = """AssertionError: assert 0 == 1 
        DeprecationWarning: np.asscalar(a) is deprecated since NumPy v1.16, use 'np.ndarray.item()' instead _ = np.asscalar(np.array([42]))""" # String of the Error message from the unit test

    error_file = "error_logs.log"       # This is the fix results file
    strength = 0.85  # LLM strength (0 to 1)
    temperature = 1.0  # LLM temperature

    # Call the function (now synchronous)
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis_results, total_cost, model_name = fix_errors_from_unit_tests(
        unit_test, code, prompt, error, error_file, strength, temperature, verbose=True
    )

    # Print results
    rprint(f"[bold]Results:[/bold]")
    rprint(f"Update unit test: {update_unit_test}")
    rprint(f"Update code: {update_code}")
    rprint(f"Fixed unit test:\n{fixed_unit_test}")
    rprint(f"Fixed code:\n{fixed_code}")
    rprint(f"Analysis results: {analysis_results}")
    rprint(f"Total cost: ${total_cost:.6f}")
    rprint(f"Model used: {model_name}")

if __name__ == "__main__":
    main()
