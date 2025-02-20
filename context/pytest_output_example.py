import argparse
import json
import io
import sys
import pytest
from rich.console import Console
from rich.pretty import pprint
import os

# Assuming the module is installed, we can import it directly.  If it were
# in a package, we'd use a relative import like `from .pytest_output import ...`
import pdd.pytest_output as pytest_output


console = Console()


def create_dummy_test_file(file_path: str, content: str):
    """Creates a dummy test file with the given content."""
    with open(file_path, "w") as f:
        f.write(content)


def main_example():
    """
    Demonstrates the usage of the pytest_output module.
    """

    # Create a dummy test file.
    test_file_path = "output/test_example.py"
    os.makedirs(os.path.dirname(test_file_path), exist_ok=True)
    create_dummy_test_file(
        test_file_path,
        """
def test_passing():
    assert 1 == 1

def test_failing():
    assert 1 == 2

def test_error():
    raise ValueError("This is an error")

import pytest
@pytest.mark.filterwarnings("error")
def test_warning():
    import warnings
    warnings.warn("This is a warning")
""",
    )

    # --- Example 1: Using the main function with argparse ---
    print("-" * 50)
    console.rule("[bold]Example 1: Using main function[/bold]")
    print("-" * 50)
    # Simulate command-line arguments.
    sys.argv = ["pdd/pytest_output", test_file_path]

    pytest_output.main()  # Call the main function.

    # --- Example 2: Using run_pytest_and_capture_output and save_output_to_json ---
    print("\n" + "-" * 50)
    console.rule(
        "[bold]Example 2: Using run_pytest_and_capture_output and save_output_to_json[/bold]"
    )
    print("-" * 50)

    result = pytest_output.run_pytest_and_capture_output(test_file_path)
    if result:
        pprint(result, console=console)
        pytest_output.save_output_to_json(result, "output/pytest_example.json")

    # --- Example 3: Handling a non-existent test file ---
    print("\n" + "-" * 50)
    console.rule("[bold]Example 3: Handling a non-existent test file[/bold]")
    print("-" * 50)
    non_existent_file = "output/non_existent_test.py"
    result = pytest_output.run_pytest_and_capture_output(non_existent_file)  # Should print an error message.

    # --- Example 4: Handling a non-python test file ---
    print("\n" + "-" * 50)
    console.rule("[bold]Example 4: Handling a non-python test file[/bold]")
    print("-" * 50)
    non_python_file = "output/test_example.txt"
    create_dummy_test_file(non_python_file, "This is not a python file")
    result = pytest_output.run_pytest_and_capture_output(non_python_file)  # Should print an error message

    # --- Example 5: Test file with no tests ---
    print("\n" + "-" * 50)
    console.rule("[bold]Example 5: Test file with no tests[/bold]")
    print("-" * 50)
    empty_test_file = "output/empty_test.py"
    create_dummy_test_file(empty_test_file, "")  # Create an empty file.
    result = pytest_output.run_pytest_and_capture_output(empty_test_file)
    if result:
        pprint(result, console=console)
        pytest_output.save_output_to_json(result, "output/pytest_empty.json")

    # --- Example 6: Using TestResultCollector directly (advanced) ---
    print("\n" + "-" * 50)
    console.rule("[bold]Example 6: Using TestResultCollector directly (advanced)[/bold]")
    print("-" * 50)

    collector = pytest_output.TestResultCollector()
    try:
        collector.capture_logs()
        pytest.main([test_file_path], plugins=[collector])
    finally:
        stdout, stderr = collector.get_logs()

    print("Captured stdout:", stdout)
    print("Captured stderr:", stderr)
    print("Failures:", collector.failures)
    print("Errors:", collector.errors)
    print("Warnings:", collector.warnings)
    print("Passed:", collector.passed)


if __name__ == "__main__":
    main_example()
