# example_usage.py
"""
Example of how to use the `merge_with_existing_test` function.

This script demonstrates merging a new Python test case into an existing
test suite using the provided function.

Key Features Demonstrated:
- How to structure input strings for existing and new tests.
- How to call the function with required parameters (language, strength, etc.).
- How to interpret the returned tuple (merged code, cost, model name).

To make this example runnable and self-contained, it uses `unittest.mock`
to simulate the behavior of internal dependencies (`load_prompt_template`,
`llm_invoke`, `postprocess`). In a real application, these would perform
actual file I/O and network requests to an LLM API.
"""
import sys
from unittest.mock import patch
from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax
from typing import Tuple, Optional

# --- Minimal stubs for dependencies (so the module is self-contained) ---
# These exist so that patch targets (e.g. '__main__.llm_invoke') are present.
# In practice, real implementations would be provided by the package.
EXTRACTION_STRENGTH = 0.5
DEFAULT_TIME = 0.5


def llm_invoke(prompt, input_json, strength, temperature, time, verbose=False):
    """Stub: should be patched during the example run."""
    raise RuntimeError("llm_invoke stub should be patched in the example")


def load_prompt_template(name: str) -> str:
    """Stub: returns a mock template string."""
    return "mock_template"


def preprocess(*args, **kwargs):
    """Stub for preprocess."""
    return args


def postprocess(raw: str, language: str, strength: float, temperature: float, time: Optional[float], verbose: bool = False):
    """Stub: should be patched during the example run."""
    raise RuntimeError("postprocess stub should be patched in the example")


# --- Function under demonstration ---

def merge_with_existing_test(
    existing_tests: str,
    new_tests: str,
    language: str,
    strength: float,
    temperature: float,
    time_budget: Optional[float] = 0.5,
    verbose: bool = False,
) -> Tuple[str, float, str]:
    """
    Merges a new test case into an existing test file using an LLM.

    Args:
        existing_tests (str): The content of the existing test file.
        new_tests (str): The new test case to be merged.
        language (str): The programming language of the tests (e.g., "python").
        strength (float): LLM model strength (0.0 to 1.0). Higher values
                          use more powerful (and expensive) models.
        temperature (float): LLM model temperature (0.0 to 2.0). Higher values
                             produce more creative/random output.
        time_budget (Optional[float]): Time allocation for the LLM.
        verbose (bool, optional): If True, enables detailed logging to the console.
                                  Defaults to False.

    Returns:
        Tuple[str, float, str]: A tuple containing:
            - merged_code (str): The complete, merged test code.
            - total_cost (float): The total cost in USD for the LLM operations.
            - model_name (str): The name of the primary LLM used for the merge.
    """
    console = Console()
    if not all([existing_tests, new_tests, language]):
        raise ValueError("existing_tests, new_tests, and language must be non-empty strings.")
    if not (0.0 <= strength <= 1.0):
        raise ValueError("Strength must be between 0.0 and 1.0.")
    if not (0.0 <= temperature <= 2.0):
        raise ValueError("Temperature must be between 0.0 and 2.0.")

    try:
        # In the real implementation you would call load_prompt_template(...)
        template = load_prompt_template("merge_tests")
        input_json = {"existing_tests": existing_tests, "new_tests": new_tests, "language": language}

        if verbose:
            console.print("[blue]Invoking LLM to merge test cases...[/blue]")

        response = llm_invoke(prompt=template, input_json=input_json, strength=strength, temperature=temperature, time=time_budget, verbose=verbose)
        raw_result, total_cost, model_name = response["result"], response["cost"], response["model_name"]

        if not raw_result or not raw_result.strip():
            raise ValueError("LLM returned an empty result during merge operation.")

        if verbose:
            console.print(f"[green]LLM invocation successful. Model: {model_name}, Cost: ${total_cost:.6f}[/green]")
            console.print("[blue]Post-processing the merged code...[/blue]")

        merged_code, post_cost, _ = postprocess(raw_result, language=language, strength=0.5, temperature=temperature, time=time_budget, verbose=verbose)
        total_cost += post_cost

        if verbose:
            console.print(f"[green]Post-processing complete. Additional cost: ${post_cost:.6f}[/green]")
            console.print(f"[bold green]Total cost for merge operation: ${total_cost:.6f}[/bold green]")

        return merged_code, total_cost, model_name

    except Exception as e:
        console.print(f"[bold red]Error in merge_with_existing_test:[/bold red] {e}")
        raise


# --- Example Usage ---

# 1. Define sample inputs for the function
EXISTING_PYTHON_TESTS = """
import unittest

def calculate_area(length, width):
    return length * width

class TestCalculateArea(unittest.TestCase):
    def test_positive_integers(self):
        self.assertEqual(calculate_area(5, 10), 50)

    def test_with_zero(self):
        self.assertEqual(calculate_area(5, 0), 0)
"""

NEW_PYTHON_TEST_CASE = """
    def test_floats(self):
        self.assertAlmostEqual(calculate_area(2.5, 4.0), 10.0)
"""


def main():
    """Main function to run the demonstration."""
    console = Console()
    console.print(Panel(
        "Demonstrating `merge_with_existing_test`",
        title="[bold cyan]Module Usage Example[/bold cyan]",
        expand=False,
    ))

    # 2. Mock the internal dependencies for a predictable, offline demonstration
    # This simulates the raw, often messy, output from the first LLM call
    mock_llm_raw_output = f"""
Of course! I've merged the new test case for floating-point numbers into your
existing test file. Here is the updated code:

```python
import unittest

def calculate_area(length, width):
    return length * width

class TestCalculateArea(unittest.TestCase):
    def test_positive_integers(self):
        self.assertEqual(calculate_area(5, 10), 50)

    def test_with_zero(self):
        self.assertEqual(calculate_area(5, 0), 0)

    def test_floats(self):
        self.assertAlmostEqual(calculate_area(2.5, 4.0), 10.0)
```

This new version is ready to run.
"""
    # This simulates the clean code extracted by the `postprocess` function
    mock_final_clean_code = """import unittest

def calculate_area(length, width):
    return length * width

class TestCalculateArea(unittest.TestCase):
    def test_positive_integers(self):
        self.assertEqual(calculate_area(5, 10), 50)

    def test_with_zero(self):
        self.assertEqual(calculate_area(5, 0), 0)

    def test_floats(self):
        self.assertAlmostEqual(calculate_area(2.5, 4.0), 10.0)
"""

    # Mock return values for the dependencies
    mock_llm_invoke_return = {
        "result": mock_llm_raw_output,
        "cost": 0.00185,
        "model_name": "claude-3-sonnet-20240229",
    }
    mock_postprocess_return = (mock_final_clean_code, 0.00030, "gpt-4-turbo")

    # The `patch` context manager replaces the real functions with our mocks
    # We target '__main__' because the function is defined in this script
    with patch("__main__.llm_invoke", return_value=mock_llm_invoke_return), \
         patch("__main__.postprocess", return_value=mock_postprocess_return):

        console.print("\n[bold]Inputs:[/bold]")
        console.print("  [cyan]Language:[/cyan] python")
        console.print("  [cyan]Strength:[/cyan] 0.7")
        console.print("  [cyan]Verbose:[/cyan] True\n")

        # 3. Call the function with verbose=True to see its internal logging
        try:
            merged_code, total_cost, model_name = merge_with_existing_test(
                existing_tests=EXISTING_PYTHON_TESTS,
                new_tests=NEW_PYTHON_TEST_CASE,
                language="python",
                strength=0.7,
                temperature=0.1,
                verbose=True,
            )

            # 4. Print the results
            console.print("\n[bold green]----- Function Result ----- [/bold green]")
            console.print(f"[bold]Model Used:[/bold] {model_name}")
            console.print(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")
            console.print("[bold]Merged Code:[/bold]")
            console.print(Syntax(merged_code, "python", theme="monokai", line_numbers=True))

        except Exception as e:
            console.print(f"[bold red]An error occurred during the example run: {e}[/bold red]")


if __name__ == "__main__":
    # To run this example, you would need to have the dependencies (like rich)
    # installed, but no API keys are required due to mocking.
    # `pip install rich`
    main()
