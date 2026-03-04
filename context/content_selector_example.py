#!/usr/bin/env python3
"""
Example usage of the ContentSelector module.

This module provides precise extraction of file content based on various
criteria including line ranges, Python AST structures (functions, classes),
Markdown sections, and regex patterns.

The primary interface is:
    ContentSelector.select(
        content: str,          # The full text to extract from
        selectors: list[str],  # Selector strings like "lines:1-10", "def:my_func", etc.
        file_path: str | None, # Optional path to infer file type (.py, .md)
        mode: str,             # "full" (default) or "interface" (Python signatures only)
    ) -> str                   # The extracted content

Selector kinds:
    lines:N-M       Line range (1-based, inclusive). Also: lines:N, lines:N-, lines:-M
    def:name        Python function/async function by name (requires .py or no file_path)
    class:Name      Entire Python class definition
    class:Name.meth A specific method within a Python class
    section:Heading Markdown section by heading text (requires .md file_path)
    pattern:/regex/ Lines matching a regular expression

Multiple selectors can be combined (as a list or comma-separated string);
the union of all matched regions is returned in original file order.
"""

from __future__ import annotations

import os
import sys
import textwrap

# ---------------------------------------------------------------------------
# Path setup – ensure the parent directory is importable
# ---------------------------------------------------------------------------
script_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.dirname(script_dir)
if project_root not in sys.path:
    sys.path.insert(0, project_root)

from pdd.content_selector import ContentSelector, SelectorError

# Output directory for any generated files
output_dir = os.path.join(script_dir, "output")
os.makedirs(output_dir, exist_ok=True)


# ---------------------------------------------------------------------------
# Sample content used throughout the examples
# ---------------------------------------------------------------------------

SAMPLE_PYTHON = textwrap.dedent("""\
    from __future__ import annotations

    import math
    from typing import Optional

    MAX_RETRIES: int = 3

    class Calculator:
        \"\"\"A simple calculator with basic arithmetic operations.\"\"\"

        precision: int = 2

        def __init__(self, name: str = \"default\") -> None:
            \"\"\"Initialise the calculator.

            Parameters
            ----------
            name:
                A human-readable label for this calculator instance.
            \"\"\"
            self.name = name
            self._history: list[str] = []

        def add(self, a: float, b: float) -> float:
            \"\"\"Return the sum of *a* and *b*.\"\"\"
            result = a + b
            self._history.append(f\"{a} + {b} = {result}\")
            return round(result, self.precision)

        def divide(self, a: float, b: float) -> float:
            \"\"\"Return *a* divided by *b*.

            Raises
            ------
            ZeroDivisionError
                If *b* is zero.
            \"\"\"
            if b == 0:
                raise ZeroDivisionError(\"Cannot divide by zero\")
            return round(a / b, self.precision)

        def _reset_history(self) -> None:
            \"\"\"Clear internal history (private).\"\"\"
            self._history.clear()

    class AdvancedCalculator(Calculator):
        \"\"\"Extended calculator with scientific functions.\"\"\"

        def sqrt(self, x: float) -> float:
            \"\"\"Return the square root of *x*.\"\"\"
            if x < 0:
                raise ValueError(\"Cannot take sqrt of negative number\")
            return round(math.sqrt(x), self.precision)

    def greet(name: str) -> str:
        \"\"\"Return a greeting string.\"\"\"
        return f\"Hello, {name}!\"

    async def fetch_data(url: str, timeout: int = 30) -> dict:
        \"\"\"Fetch data from a URL asynchronously.

        Parameters
        ----------
        url:
            The endpoint to fetch from.
        timeout:
            Request timeout in seconds.

        Returns
        -------
        dict
            The parsed JSON response.
        \"\"\"
        # Simulated async fetch
        return {\"url\": url, \"status\": \"ok\"}
""")

SAMPLE_MARKDOWN = textwrap.dedent("""\
    # Project Overview

    This project provides a calculator library.

    ## Installation

    Install via pip:

    ```bash
    pip install calculator
    ```

    ## Usage

    Import and use the calculator:

    ```python
    from calculator import Calculator
    calc = Calculator()
    print(calc.add(2, 3))
    ```

    ### Advanced Usage

    For scientific operations use `AdvancedCalculator`.

    ## API Reference

    See the full API docs at https://example.com/docs.

    ## Contributing

    PRs welcome! Please read CONTRIBUTING.md first.
""")


def separator(title: str) -> None:
    """Print a visual separator for each example."""
    print(f"\n{'=' * 70}")
    print(f"  {title}")
    print(f"{'=' * 70}\n")


def main() -> None:
    """Run all ContentSelector examples."""

    # ==================================================================
    # Example 1: Select specific lines by number and range
    # ==================================================================
    separator("Example 1: Line selectors")

    # Single line (1-based)
    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["lines:1"],
        file_path="calculator.py",
    )
    print("lines:1 →")
    print(result)
    print()

    # Inclusive range
    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["lines:1-4"],
        file_path="calculator.py",
    )
    print("lines:1-4 →")
    print(result)
    print()

    # Open-ended range (line 3 to end)
    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["lines:1-3"],
        file_path="calculator.py",
    )
    print("lines:1-3 →")
    print(result)
    print()

    # From start to line 4
    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["lines:-4"],
        file_path="calculator.py",
    )
    print("lines:-4 →")
    print(result)

    # ==================================================================
    # Example 2: Extract a Python function by name (def: selector)
    # ==================================================================
    separator("Example 2: def: selector – extract a function")

    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["def:greet"],
        file_path="calculator.py",
    )
    print("def:greet →")
    print(result)
    print()

    # Async function
    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["def:fetch_data"],
        file_path="calculator.py",
    )
    print("def:fetch_data →")
    print(result)

    # ==================================================================
    # Example 3: Extract an entire class (class: selector)
    # ==================================================================
    separator("Example 3: class: selector – extract a whole class")

    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["class:AdvancedCalculator"],
        file_path="calculator.py",
    )
    print("class:AdvancedCalculator →")
    print(result)

    # ==================================================================
    # Example 4: Extract a specific method from a class
    # ==================================================================
    separator("Example 4: class:Name.method selector")

    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["class:Calculator.divide"],
        file_path="calculator.py",
    )
    print("class:Calculator.divide →")
    print(result)

    # ==================================================================
    # Example 5: Markdown section selector
    # ==================================================================
    separator("Example 5: section: selector – Markdown heading extraction")

    # Extracts everything under "## Usage" until the next same-or-higher level heading
    result = ContentSelector.select(
        content=SAMPLE_MARKDOWN,
        selectors=["section:Usage"],
        file_path="README.md",
    )
    print("section:Usage →")
    print(result)

    # ==================================================================
    # Example 6: Regex pattern selector
    # ==================================================================
    separator("Example 6: pattern: selector – regex line matching")

    # Find all lines containing 'import'
    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["pattern:/^import|^from .+ import/"],
        file_path="calculator.py",
    )
    print("pattern:/^import|^from .+ import/ →")
    print(result)
    print()

    # Find lines containing 'round('
    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["pattern:/round\\(/"],
        file_path="calculator.py",
    )
    print("pattern:/round\\(/ →")
    print(result)

    # ==================================================================
    # Example 7: Multiple selectors combined
    # ==================================================================
    separator("Example 7: Multiple selectors (union of results)")

    # Combine a function and a class method – results are merged in file order
    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["def:greet", "class:Calculator.add"],
        file_path="calculator.py",
    )
    print("def:greet + class:Calculator.add →")
    print(result)
    print()

    # Selectors can also be passed as a single comma-separated string
    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors="lines:1-4, def:greet",
        file_path="calculator.py",
    )
    print("Comma-separated 'lines:1-4, def:greet' →")
    print(result)

    # ==================================================================
    # Example 8: Interface mode – signatures & docstrings only
    # ==================================================================
    separator("Example 8: Interface mode (mode='interface')")

    # Interface for the entire file – bodies replaced with '...',
    # private methods (except __init__) excluded
    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=[],           # empty selectors → whole file interface
        file_path="calculator.py",
        mode="interface",
    )
    print("Full-file interface →")
    print(result)

    # ==================================================================
    # Example 9: Interface mode with a specific class selector
    # ==================================================================
    separator("Example 9: Interface mode for a specific class")

    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["class:Calculator"],
        file_path="calculator.py",
        mode="interface",
    )
    print("class:Calculator (interface) →")
    print(result)

    # ==================================================================
    # Example 10: Error handling – malformed selector
    # ==================================================================
    separator("Example 10: Error handling")

    # Malformed selector
    try:
        ContentSelector.select(
            content=SAMPLE_PYTHON,
            selectors=["badformat"],
            file_path="calculator.py",
        )
    except SelectorError as exc:
        print(f"Caught SelectorError for malformed selector:\n  {exc}")
    print()

    # Function not found
    try:
        ContentSelector.select(
            content=SAMPLE_PYTHON,
            selectors=["def:nonexistent_function"],
            file_path="calculator.py",
        )
    except SelectorError as exc:
        print(f"Caught SelectorError for missing function:\n  {exc}")
    print()

    # Line out of range
    try:
        ContentSelector.select(
            content=SAMPLE_PYTHON,
            selectors=["lines:9999"],
            file_path="calculator.py",
        )
    except SelectorError as exc:
        print(f"Caught SelectorError for out-of-range line:\n  {exc}")
    print()

    # Markdown section not found
    try:
        ContentSelector.select(
            content=SAMPLE_MARKDOWN,
            selectors=["section:Nonexistent Heading"],
            file_path="README.md",
        )
    except SelectorError as exc:
        print(f"Caught SelectorError for missing section:\n  {exc}")
    print()

    # AST selector on a non-Python file
    try:
        ContentSelector.select(
            content=SAMPLE_MARKDOWN,
            selectors=["def:greet"],
            file_path="README.md",
        )
    except SelectorError as exc:
        print(f"Caught SelectorError for wrong file type:\n  {exc}")

    # ==================================================================
    # Example 11: No file_path – defaults to Python for AST selectors
    # ==================================================================
    separator("Example 11: No file_path (defaults to Python)")

    result = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=["def:greet"],
        file_path=None,  # will assume Python
    )
    print("def:greet (no file_path) →")
    print(result)

    # ==================================================================
    # Save one result to a file for reference
    # ==================================================================
    separator("Done – saving interface output to output/")

    interface_output = ContentSelector.select(
        content=SAMPLE_PYTHON,
        selectors=[],
        file_path="calculator.py",
        mode="interface",
    )
    out_path = os.path.join(output_dir, "calculator_interface.py")
    with open(out_path, "w") as f:
        f.write(interface_output)
    print(f"Interface output saved to output/calculator_interface.py")


if __name__ == "__main__":
    main()