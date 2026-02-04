#!/usr/bin/env python3
"""
Example usage of the pdd.fix_error_loop module.

This example demonstrates how to use the `fix_error_loop` function to iteratively
fix a buggy Python function using unit tests and an LLM-based repair process.

It sets up a temporary environment with a buggy code file and a failing test,
then invokes the fix loop to repair the code.
"""

import os
import sys
from pathlib import Path
from rich.console import Console

# Ensure the pdd package is in the python path
# This allows importing from pdd.fix_error_loop even if running this script directly
current_dir = Path(__file__).resolve().parent
project_root = current_dir.parents[1]  # Adjust based on file depth
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from pdd.fix_error_loop import fix_error_loop

console = Console()

# --- Setup Mock Files ---

OUTPUT_DIR = Path("./output")
OUTPUT_DIR.mkdir(exist_ok=True)

# 1. Create a buggy code file
CODE_FILE = OUTPUT_DIR / "calculator.py"
BUGGY_CODE = """
def add(a, b):
    # Bug: subtracts instead of adds
    return a - b
"""
with open(CODE_FILE, "w") as f:
    f.write(BUGGY_CODE)

# 2. Create a failing unit test file
TEST_FILE = OUTPUT_DIR / "test_calculator.py"
TEST_CODE = """
from calculator import add

def test_add():
    assert add(2, 3) == 5
    assert add(-1, 1) == 0
"""
with open(TEST_FILE, "w") as f:
    f.write(TEST_CODE)

# 3. Create a prompt file (context for the LLM)
PROMPT_FILE = OUTPUT_DIR / "prompt.txt"
PROMPT_TEXT = "Write a Python function `add(a, b)` that returns the sum of two numbers."
with open(PROMPT_FILE, "w") as f:
    f.write(PROMPT_TEXT)

# 4. Create a verification script (optional, but good practice)
# This script ensures the code is syntactically valid and importable
VERIFY_FILE = OUTPUT_DIR / "verify_calc.py"
VERIFY_CODE = """
try:
    from calculator import add
    print("Import successful")
except ImportError as e:
    print(f"Import failed: {e}")
    exit(1)
"""
with open(VERIFY_FILE, "w") as f:
    f.write(VERIFY_CODE)


def main():
    console.print("[bold blue]Starting Fix Error Loop Example[/bold blue]")

    # Configuration parameters
    strength = 0.7          # LLM creativity/strength (0.0 to 1.0)
    temperature = 0.2       # LLM sampling temperature (0.0 to 1.0)
    max_attempts = 3        # Maximum number of fix iterations
    budget = 0.50           # Max cost budget in USD
    error_log = str(OUTPUT_DIR / "fix_log.txt")
    verbose = True          # Print detailed logs to console
    
    # Run the fix loop
    # This will:
    # 1. Run pytest on test_calculator.py
    # 2. Detect the failure (2 - 3 != 5)
    # 3. Send code + errors to LLM
    # 4. Apply the fix to calculator.py
    # 5. Verify and re-test
    success, final_test, final_code, attempts, cost, model = fix_error_loop(
        unit_test_file=str(TEST_FILE),
        code_file=str(CODE_FILE),
        prompt_file=str(PROMPT_FILE),
        prompt=PROMPT_TEXT,
        verification_program=str(VERIFY_FILE),
        strength=strength,
        temperature=temperature,
        max_attempts=max_attempts,
        budget=budget,
        error_log_file=error_log,
        verbose=verbose,
        agentic_fallback=True,  # Enable agentic fallback if simple loop fails
        use_cloud=False         # Set to True to use cloud LLM endpoint
    )

    console.print("\n[bold green]=== Results ===[/bold green]")
    console.print(f"Success: {success}")
    console.print(f"Attempts used: {attempts}")
    console.print(f"Total Cost: ${cost:.4f}")
    console.print(f"Model: {model}")
    
    if success:
        console.print("\n[bold]Fixed Code:[/bold]")
        console.print(final_code)
    else:
        console.print("[red]Failed to fix the code within budget/attempts.[/red]")

if __name__ == "__main__":
    main()