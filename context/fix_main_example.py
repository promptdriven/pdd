import os
import sys
import click
from pathlib import Path
from rich.console import Console

# Ensure the pdd package is in the python path
# This allows importing from pdd.fix_main even if running this script directly
# from the 'context' directory.
current_dir = Path(__file__).resolve().parent
project_root = current_dir.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from pdd.fix_main import fix_main

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
PROMPT_FILE = OUTPUT_DIR / "calculator_python.prompt"
PROMPT_TEXT = "Write a Python function `add(a, b)` that returns the sum of two numbers."
with open(PROMPT_FILE, "w") as f:
    f.write(PROMPT_TEXT)

# 4. Create a verification script (required for --loop mode)
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

# 5. Create an error log file (required for non-loop mode, optional for loop)
ERROR_FILE = OUTPUT_DIR / "errors.log"
with open(ERROR_FILE, "w") as f:
    f.write("AssertionError: assert -1 == 5")


def main():
    """
    Demonstrates how to use fix_main to fix code errors.
    We will simulate a Click context and call the function directly.
    """
    console.print("[bold blue]Starting Fix Main Example[/bold blue]")

    # Create a dummy Click command to serve as the parent for the context
    @click.command()
    def dummy_cli():
        pass

    # Initialize a Click Context
    # fix_main expects certain keys in ctx.obj (populated by the main CLI group)
    ctx = click.Context(dummy_cli)
    ctx.obj = {
        'verbose': True,
        'strength': 0.5,       # Default LLM strength
        'temperature': 0.0,    # Default LLM temperature
        'time': 0.25,          # Thinking time
        'force': True,         # Overwrite files without asking
        'quiet': False,
        'local': True,         # Force local execution for this example
        'context': None,
        'confirm_callback': None
    }

    # Define output paths
    output_test_path = str(OUTPUT_DIR / "test_calculator_fixed.py")
    output_code_path = str(OUTPUT_DIR / "calculator_fixed.py")
    output_results_path = str(OUTPUT_DIR / "fix_results.log")

    # --- Example 1: Using Loop Mode (Iterative Fixing) ---
    console.print("\n[bold green]--- Running in Loop Mode ---[/bold green]")
    
    # In loop mode, the system runs the tests, captures errors, and iterates.
    # It requires a verification program.
    success, fixed_test, fixed_code, attempts, cost, model = fix_main(
        ctx=ctx,
        prompt_file=str(PROMPT_FILE),
        code_file=str(CODE_FILE),
        unit_test_file=str(TEST_FILE),
        error_file=str(ERROR_FILE), # Can be empty/ignored in loop mode as it's generated
        output_test=output_test_path,
        output_code=output_code_path,
        output_results=output_results_path,
        loop=True,                  # Enable iterative loop
        verification_program=str(VERIFY_FILE),
        max_attempts=3,
        budget=1.0,                 # $1.00 budget
        auto_submit=False,
        agentic_fallback=False,     # Disable agentic fallback for simple example
        strength=None,              # Use context default
        temperature=None            # Use context default
    )

    console.print(f"Loop Mode Success: {success}")
    console.print(f"Attempts: {attempts}")
    console.print(f"Cost: ${cost:.4f}")
    
    if success:
        console.print("[green]Fixed Code Content:[/green]")
        console.print(fixed_code)

    # --- Example 2: Single Pass Mode (Non-Loop) ---
    # This mode assumes you already have an error log file and just want one fix attempt.
    console.print("\n[bold green]--- Running in Single-Pass Mode ---[/bold green]")
    
    # Reset output paths to avoid confusion
    single_pass_code_path = str(OUTPUT_DIR / "calculator_single_pass.py")
    
    success_single, _, fixed_code_single, attempts_single, cost_single, _ = fix_main(
        ctx=ctx,
        prompt_file=str(PROMPT_FILE),
        code_file=str(CODE_FILE),
        unit_test_file=str(TEST_FILE),
        error_file=str(ERROR_FILE), # Must exist and contain errors
        output_test=None,           # Don't save fixed test
        output_code=single_pass_code_path,
        output_results=None,
        loop=False,                 # Disable loop
        verification_program=None,  # Not needed for single pass
        max_attempts=1,             # Ignored in non-loop mode (always 1)
        budget=1.0,
        auto_submit=False,
        agentic_fallback=False
    )

    console.print(f"Single Pass Success: {success_single}")
    console.print(f"Cost: ${cost_single:.4f}")

if __name__ == "__main__":
    main()