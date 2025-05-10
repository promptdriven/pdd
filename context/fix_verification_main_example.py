import os
import click
import textwrap                 #  ← added
from pathlib import Path
from typing import Tuple, Dict, Any

# Assume 'pdd' package is installed or accessible in the Python path.
# The example script is likely in a different directory than the 'pdd' package.
from pdd.fix_verification_main import fix_verification_main

# Define default values matching the module's defaults for clarity
DEFAULT_MAX_ATTEMPTS = 3
DEFAULT_BUDGET = 5.0
DEFAULT_STRENGTH = 0.5
DEFAULT_TEMPERATURE = 0.0

def create_dummy_context(params: Dict[str, Any]) -> click.Context:
    """Creates a dummy Click context object for testing purposes."""
    # A minimal context setup is needed. We mainly care about ctx.params.
    ctx = click.Context(click.Command('dummy'))
    ctx.obj = params
    return ctx

def run_fix_verification_example():
    """
    Demonstrates how to use the fix_verification_main function.
    This example simulates calling the function as if invoked by the Click CLI,
    showing both single-pass and loop verification modes.
    """
    print("[bold blue]=== Running fix_verification_main Example ===[/bold blue]\n")

    # --- 1. Setup: Create necessary directories and input files ---
    output_dir = Path("output")
    output_dir.mkdir(exist_ok=True)

    prompt_content = "Create a Python module 'calculator.py' with a function 'add(a, b)' that returns the sum of two integers."
    # Intentionally buggy code (subtracts instead of adds) –‑ outer quotes
    #   switched to triple single quotes so the inner triple double quotes are
    #   perfectly legal.
    code_content_buggy = textwrap.dedent('''\
# calculator.py
def add(a: int, b: int) -> int:
    """Returns the difference of two integers (intentionally wrong)."""
    return a - b
''')

    # Program to run the code and produce output for verification
    program_content = textwrap.dedent("""\
import calculator
import sys

if len(sys.argv) != 3:
    print("Usage: python program.py <num1> <num2>")
    sys.exit(1)

a = int(sys.argv[1])
b = int(sys.argv[2])

result = calculator.add(a, b)
print(f"Input: ({a}, {b})")
print(f"Result: {result}")  # Output will be judged by LLM against the prompt
""")
    # Verification program for the loop mode (simple assertion)
    verification_program_content = textwrap.dedent("""\
import calculator
import sys

print("Running verification program...")
try:
    assert calculator.add(5, 3) == 8, "Verification Failed: 5 + 3 != 8"
    assert calculator.add(-1, 1) == 0, "Verification Failed: -1 + 1 != 0"
    print("Verification Succeeded!")
    sys.exit(0)  # Exit code 0 indicates success
except AssertionError as e:
    print(e)
    sys.exit(1)  # Non‑zero exit code indicates failure
""")

    prompt_file = output_dir / "calc.prompt"
    code_file = output_dir / "calculator.py"
    program_file = output_dir / "run_calculator.py"
    verification_program_file = output_dir / "verify_calculator.py"

    prompt_file.write_text(prompt_content)
    code_file.write_text(code_content_buggy)
    program_file.write_text(program_content)
    verification_program_file.write_text(verification_program_content)

    print(f"Created example files in: {output_dir.absolute()}")
    print(f"  - Prompt: {prompt_file.name}")
    print(f"  - Code (buggy): {code_file.name}")
    print(f"  - Program: {program_file.name}")
    print(f"  - Verification Program: {verification_program_file.name}\n")

    # --- 2. Define common parameters and context ---
    # These would typically come from global Click options
    global_params = {
        'strength': DEFAULT_STRENGTH,
        'temperature': DEFAULT_TEMPERATURE,
        'force': True,  # Allow overwriting output files in the example
        'quiet': False, # Show output during the run
        'verbose': True # Enable verbose logging for demonstration
    }
    ctx = create_dummy_context(global_params)

    # Define output paths
    output_results_single = output_dir / "verify_results_single.log"
    output_code_single = output_dir / "calculator_verified_single.py"
    output_program_single = output_dir / "run_calculator_verified_single.py"
    output_results_loop = output_dir / "verify_results_loop.log"
    output_code_loop = output_dir / "calculator_verified_loop.py"
    output_program_loop = output_dir / "run_calculator_verified_loop.py"

    # --- 3. Run in Single Pass Mode (loop=False) ---
    print("[bold cyan]--- Running Single Pass Verification (loop=False) ---[/bold cyan]")
    # In single pass, the LLM judges the output of `program_file` against the prompt.
    # It might propose fixes based on discrepancies found.
    # `verification_program` is not used here.
    try:
        success, final_program, final_code, attempts, total_cost, model_name = fix_verification_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            code_file=str(code_file), # Start with the buggy code
            program_file=str(program_file),
            output_results=str(output_results_single),
            output_code=str(output_code_single),
            output_program=str(output_program_single),
            loop=False,
            verification_program=None, # Not needed for single pass
            max_attempts=1, # Ignored when loop=False, but set for clarity
            budget=0.0      # Ignored when loop=False, but set for clarity
        )

        print("\n[bold green]--- Single Pass Results ---[/bold green]")
        print(f"Success Status: {success}")
        print(f"Attempts Made: {attempts}") # Should be 1 for single pass
        print(f"Total Cost (USD): ${total_cost:.6f}")
        print(f"Model Used: {model_name}")
        print(f"Final Program Content (first ~100 chars): {final_program[:100]}...")
        print(f"Final Code Content (first ~100 chars): {final_code[:100]}...")
        print(f"Results Log Saved To: {output_results_single if output_results_single.exists() else 'N/A'}")
        print(f"Verified Code Saved To: {output_code_single if success and output_code_single.exists() else 'N/A'}")
        print(f"Verified Program Saved To: {output_program_single if success and output_program_single.exists() else 'N/A'}")

    except Exception as e:
        print(f"[bold red]Error during single pass verification:[/bold red] {e}")

    # --- 4. Run in Loop Mode (loop=True) ---
    print("\n[bold cyan]--- Running Iterative Verification (loop=True) ---[/bold cyan]")
    # Reset code file to buggy version for the loop test
    code_file.write_text(code_content_buggy)
    print(f"Reset {code_file.name} to buggy version for loop test.")

    # In loop mode, the function repeatedly runs `program_file`, uses the LLM
    # to check output against the prompt, potentially fixes `code_file` and/or
    # `program_file`, and then runs `verification_program` to confirm the fix.
    # This continues until success, max_attempts, or budget is reached.
    loop_max_attempts = 3
    loop_budget = 0.10 # Set a small budget (in USD) for the example

    try:
        success_loop, final_program_loop, final_code_loop, attempts_loop, total_cost_loop, model_name_loop = fix_verification_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            code_file=str(code_file), # Start with the buggy code
            program_file=str(program_file),
            output_results=str(output_results_loop),
            output_code=str(output_code_loop),
            output_program=str(output_program_loop),
            loop=True,
            verification_program=str(verification_program_file), # Required for loop
            max_attempts=loop_max_attempts,
            budget=loop_budget
        )

        print("\n[bold green]--- Loop Results ---[/bold green]")
        print(f"Success Status: {success_loop}")
        print(f"Attempts Made: {attempts_loop} (Max: {loop_max_attempts})")
        print(f"Total Cost (USD): ${total_cost_loop:.6f} (Budget: ${loop_budget:.2f})")
        print(f"Model Used: {model_name_loop}")
        print(f"Final Program Content (first ~100 chars): {final_program_loop[:100]}...")
        print(f"Final Code Content (first ~100 chars): {final_code_loop[:100]}...")
        print(f"Results Log Saved To: {output_results_loop if output_results_loop.exists() else 'N/A'}")
        print(f"Verified Code Saved To: {output_code_loop if success_loop and output_code_loop.exists() else 'N/A'}")
        print(f"Verified Program Saved To: {output_program_loop if success_loop and output_program_loop.exists() else 'N/A'}")

        # Optionally, display the final fixed code if successful
        if success_loop and output_code_loop.exists():
             print("\n[bold magenta]Final Code Content (Loop):[/bold magenta]")
             print(output_code_loop.read_text())

    except Exception as e:
        print(f"[bold red]Error during loop verification:[/bold red] {e}")

    print("\n[bold blue]=== Example Finished ===[/bold blue]")

if __name__ == "__main__":
    # Use Rich for pretty printing in the example output
    from rich import print
    run_fix_verification_example()
