import click
import os
from pathlib import Path
from rich import print as rprint

# Assuming the module is importable as pdd.crash_main
# In a real scenario, you would adjust the import based on your package structure
from pdd.crash_main import crash_main


def run_crash_fix_example() -> None:
    """
    Demonstrates how to use the crash_main function to fix a crashed program.
    
    This example:
    1. Creates a dummy environment with a broken code file and a program that crashes.
    2. Creates a mock Click context.
    3. Calls crash_main to fix the error.
    4. Displays the results.
    """
    
    # --- Setup: Create dummy files ---
    base_dir = Path("crash_example_env")
    base_dir.mkdir(exist_ok=True)

    # 1. The Prompt File (what the code should do)
    prompt_file = base_dir / "calculator_python.prompt"
    prompt_content = "Write a calculator module with an add function that handles integers."
    prompt_file.write_text(prompt_content)

    # 2. The Code File (contains a bug)
    code_file = base_dir / "calculator.py"
    code_content = """
def add(a, b):
    # Bug: This function doesn't cast strings to ints
    return a + b
"""
    code_file.write_text(code_content)

    # 3. The Program File (calls the code and crashes)
    program_file = base_dir / "main_app.py"
    program_content = """
from calculator import add

# This will crash because inputs are strings
result = add("10", "5")
print(f"Result: {result}")
"""
    program_file.write_text(program_content)

    # 4. The Error File (captured stderr from the crash)
    error_file = base_dir / "error.log"
    error_content = """
Traceback (most recent call last):
  File "main_app.py", line 5, in <module>
    result = add("10", "5")
  File "/path/to/calculator.py", line 4, in add
    return a + b
TypeError: can only concatenate str (not "int") to str
"""
    error_file.write_text(error_content)

    # Output paths
    output_code = base_dir / "calculator_fixed.py"
    output_program = base_dir / "main_app_fixed.py"

    # --- Execution: Call crash_main ---
    
    rprint("[bold blue]Starting crash fix example...[/bold blue]")

    # Create a mock Click Context
    # crash_main expects ctx.obj to contain configuration like 'verbose', 'quiet', etc.
    ctx = click.Context(click.Command("crash"))
    ctx.obj = {
        "verbose": True,
        "quiet": False,
        "local": True,  # Force local execution for this example
        "force": True   # Overwrite output files without asking
    }

    try:
        success, final_code, final_program, attempts, cost, model = crash_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            code_file=str(code_file),
            program_file=str(program_file),
            error_file=str(error_file),
            output=str(output_code),
            output_program=str(output_program),
            loop=False,           # Single pass fix
            strength=0.5,         # Medium model strength
            temperature=0.0,      # Deterministic output
            budget=1.0            # $1.00 budget
        )

        # --- Results ---
        if success:
            rprint("\n[bold green]Fix Successful![/bold green]")
            rprint(f"Model used: {model}")
            rprint(f"Cost: ${cost:.4f}")
            
            rprint("\n[bold]Fixed Code Content:[/bold]")
            rprint(final_code)
            
            rprint("\n[bold]Fixed Program Content:[/bold]")
            rprint(final_program)
            
            rprint(f"\nFiles saved to:\n- {output_code}\n- {output_program}")
        else:
            rprint(f"\n[bold red]Fix Failed.[/bold red] Error: {model}")

    except Exception as e:
        rprint(f"[bold red]An error occurred during execution:[/bold red] {e}")

    # Cleanup (optional)
    # import shutil
    # shutil.rmtree(base_dir)


if __name__ == "__main__":
    run_crash_fix_example()