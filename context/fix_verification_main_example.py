import os
import sys
import click
from pathlib import Path
from rich import print as rich_print

# Adjust the path to ensure we can import the module
# Assuming the module is in a package structure like 'pdd.fix_verification_main'
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

# Import the function to be demonstrated
# Note: In a real package, this would be: from pdd.fix_verification_main import fix_verification_main
try:
    from pdd.fix_verification_main import fix_verification_main
except ImportError:
    # Fallback for standalone testing if not installed as a package
    try:
        from fix_verification_main import fix_verification_main
    except ImportError:
        rich_print("[red]Error: Could not import fix_verification_main. Ensure it is in the python path.[/red]")
        sys.exit(1)


def create_dummy_files(base_dir: Path) -> tuple[Path, Path, Path]:
    """Creates dummy files for the example.
    
    Args:
        base_dir: The base directory to create the dummy files in.
        
    Returns:
        A tuple containing paths to the prompt file, code file, and program file.
    """
    base_dir.mkdir(exist_ok=True)

    # 1. Create a dummy prompt file
    prompt_file = base_dir / "calculator_python.prompt"
    prompt_file.write_text("Create a calculator module with an add function.", encoding="utf-8")

    # 2. Create a dummy code file (with a bug)
    code_file = base_dir / "calculator.py"
    code_content = """
def add(a, b):
    # Intentional bug: subtraction instead of addition
    return a - b
"""
    code_file.write_text(code_content, encoding="utf-8")

    # 3. Create a dummy verification program
    program_file = base_dir / "verify_calculator.py"
    program_content = """
import sys
import calculator

def test_add():
    result = calculator.add(5, 3)
    expected = 8
    print(f"Testing add(5, 3)... Result: {result}, Expected: {expected}")
    if result != expected:
        print("FAILURE: Result does not match expected value.")
        sys.exit(1)
    else:
        print("SUCCESS: Test passed.")

if __name__ == "__main__":
    test_add()
"""
    program_file.write_text(program_content, encoding="utf-8")

    return prompt_file, code_file, program_file


def main() -> None:
    """Main function to demonstrate the fix_verification_main module."""
    # Setup paths
    base_dir = Path("example_verification_env")
    prompt_path, code_path, program_path = create_dummy_files(base_dir)
    
    # Define output paths
    output_results = base_dir / "verification_results.log"
    output_code = base_dir / "calculator_fixed.py"
    output_program = base_dir / "verify_calculator_fixed.py"

    # Mock a Click Context
    # The function expects a Click context with an 'obj' dictionary for global settings
    ctx = click.Context(click.Command("verify"))
    ctx.obj = {
        'verbose': True,
        'quiet': False,
        'force': True,
        'strength': 0.5,
        'temperature': 0.0,
        'time': 0.5,
        'local': True,  # Force local execution for this example
        'context': None,
        'confirm_callback': None
    }

    rich_print("[bold blue]Running fix_verification_main Example[/bold blue]")
    rich_print(f"Prompt: {prompt_path}")
    rich_print(f"Code: {code_path}")
    rich_print(f"Program: {program_path}")

    try:
        # Call the main verification function
        # We are running in single-pass mode (loop=False)
        success, final_prog, final_code, attempts, cost, model = fix_verification_main(
            ctx=ctx,
            prompt_file=str(prompt_path),
            code_file=str(code_path),
            program_file=str(program_path),
            output_results=str(output_results),
            output_code=str(output_code),
            output_program=str(output_program),
            loop=False,
            verification_program=None,  # Not needed for single pass
            max_attempts=1,
            budget=1.0,
            agentic_fallback=False
        )

        rich_print("\n[bold green]Execution Finished[/bold green]")
        rich_print(f"Success: {success}")
        rich_print(f"Attempts: {attempts}")
        rich_print(f"Total Cost: ${cost:.4f}")
        rich_print(f"Model: {model}")
        
        if success:
            rich_print("\n[bold]Fixed Code Content:[/bold]")
            rich_print(final_code)
        else:
            rich_print("\n[yellow]Verification failed or no fixes proposed.[/yellow]")

    except Exception as e:
        rich_print(f"[bold red]An error occurred during execution:[/bold red] {e}")
    finally:
        # Cleanup (optional)
        # import shutil
        # shutil.rmtree(base_dir)
        pass


if __name__ == "__main__":
    main()