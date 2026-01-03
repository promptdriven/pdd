import os
import sys
from pathlib import Path
from rich.console import Console

# Add the parent directory to sys.path to allow importing the module
# This assumes the example script is in a subdirectory relative to the module
sys.path.append(str(Path(__file__).resolve().parent.parent))

# Import the main function from the module
# Note: Adjust the import path based on your actual package structure
try:
    from fix_code_loop import fix_code_loop
except ImportError:
    # Fallback for direct execution if not in a package
    try:
        from .fix_code_loop import fix_code_loop
    except ImportError:
        print("Error: Could not import fix_code_loop. Ensure the module is in the python path.")
        sys.exit(1)

console = Console()


def create_dummy_files(directory: Path) -> tuple[Path, Path, Path]:
    """
    Creates a dummy buggy code file and a verification script for demonstration.

    Args:
        directory: The directory where the dummy files will be created.

    Returns:
        A tuple containing paths to the code file, verification file, and prompt file.
    """
    directory.mkdir(parents=True, exist_ok=True)

    # 1. Create a buggy Python file
    # The bug: it tries to add a number and a string without casting
    code_file = directory / "calculator.py"
    code_content = """
def add_numbers(a, b):
    # This function is supposed to add two numbers safely
    return a + b
"""
    code_file.write_text(code_content, encoding="utf-8")

    # 2. Create a verification script (test)
    # This script will fail initially because it passes a string to the function
    verify_file = directory / "verify_calculator.py"
    verify_content = """
import sys
try:
    from calculator import add_numbers
except ImportError:
    # Handle case where import fails
    sys.exit(1)

def test_addition():
    try:
        # This input causes a TypeError in the buggy implementation
        result = add_numbers(10, "20")
        
        # Check correctness
        if result == 30:
            print("Test Passed: 10 + '20' = 30")
            sys.exit(0)
        else:
            print(f"Test Failed: Expected 30, got {result}")
            sys.exit(1)
    except Exception as e:
        print(f"Test Crashed: {e}")
        sys.exit(1)

if __name__ == "__main__":
    test_addition()
"""
    verify_file.write_text(verify_content, encoding="utf-8")

    # 3. Create a dummy prompt file (required for agentic fallback)
    prompt_file = directory / "prompt.txt"
    prompt_file.write_text(
        "Create a robust calculator function that handles string inputs.",
        encoding="utf-8"
    )

    return code_file, verify_file, prompt_file


def main() -> None:
    """
    Main function to demonstrate the fix_code_loop module.
    Sets up test files and runs the repair loop.
    """
    # Setup paths
    base_dir = Path("example_output")
    code_path, verify_path, prompt_path = create_dummy_files(base_dir)
    error_log_path = base_dir / "error_log.xml"

    console.print("[bold blue]Starting Fix Code Loop Example[/bold blue]")
    console.print(f"Target Code: {code_path}")
    console.print(f"Verification: {verify_path}")

    # Define parameters for the fix loop
    params = {
        "code_file": str(code_path),
        "prompt": "Write a python function to add two numbers, handling string inputs gracefully.",
        "verification_program": str(verify_path),
        "strength": 0.7,          # LLM creativity/strength
        "temperature": 0.2,       # LLM sampling temperature
        "max_attempts": 3,        # Max number of fix iterations
        "budget": 0.50,           # Max cost in USD
        "error_log_file": str(error_log_path),
        "verbose": True,          # Enable detailed logging
        "time": 1.0,              # Time factor for LLM
        "prompt_file": str(prompt_path),
        "agentic_fallback": True, # Enable backup agent if simple loop fails
        "use_cloud": False        # Set to True if you have cloud config set up
    }

    # Run the fix loop
    # Note: In a real scenario, this requires a working LLM backend hooked up
    # to `fix_code_module_errors`. If running without an LLM backend,
    # this will likely fail or use the dummy mock if configured.
    try:
        success, final_prog, final_code, attempts, cost, model = fix_code_loop(**params)

        console.print("\n[bold blue]--- Results ---[/bold blue]")
        if success:
            console.print(f"Success: [green]{success}[/green]")
        else:
            console.print(f"Success: [red]{success}[/red]")
        console.print(f"Total Attempts: {attempts}")
        console.print(f"Total Cost: ${cost:.4f}")
        console.print(f"Model Used: {model}")

        if success:
            console.print("\n[bold green]Fixed Code Content:[/bold green]")
            console.print(final_code)
        else:
            console.print("\n[bold red]Failed to fix the code.[/bold red]")
            console.print(f"Check log file at: {error_log_path}")

    except Exception as e:
        console.print(f"[bold red]An error occurred during execution:[/bold red] {e}")

    # Cleanup (Optional)
    # import shutil
    # shutil.rmtree(base_dir)


if __name__ == "__main__":
    main()