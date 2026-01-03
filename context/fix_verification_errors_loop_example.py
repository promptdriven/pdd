import os
import sys
import shutil
from pathlib import Path
from rich.console import Console

# Ensure the 'pdd' package is in the Python path
# This allows us to import the module we want to demonstrate
current_dir = Path(__file__).resolve().parent
pdd_root = current_dir.parent  # Adjust this based on your actual project structure
if str(pdd_root) not in sys.path:
    sys.path.insert(0, str(pdd_root))

try:
    # Import the function to demonstrate
    # Note: Adjust the import path based on where the module is located in your package
    from pdd.fix_verification_errors_loop import fix_verification_errors_loop
except ImportError:
    print("Error: Could not import 'fix_verification_errors_loop'. Ensure the 'pdd' package is installed or in PYTHONPATH.")
    sys.exit(1)

# Initialize console for pretty printing
console = Console()


def setup_demo_environment(work_dir: Path) -> tuple[Path, Path, Path, str]:
    """
    Creates a temporary environment with:
    1. A buggy code file (calculator.py)
    2. A verification program (verify_calc.py)
    3. A prompt file (calculator.prompt)

    Args:
        work_dir: The directory to create the demo environment in.

    Returns:
        A tuple containing paths to the code file, verify file, prompt file,
        and the prompt content string.
    """
    if work_dir.exists():
        shutil.rmtree(work_dir)
    work_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create the buggy code file
    # It implements subtraction instead of addition
    code_content = """
def add(a: int, b: int) -> int:
    # Bug: Incorrectly subtracts instead of adds
    return a - b
"""
    code_file = work_dir / "calculator.py"
    code_file.write_text(code_content, encoding="utf-8")

    # 2. Create the verification program
    # This script runs the code and asserts the expected behavior
    verify_content = """
import sys
from calculator import add

def verify():
    print("Running verification for calculator.add(5, 3)...")
    result = add(5, 3)
    expected = 8
    
    print(f"Result: {result}")
    print(f"Expected: {expected}")
    
    if result != expected:
        print("VERIFICATION_FAILURE: Result does not match expected value.")
        sys.exit(1)
    
    print("VERIFICATION_SUCCESS")
    sys.exit(0)

if __name__ == "__main__":
    verify()
"""
    verify_file = work_dir / "verify_calc.py"
    verify_file.write_text(verify_content, encoding="utf-8")

    # 3. Create the prompt file
    # Describes the intended behavior
    prompt_content = """
Create a Python module 'calculator.py' with a function 'add(a, b)' that returns the sum of two integers.
"""
    prompt_file = work_dir / "calculator.prompt"
    prompt_file.write_text(prompt_content, encoding="utf-8")

    return code_file, verify_file, prompt_file, prompt_content


def main() -> None:
    """
    Main function to demonstrate the fix_verification_errors_loop.

    Sets up a demo environment with a buggy calculator module and runs
    the fix loop to automatically correct the code.
    """
    # Define a temporary working directory for the demo
    demo_dir = Path("demo_fix_loop_env")

    console.print(f"[bold blue]Setting up demo environment in {demo_dir}...[/bold blue]")
    code_file, verify_file, prompt_file, prompt_text = setup_demo_environment(demo_dir)

    console.print("[bold]Initial State:[/bold]")
    console.print(f"Code File ({code_file}):\n[dim]{code_file.read_text()}[/dim]")
    console.print(f"Verification Program ({verify_file}):\n[dim]{verify_file.read_text()}[/dim]")

    # Define parameters for the fix loop
    max_attempts = 3
    budget = 0.50  # USD
    strength = 0.5
    temperature = 0.2

    console.print("\n[bold green]Starting fix_verification_errors_loop...[/bold green]")

    # Invoke the function
    # Note: This requires a configured LLM environment (e.g., OPENAI_API_KEY) to actually run the fix.
    # If no API key is present, it might fail gracefully or trigger agentic fallback depending on config.
    try:
        result = fix_verification_errors_loop(
            program_file=str(verify_file),      # The program that exercises the code
            code_file=str(code_file),           # The code to be fixed
            prompt=prompt_text,                 # The intent
            prompt_file=str(prompt_file),       # Path to prompt file (for context/fallback)
            verification_program=str(verify_file),  # Secondary verification (same as program here)
            strength=strength,
            temperature=temperature,
            max_attempts=max_attempts,
            budget=budget,
            verification_log_file=str(demo_dir / "verification.log"),
            verbose=True,                       # Enable detailed logging to stdout
            agentic_fallback=True,              # Enable fallback if standard fix fails
            use_cloud=False                     # Use local execution (set True for cloud API)
        )

        console.print("\n[bold blue]--- Loop Execution Finished ---[/bold blue]")

        if result["success"]:
            console.print("[bold green]SUCCESS: The code was fixed![/bold green]")
            console.print(f"Total Attempts: {result['total_attempts']}")
            console.print(f"Total Cost: ${result['total_cost']:.4f}")
            console.print(f"Model Used: {result['model_name']}")

            console.print("\n[bold]Fixed Code Content:[/bold]")
            console.print(result["final_code"])
        else:
            console.print("[bold red]FAILURE: Could not fix the code within constraints.[/bold red]")
            console.print(f"Status Message: {result['statistics'].get('status_message')}")

    except Exception as e:
        console.print(f"[bold red]An error occurred during execution: {e}[/bold red]")
        # This might happen if LLM keys are missing in the environment

    # Cleanup (optional)
    # shutil.rmtree(demo_dir)


if __name__ == "__main__":
    main()
