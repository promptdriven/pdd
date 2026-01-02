import os
import click
from pathlib import Path
from rich.console import Console

# Import the function to be tested
# Note: In a real package structure, this would be: from pdd.cmd_test_main import cmd_test_main
# We assume the pdd package is installed or in the python path.
from pdd.cmd_test_main import cmd_test_main

# Setup console for output
console = Console()

def run_example():
    """
    Demonstrates how to use cmd_test_main to generate unit tests for a simple calculator module.
    """
    # 1. Setup paths and directories
    base_dir = Path("./output")
    base_dir.mkdir(exist_ok=True)
    
    prompt_file = base_dir / "calculator_python.prompt"
    code_file = base_dir / "calculator.py"
    output_test_file = base_dir / "test_calculator.py"

    # 2. Create dummy input files
    # Create a prompt file
    prompt_content = """
    Task: Create a simple calculator module.
    Requirements:
    - Implement add(a, b)
    - Implement subtract(a, b)
    """
    prompt_file.write_text(prompt_content, encoding="utf-8")

    # Create the corresponding code file
    code_content = """
def add(a, b):
    return a + b

def subtract(a, b):
    return a - b
    """
    code_file.write_text(code_content, encoding="utf-8")

    console.print("[bold green]Created input files:[/bold green]")
    console.print(f"  Prompt: {prompt_file}")
    console.print(f"  Code:   {code_file}")

    # 3. Mock the Click Context
    # cmd_test_main expects a click.Context object with specific obj keys
    ctx = click.Context(click.Command("test"))
    ctx.obj = {
        "verbose": True,
        "force": True,      # Force overwrite without prompting
        "quiet": False,
        "local": True,      # Force local execution for this example
        "context": None,    # Optional context override
        "confirm_callback": None
    }

    # 4. Define arguments for cmd_test_main
    # Note: We set strength/temperature here, but they can also be resolved from config
    strength = 0.5
    temperature = 0.0
    
    console.print("\n[bold blue]Running cmd_test_main...[/bold blue]")

    # 5. Call the function
    # This will generate the test code, save it to output_test_file, and return details
    unit_test_code, total_cost, model_name = cmd_test_main(
        ctx=ctx,
        prompt_file=str(prompt_file),
        code_file=str(code_file),
        output=str(output_test_file),
        language="python",       # Explicitly set language
        coverage_report=None,    # Not using coverage report mode
        existing_tests=None,     # Not augmenting existing tests
        target_coverage=None,
        merge=False,
        strength=strength,
        temperature=temperature
    )

    # 6. Display results
    console.print("\n[bold green]Execution Complete![/bold green]")
    console.print(f"Model Used: {model_name}")
    console.print(f"Estimated Cost: ${total_cost:.6f}")
    console.print(f"Test file saved to: {output_test_file}")
    
    console.print("\n[bold]Generated Test Code Preview (first 5 lines):[/bold]")
    preview = "\n".join(unit_test_code.splitlines()[:5])
    console.print(preview)

if __name__ == "__main__":
    # Ensure PDD_PATH is set if your environment requires it for config resolution
    if "PDD_PATH" not in os.environ:
        os.environ["PDD_PATH"] = os.getcwd()
        
    run_example()