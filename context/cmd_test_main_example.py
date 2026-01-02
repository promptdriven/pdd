import os
import click
from pathlib import Path
from rich.console import Console

# Import the module to be tested
# Note: In a real package structure, this would be 'from pdd.cmd_test_main import cmd_test_main'
# Adjust the import path based on your actual project structure if running this script directly.
from pdd.cmd_test_main import cmd_test_main

# Initialize console for output
console = Console()

def run_example():
    """
    Demonstrates how to use cmd_test_main to generate unit tests for a Python file.
    """
    # 1. Setup paths for input and output files
    # We will create temporary files in an 'output' directory for this demonstration
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)

    prompt_file = output_dir / "calculator_python.prompt"
    code_file = output_dir / "calculator.py"
    test_output_file = output_dir / "test_calculator.py"

    # 2. Create dummy input files
    prompt_content = """
    Task: Create a simple calculator module.
    Language: Python
    Requirements:
    - Implement add(a, b)
    - Implement subtract(a, b)
    """
    
    code_content = """
def add(a, b):
    return a + b

def subtract(a, b):
    return a - b
    """

    prompt_file.write_text(prompt_content, encoding="utf-8")
    code_file.write_text(code_content, encoding="utf-8")

    console.print(f"[bold green]Created input files:[/bold green]")
    console.print(f"  Prompt: {prompt_file}")
    console.print(f"  Code:   {code_file}")

    # 3. Mock the Click Context
    # cmd_test_main expects a click.Context with specific objects in ctx.obj
    # This simulates the global flags passed to the CLI (e.g., --verbose, --local)
    class MockContext:
        def __init__(self):
            self.obj = {
                "verbose": True,
                "force": True,      # Force overwrite without prompting
                "quiet": False,
                "local": True,      # Force local execution for this example
                "context": None,    # No specific context override
                "confirm_callback": None,
                "strength": 0.5,    # Default strength
                "temperature": 0.0, # Default temperature
                "time": 0.25        # Default thinking time
            }
        
        def exit(self, code=0):
            # Mock exit to prevent script termination
            console.print(f"[yellow]Context exit called with code: {code}[/yellow]")

    ctx = MockContext()

    # 4. Call cmd_test_main
    # We pass explicit None for optional parameters we don't want to override
    console.print("\n[bold blue]Running cmd_test_main...[/bold blue]")
    
    unit_test_code, total_cost, model_name = cmd_test_main(
        ctx=ctx,
        prompt_file=str(prompt_file),
        code_file=str(code_file),
        output=str(test_output_file),
        language="python",          # Explicitly set language
        coverage_report=None,       # Not using coverage report mode
        existing_tests=None,        # No existing tests
        target_coverage=None,       # Not targeting specific coverage
        merge=False,                # Not merging
        strength=None,              # Use context default
        temperature=None            # Use context default
    )

    # 5. Display Results
    console.print("\n[bold green]Execution Complete![/bold green]")
    console.print(f"Model Used: {model_name}")
    console.print(f"Total Cost: ${total_cost:.6f}")
    
    if unit_test_code:
        console.print(f"\n[bold]Generated Test Code (Preview):[/bold]")
        console.print(unit_test_code[:200] + "...\n(truncated)")
        
        # Verify file creation
        if test_output_file.exists():
            console.print(f"[green]Test file successfully saved to: {test_output_file}[/green]")
    else:
        console.print("[red]No test code was generated.[/red]")

if __name__ == "__main__":
    # Ensure PDD_PATH is set if needed by internal modules, though usually handled by installation
    if "PDD_PATH" not in os.environ:
        os.environ["PDD_PATH"] = os.getcwd()
        
    run_example()