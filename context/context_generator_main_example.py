"""
example_context_generator_main.py
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This example demonstrates how to use the `context_generator_main` function, which serves
as the CLI wrapper for generating example code (usage examples) for a given source code file.

The function handles:
1. Path resolution for inputs and outputs.
2. Cloud vs. Local execution logic (with automatic fallback).
3. Syntax validation and fixing for Python code.
4. Saving the generated example to disk.

Prerequisites:
- The `pdd` package must be installed or in the python path.
- Environment variables like `PDD_PATH` should be set if relying on default paths.
"""

import os
import sys
import click
from pathlib import Path
from rich.console import Console

# Adjust path to ensure we can import pdd modules if running from a different directory
# In a real installation, this would just be `from pdd.context_generator_main import context_generator_main`
sys.path.append(str(Path(__file__).parent.parent.parent))

from pdd.context_generator_main import context_generator_main

console = Console()

# ---------------------------------------------------------------------------
# 1. Setup Mock Data and Files
# ---------------------------------------------------------------------------
# We need a prompt file and a code file to generate an example for.
output_dir = Path("output")
output_dir.mkdir(exist_ok=True)

prompt_file = output_dir / "calculator_python.prompt"
code_file = output_dir / "calculator.py"
example_output_file = output_dir / "calculator_example.py"

# Create a dummy prompt file
prompt_content = """
Task: Create a simple calculator class with add and subtract methods.
Language: Python
"""
prompt_file.write_text(prompt_content, encoding="utf-8")

# Create a dummy code file (the source for which we want an example)
code_content = """
class Calculator:
    def add(self, a: float, b: float) -> float:
        return a + b

    def subtract(self, a: float, b: float) -> float:
        return a - b
"""
code_file.write_text(code_content, encoding="utf-8")

console.print(f"[bold blue]Created mock files in:[/bold blue] {output_dir}")

# ---------------------------------------------------------------------------
# 2. Prepare the Click Context
# ---------------------------------------------------------------------------
# context_generator_main expects a Click Context object populated with
# configuration options usually provided by CLI flags.

# Create a dummy Click command to act as the parent
@click.command()
def dummy_command():
    pass

# Initialize the context
ctx = click.Context(dummy_command)

# Populate ctx.obj with standard PDD global options
ctx.obj = {
    'verbose': True,          # Enable detailed logging
    'strength': 0.5,          # AI model strength (0.0 - 1.0)
    'temperature': 0.2,       # AI creativity (0.0 - 1.0)
    'time': None,             # Thinking time (optional)
    'force': True,            # Overwrite existing files
    'quiet': False,           # Show output
    'local': True,            # Force local execution for this example (avoids API keys)
    'context': None,          # Optional context directory override
    'confirm_callback': None  # Optional TUI callback
}

# ---------------------------------------------------------------------------
# 3. Run the Generator
# ---------------------------------------------------------------------------
console.print("\n[bold green]Running context_generator_main...[/bold green]")

try:
    # The function returns a tuple: (generated_code, total_cost, model_name)
    generated_code, total_cost, model_name = context_generator_main(
        ctx=ctx,
        prompt_file=str(prompt_file),
        code_file=str(code_file),
        output=str(example_output_file)
    )

    # ---------------------------------------------------------------------------
    # 4. Inspect Results
    # ---------------------------------------------------------------------------
    console.print("\n[bold]Generation Results:[/bold]")
    console.print(f"Model Used: {model_name}")
    console.print(f"Total Cost: ${total_cost:.6f}")
    console.print(f"Output Saved To: {example_output_file}")
    
    console.print("\n[bold]Generated Code Preview:[/bold]")
    console.print(generated_code)

except Exception as e:
    console.print(f"[bold red]Execution failed:[/bold red] {e}")

# ---------------------------------------------------------------------------
# 5. Cleanup (Optional)
# ---------------------------------------------------------------------------
# Uncomment to remove generated files
# import shutil
# shutil.rmtree(output_dir)