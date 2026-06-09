from __future__ import annotations

import os
import sys
import pathlib
from typing import Any, Dict, Tuple
from unittest.mock import patch
import click
from rich.console import Console

# Resolve the absolute path to the 'pdd' package parent to ensure imports work
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))

from pdd.code_generator_main import (
    code_generator_main,
    ArchitectureConformanceError,
    PublicSurfaceRegressionError,
    TestChurnError,
)

console = Console()


def prepare_workspace() -> Tuple[pathlib.Path, pathlib.Path]:
    """Prepares a temporary output directory and mock files for the generator."""
    output_dir = pathlib.Path("./output").resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a dummy .prompt file
    prompt_file = output_dir / "calculator.prompt"
    prompt_file.write_text(
        """---
title: Calculator Module
language: Python
---
<pdd-reason>Simple mathematical operations utility.</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "add", "signature": "(a: int, b: int) -> int"}
    ]
  }
}
</pdd-interface>

Generate a Python function named 'add' that takes two integers and returns their sum.
""",
        encoding="utf-8",
    )

    # 2. Create a dummy existing code file to simulate regression testing
    existing_code_file = output_dir / "calculator.py"
    existing_code_file.write_text(
        "def add(a: int, b: int) -> int:\n    return a + b\n",
        encoding="utf-8",
    )

    return prompt_file, existing_code_file


def run_generation_example() -> None:
    """Orchestrates a mock local execution of code_generator_main."""
    console.print("[bold blue]Setting up mock workspace...[/bold blue]")
    prompt_file, output_file = prepare_workspace()

    # Create a simulated Click Context with CLI configuration parameters
    @click.command()
    def cli_stub() -> None:
        pass

    ctx = click.Context(
        cli_stub,
        obj={
            "local": True,        # Prefer local LLM generation
            "strength": 0.5,      # Prompt strength threshold (0.0 to 1.0)
            "temperature": 0.0,   # Sampling temperature (0.0 to 2.0)
            "time": 0.25,         # Thinking effort budget (0.0 to 1.0)
            "verbose": True,      # Enable detailed rich console logging
            "force": True,        # Overwrite existing files
        },
    )

    # We mock the internal local LLM generator function to isolate the test from 
    # external LLM weights or credentials, ensuring it runs reliably in any environment.
    mock_llm_response = (
        "def add(a: int, b: int) -> int:\n"
        "    # Simulated generated implementation\n"
        "    return a + b\n"
    )

    console.print("\n[bold green]Executing code_generator_main...[/bold green]")

    # Disable strict conformance and regression gates for this initial positive path
    os.environ["PDD_SKIP_CONFORMANCE"] = "1"
    os.environ["PDD_SKIP_PUBLIC_SURFACE_GATE"] = "1"

    with patch("pdd.code_generator_main.local_code_generator_func") as mock_gen:
        # Mock returns (generated_code, total_cost, model_name)
        mock_gen.return_value = (mock_llm_response, 0.0015, "mock-gpt-4o")

        generated_code, was_incremental, cost, model = code_generator_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            output=str(output_file),
            original_prompt_file_path=None,
            force_incremental_flag=False,
            env_vars={"APP_NAME": "DemoCalculator"},
        )

        console.print("\n[bold cyan]Generation Results:[/bold cyan]")
        console.print(f"Was Incremental: [yellow]{was_incremental}[/yellow]")
        console.print(f"Total Cost: [yellow]${cost:.6f}[/yellow] USD")
        console.print(f"Model Name: [yellow]{model}[/yellow]")
        console.print(f"Generated Output Code:\n[dim]{generated_code}[/dim]")


def run_error_handling_example() -> None:
    """Demonstrates how to catch and handle ArchitectureConformanceError."""
    console.print("\n[bold blue]Demonstrating Architecture Conformance Error...[/bold blue]")
    prompt_file, output_file = prepare_workspace()

    # Re-enable architecture conformance validation
    if "PDD_SKIP_CONFORMANCE" in os.environ:
        del os.environ["PDD_SKIP_CONFORMANCE"]

    @click.command()
    def cli_stub() -> None:
        pass

    ctx = click.Context(cli_stub, obj={"local": True, "verbose": False})

    # We mock the generator to return code missing the required "add" function
    # declared in the prompt's <pdd-interface> block.
    invalid_code = "def subtract(a: int, b: int) -> int:\n    return a - b\n"

    with patch("pdd.code_generator_main.local_code_generator_func") as mock_gen:
        mock_gen.return_value = (invalid_code, 0.002, "mock-gpt-4o")

        try:
            code_generator_main(
                ctx=ctx,
                prompt_file=str(prompt_file),
                output=str(output_file),
                original_prompt_file_path=None,
                force_incremental_flag=False,
            )
        except ArchitectureConformanceError as err:
            console.print("[bold red]Successfully caught Conformance Error![/bold red]")
            console.print(f"Prompt Name: [yellow]{err.prompt_name}[/yellow]")
            console.print(f"Missing Exports: [yellow]{err.missing_symbols}[/yellow]")
            console.print(f"Failed Model: [yellow]{err.model_name}[/yellow]")
            console.print(f"Cost Incurred: [yellow]${err.total_cost:.6f}[/yellow]")
            console.print("\n[bold cyan]Repair Directive generated for LLM retry:[/bold cyan]")
            console.print(f"[dim]{err.repair_directive}[/dim]")


if __name__ == "__main__":
    run_generation_example()
    run_error_handling_example()