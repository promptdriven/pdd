from __future__ import annotations

"""
Example demonstrating how to programmatically use the `sync_main` module.

This script sets up a simulated workspace in the `./output` directory,
configures a mock Click Context, and invokes the `sync_main` function
to run a synchronization analysis and execution workflow using mock patches.
"""

import json
import os
import shutil
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import click
from rich.console import Console

# Import the sync_main function from the pdd package
from pdd.sync_main import sync_main

# Setup directories relative to this script
BASE_DIR = Path(__file__).resolve().parent
OUTPUT_DIR = BASE_DIR / "output"


def setup_mock_project() -> tuple[Path, Path]:
    """
    Creates a temporary local directory structure and mock prompt file
    to simulate a real PDD workspace environment.
    """
    if OUTPUT_DIR.exists():
        shutil.rmtree(OUTPUT_DIR)

    prompts_dir = OUTPUT_DIR / "prompts"
    code_dir = OUTPUT_DIR / "src"
    tests_dir = OUTPUT_DIR / "tests"

    prompts_dir.mkdir(parents=True, exist_ok=True)
    code_dir.mkdir(parents=True, exist_ok=True)
    tests_dir.mkdir(parents=True, exist_ok=True)

    # Write a simulated Python development prompt file
    python_prompt = prompts_dir / "calculator_python.prompt"
    python_prompt.write_text(
        "Create a calculator module with an `add` function.", encoding="utf-8"
    )

    return prompts_dir, code_dir


def main() -> None:
    console = Console()

    console.rule("[bold green]1. Preparing Mock Workspace[/bold green]")
    prompts_dir, code_dir = setup_mock_project()
    console.print(f"Mock workspace initialized under: [cyan]{OUTPUT_DIR}[/cyan]")

    console.rule("[bold green]2. Configuring Click Context[/bold green]")

    # Programmatic instantiation of Click Context to simulate CLI state
    ctx = click.Context(click.Command("sync"))
    ctx.obj = {
        "strength": 0.5,  # LLM selection strength (0.0 to 1.0)
        "temperature": 0.0,  # Sampling temperature (0.0 for deterministic)
        "time": 0.25,  # Reasoning limit token allocation ratio (0.0 to 1.0)
        "verbose": True,  # Enable detail-rich logging
        "force": True,  # Avoid interactive block prompts
        "quiet": False,  # Allow rich screen outputs
        "output_cost": None,  # Cost tracking CSV path (None to disable)
        "review_examples": False,  # Skip manual few-shot reviews
        "local": True,  # Run locally rather than utilizing Cloud executors
        "context": None,  # Custom .pddrc context override
    }

    # Simulate programmatic CLI command line source resolution
    mock_source = MagicMock()
    mock_source.name = "COMMANDLINE"
    ctx.get_parameter_source = MagicMock(return_value=mock_source)

    console.rule("[bold green]3. Patching Downstream Sub-Orchestrators[/bold green]")

    # Mock construct_paths to redirect resolving logic to our mock './output' directory
    def mock_construct_paths(*args, **kwargs):
        resolved_config = {
            "prompts_dir": str(prompts_dir),
            "code_dir": str(code_dir),
            "tests_dir": str(OUTPUT_DIR / "tests"),
            "examples_dir": str(OUTPUT_DIR / "examples"),
            "target_coverage": 90.0,
            "max_attempts": 3,
            "budget": 20.0,
        }
        return resolved_config, {}, {}, "python"

    # Mock sync_orchestration to simulate successful code-generation and unit testing
    def mock_sync_orchestration(*args, **kwargs):
        return {
            "success": True,
            "total_cost": 0.0425,
            "summary": "Calculator module generated successfully. 3/3 tests passed with 95% coverage.",
            "model_name": "mock-gpt-4o-developer",
            "operations_completed": ["auto-deps", "generate", "test", "verify"],
        }

    console.rule("[bold green]4. Programmatically Executing PDD Sync[/bold green]")

    # Run sync_main safely in a patched execution sandbox
    with (
        patch("pdd.sync_main.construct_paths", side_effect=mock_construct_paths),
        patch(
            "pdd.sync_main.sync_orchestration", side_effect=mock_sync_orchestration
        ),
    ):
        # sync_main Arguments and Parameters:
        # - ctx (click.Context): Context holding shared configuration flags
        # - basename (str): Name of target prompt without suffix (e.g. "calculator")
        # - max_attempts (int | None): Max allowed iterative fixes. None = use config defaults.
        # - budget (float | None): Limit on LLM billing in USD
        # - skip_verify (bool): Skip semantic LLM-judge verification
        # - skip_tests (bool): Skip generating and running unit tests
        # - target_coverage (float): Code coverage percentage boundary
        # - dry_run (bool): Analyze configuration state and exit without writing files
        #
        # Returns:
        # - Tuple[Dict[str, Any], float, str]: (workflow_results, total_cost_usd, primary_model_used)
        results, total_cost, primary_model = sync_main(
            ctx=ctx,
            basename="calculator",
            max_attempts=3,
            budget=10.00,
            skip_verify=False,
            skip_tests=False,
            target_coverage=90.0,
            dry_run=False,
            one_session=False,
            compress=False,
            evidence=False,
            snapshot_context=False,
            compressed_context=False,
        )

    console.rule("[bold blue]5. Sync Output Analysis[/bold blue]")
    status = (
        "[bold green]Success[/bold green]"
        if results.get("overall_success")
        else "[bold red]Failure[/bold red]"
    )
    console.print(f"Overall Status: {status}")
    console.print(f"Total Billable Cost:  [yellow]${total_cost:.4f} USD[/yellow]")
    console.print(f"Primary Solver Model: [cyan]{primary_model}[/cyan]")
    console.print("\n[bold]Aggregated Results JSON:[/bold]")
    console.print(json.dumps(results, indent=2))

    # Clean up mock directories
    if OUTPUT_DIR.exists():
        shutil.rmtree(OUTPUT_DIR)


if __name__ == "__main__":
    main()