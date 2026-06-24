from __future__ import annotations

import os
import sys
from pathlib import Path
from typing import Any, Dict, Tuple

import click

# Import sync_main dynamically using the exact module name
from pdd.sync_main import sync_main


def setup_mock_environment(base_dir: Path) -> None:
    """Creates the directories and prompt files required for sync_main to discover the module.

    Args:
        base_dir: The directory acting as the project workspace root.
    """
    prompts_dir = base_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    # Write a mock prompt file for a 'math_utils' Python module
    prompt_path = prompts_dir / "math_utils_python.prompt"
    prompt_path.write_text(
        "Create a Python function `add(a: int, b: int) -> int` that returns the sum.",
        encoding="utf-8",
    )


def run_sync_example() -> Tuple[Dict[str, Any], float, str]:
    """Demonstrates how to programmatically invoke sync_main.

    This function configures a simulated Click Context with options, sets up
    the mock workspace environment under './output', and executes sync_main
    in dry_run mode to safely demonstrate orchestration without billing LLM APIs.

    Returns:
        A tuple containing:
            - results (Dict[str, Any]): A dictionary mapping synchronized
              languages to their execution results.
            - total_cost (float): Accumulated run cost in USD.
            - primary_model (str): Name of the primary AI model resolved/used.
    """
    # 1. Setup mock workspace in './output'
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)
    setup_mock_environment(output_dir)

    # 2. Configure a programmatic Click context
    # sync_main retrieves global execution options from ctx.obj.
    ctx = click.Context(click.Command("sync"))
    ctx.obj = {
        "strength": 0.5,           # Default model strength capability setting (0.0 to 1.0)
        "temperature": 0.0,        # Model temperature for predictable code output
        "time": 0.25,              # Allocated thinking/reasoning budget (0.0 to 1.0)
        "verbose": True,           # Enable detailed diagnostics log printing
        "force": True,             # Suppress interactive confirmation prompts
        "quiet": False,            # Let stdout output show progress animations
        "local": True,             # Instruct execution to run locally
        "context": None,           # Optional specific context override name from .pddrc
        "output_cost": None,       # CSV file path for audit logs
        "review_examples": False,  # Skip interactive few-shot example selection
    }

    # Avoid Click errors when resolving parameter sources programmatically
    ctx.get_parameter_source = lambda name: click.core.ParameterSource.DEFAULT

    # 3. Pivot working directory to './output' so the sync scanner detects files relatively
    original_cwd = os.getcwd()
    os.chdir(output_dir)

    try:
        print("Invoking sync_main in dry_run mode...")
        results, total_cost, primary_model = sync_main(
            ctx=ctx,
            basename="math_utils",
            max_attempts=3,
            budget=5.00,
            skip_verify=True,
            skip_tests=True,
            target_coverage=90.0,
            dry_run=True,  # Keeps execution non-interactive and free of LLM costs
            no_steer=True,
            one_session=False,
            compress=False,
            evidence=False,
            snapshot_context=False,
            compressed_context=False,
        )
    finally:
        os.chdir(original_cwd)

    return results, total_cost, primary_model


if __name__ == "__main__":
    results, cost, model = run_sync_example()
    print("\n--- Orchestration Dry-Run Summary ---")
    print(f"Results Dictionary: {results}")
    print(f"Total USD Billed: ${cost:.4f}")
    print(f"Resolved Model Name: {model}")