#!/usr/bin/env python3
"""
Example demonstrating how to use the `sync_main` CLI wrapper module programmatically.

This example sets up a mock environment inside an `./output` directory,
creates a simulated prompt file, configures a Click Context object,
and runs `sync_main` to orchestrate code generation and verification workflows.
"""

from __future__ import annotations

import json
import os
import shutil
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import click
from rich.console import Console

# Import the target function from the pdd package
from pdd.sync_main import sync_main


def setup_mock_project(output_dir: Path) -> None:
    """
    Creates a temporary local directory structure and mock prompt files
    to simulate a real PDD workspace environment.
    """
    if output_dir.exists():
        shutil.rmtree(output_dir)
    
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "src").mkdir(parents=True, exist_ok=True)
    (output_dir / "tests").mkdir(parents=True, exist_ok=True)

    # Write a simulated Python development prompt file
    python_prompt = prompts_dir / "calculator_python.prompt"
    python_prompt.write_text(
        "Create a calculator module with an `add` function.", 
        encoding="utf-8"
    )

    print(f"Set up mock project directory at: {output_dir.resolve()}")
    print(f"Created simulated prompt: {python_prompt.name}")


def main() -> None:
    console = Console()
    output_dir = Path("./output")

    console.rule("[bold green]1. Preparing Workspace[/bold green]")
    setup_mock_project(output_dir)

    console.rule("[bold green]2. Configuring Click Context[/bold green]")
    
    # Programmatic instantiation of Click Context to simulate CLI state
    ctx = click.Context(click.Command("sync"))
    ctx.obj = {
        "strength": 0.5,        # Default LLM selection strength (0.0 to 1.0)
        "temperature": 0.0,     # Sampling temperature (0.0 for deterministic)
        "time": 0.25,           # Reasoning limit token allocation ratio (0.0 to 1.0)
        "verbose": True,        # Enable detail-rich logging
        "force": True,          # Avoid prompt confirmation blocks
        "quiet": False,         # Output logging allowed
        "output_cost": None,    # Cost tracking CSV path (disabled)
        "review_examples": False,# Skip interactive few-shot reviews
        "local": True,          # Run locally rather than utilizing Cloud executors
        "context": None,        # Custom .pddrc context override
    }

    # Simulate programmatic source resolution
    mock_source = MagicMock()
    mock_source.name = "COMMANDLINE"
    ctx.get_parameter_source = MagicMock(return_value=mock_source)

    console.rule("[bold green]3. Mocking Downstream Sub-Orchestrators[/bold green]")
    
    # We mock construct_paths to point to our output directory
    def mock_construct_paths(*args, **kwargs):
        resolved_config = {
            "prompts_dir": str(output_dir / "prompts"),
            "code_dir": str(output_dir / "src"),
            "tests_dir": str(output_dir / "tests"),
            "target_coverage": 90.0,
            "max_attempts": 3,
            "budget": 20.0
        }
        # Returns (resolved_config, input_strings, output_file_paths, resolved_language)
        return resolved_config, {}, {}, "python"

    # We mock sync_orchestration to simulate successful execution of the workflow
    def mock_sync_orchestration(*args, **kwargs):
        return {
            "success": True,
            "total_cost": 0.0425,  # Estimated Cost in USD
            "summary": "Calculator module generated successfully. 3/3 tests passed.",
            "model_name": "mock-gpt-4o-developer",
            "operations_completed": ["auto-deps", "generate", "test", "verify"]
        }

    console.rule("[bold green]4. Running PDD Sync Wrapper[/bold green]")

    # Run sync_main with the simulated environment
    with patch("pdd.sync_main.construct_paths", side_effect=mock_construct_paths), \
         patch("pdd.sync_main.sync_orchestration", side_effect=mock_sync_orchestration):
        
        results, total_cost, primary_model = sync_main(
            ctx=ctx,
            basename="calculator",
            max_attempts=3,          # Cap iterative fixes at 3 loops
            budget=5.00,             # Total budget cap in USD
            skip_verify=False,       # Run semantic LLM-judge verification
            skip_tests=False,        # Run unit-tests generating and fixing
            target_coverage=90.0,    # Target unit-test coverage percentage
            dry_run=False,           # Execute operations
            one_session=False,       # Use classic step-wise loop mode
            compress=False,          # Disable source-include compression
            evidence=False           # Skip telemetry evidence manifest output
        )

    console.rule("[bold blue]5. Sync Output Summary[/bold blue]")
    print(f"Overall Success: {results.get('overall_success')}")
    print(f"Total Cost:      ${total_cost:.4f} USD")
    print(f"Primary Model:   {primary_model}")
    print("\nDetailed Workflow Results JSON:")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()