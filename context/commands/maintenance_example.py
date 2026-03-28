#!/usr/bin/env python3
"""
Example demonstrating how to use the maintenance commands module.

This module provides three Click commands for PDD maintenance operations:
- sync: Synchronize prompts with code and tests
- auto-deps: Analyze and inject dependencies into prompt files
- setup: Run the interactive setup utility

The commands are designed to be invoked via the Click CLI framework.
"""

import os
import shutil
from pathlib import Path
from unittest.mock import MagicMock, patch

import click
from click.testing import CliRunner

# Import the maintenance commands from the pdd package
from pdd.commands.maintenance import sync, auto_deps, setup


def setup_output_directory() -> Path:
    """
    Create and return a clean output directory for the example.

    Returns:
        Path: Path to the output directory (./output relative to script location).
    """
    script_dir = os.path.dirname(os.path.abspath(__file__))
    output_dir = Path(script_dir) / "output"
    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    return output_dir


def create_mock_project(output_dir: Path) -> dict:
    """
    Create a mock project structure for demonstrating the commands.

    Args:
        output_dir: Base directory for the mock project.

    Returns:
        dict: Paths to created files and directories.
    """
    prompts_dir = output_dir / "prompts"
    src_dir = output_dir / "src"
    examples_dir = output_dir / "examples"

    for d in [prompts_dir, src_dir, examples_dir]:
        d.mkdir(parents=True, exist_ok=True)

    prompt_file = prompts_dir / "calculator_python.prompt"
    prompt_file.write_text(
        "% Create a Python calculator module with add, subtract, multiply, divide."
    )

    example_file = examples_dir / "math_utils_example.py"
    example_file.write_text("from math_utils import square\nresult = square(5)\n")

    csv_file = output_dir / "project_dependencies.csv"
    csv_file.write_text("full_path,file_summary,key_exports,dependencies,date\n")

    return {
        "prompts_dir": prompts_dir,
        "src_dir": src_dir,
        "examples_dir": examples_dir,
        "prompt_file": prompt_file,
        "example_file": example_file,
        "csv_file": csv_file,
    }


def example_sync_command():
    """
    Demonstrate the sync command via CliRunner.

    The sync command synchronizes prompts with code and tests. It accepts:
        basename (str): Base name of prompt or a GitHub issue URL
        max_attempts (Optional[int]): Max fix attempts (default: 3)
        budget (Optional[float]): Max cost in USD (default: 20.0)
        skip_verify (bool): Skip functional verification
        skip_tests (bool): Skip test generation
        target_coverage (Optional[float]): Code coverage target (default: 90.0)
        dry_run (bool): Analyze without executing
        no_steer (bool): Disable interactive steering
        steer_timeout (Optional[float]): Steering prompt timeout in seconds (default: 8.0)
        agentic (bool): Use agentic mode
        timeout_adder (float): Extra timeout per step (default: 0.0)
        no_github_state (bool): Disable GitHub state persistence
        one_session (Optional[bool]): Single agentic session mode

    Returns:
        Optional[Tuple[str, float, str]]:
            - result (str): JSON string with sync results
            - total_cost (float): Total cost in USD
            - model_name (str): AI model name
    """
    print("\n" + "=" * 60)
    print("SYNC COMMAND EXAMPLE")
    print("=" * 60)

    runner = CliRunner()

    mock_result = (
        {"overall_success": True, "languages_processed": ["python"]},
        0.05,  # Cost in USD
        "gpt-4",
    )

    with patch("pdd.commands.maintenance.sync_main", return_value=mock_result):

        @click.group()
        @click.pass_context
        def cli(ctx):
            ctx.ensure_object(dict)
            ctx.obj = {
                "strength": 0.5,
                "temperature": 0.0,
                "time": 0.25,
                "verbose": False,
                "force": True,
                "quiet": False,
                "output_cost": None,
                "review_examples": False,
                "local": True,
                "context": None,
            }

        cli.add_command(sync)

        result = runner.invoke(
            cli,
            [
                "sync",
                "calculator",
                "--max-attempts", "3",
                "--budget", "10.0",
                "--skip-verify",
                "--target-coverage", "80.0",
                "--no-steer",
            ],
            catch_exceptions=False,
        )

        print(f"Command exit code: {result.exit_code}")
        print(f"Command output:\n{result.output}")


def example_sync_dry_run():
    """
    Demonstrate sync --dry-run mode which analyzes state without executing.
    """
    print("\n" + "=" * 60)
    print("SYNC DRY-RUN EXAMPLE")
    print("=" * 60)

    runner = CliRunner()

    mock_result = (
        {"dry_run": True, "operations_recommended": ["generate", "test"]},
        0.0,
        "none",
    )

    with patch("pdd.commands.maintenance.sync_main", return_value=mock_result):

        @click.group()
        @click.pass_context
        def cli(ctx):
            ctx.ensure_object(dict)
            ctx.obj = {
                "strength": 0.5,
                "temperature": 0.0,
                "time": 0.25,
                "verbose": False,
                "force": False,
                "quiet": False,
                "output_cost": None,
                "review_examples": False,
                "local": True,
                "context": None,
            }

        cli.add_command(sync)

        result = runner.invoke(
            cli,
            ["sync", "calculator", "--dry-run"],
            catch_exceptions=False,
        )

        print(f"Command exit code: {result.exit_code}")
        print(f"Command output:\n{result.output}")


def example_sync_github_issue():
    """
    Demonstrate sync with a GitHub issue URL (agentic multi-module sync).

    When a GitHub issue URL is passed, sync dispatches to run_agentic_sync()
    instead of sync_main(). Returns (message, cost, model) on success.
    """
    print("\n" + "=" * 60)
    print("SYNC GITHUB ISSUE EXAMPLE (agentic mode)")
    print("=" * 60)

    runner = CliRunner()

    mock_agentic_result = (
        True,  # success
        "All 3 modules synced successfully",
        0.42,  # cost in USD
        "claude-3-opus",
    )

    with patch(
        "pdd.commands.maintenance.run_agentic_sync",
        return_value=mock_agentic_result,
    ), patch(
        "pdd.commands.maintenance._is_github_issue_url",
        return_value=True,
    ):

        @click.group()
        @click.pass_context
        def cli(ctx):
            ctx.ensure_object(dict)
            ctx.obj = {
                "strength": 0.5,
                "temperature": 0.0,
                "time": 0.25,
                "verbose": True,
                "force": True,
                "quiet": False,
                "output_cost": None,
                "review_examples": False,
                "local": False,
                "context": None,
            }

        cli.add_command(sync)

        result = runner.invoke(
            cli,
            [
                "sync",
                "https://github.com/org/repo/issues/42",
                "--timeout-adder", "30.0",
                "--no-github-state",
            ],
            catch_exceptions=False,
        )

        print(f"Command exit code: {result.exit_code}")
        print(f"Command output:\n{result.output}")


def example_auto_deps_command():
    """
    Demonstrate the auto-deps command.

    Parameters:
        prompt_file (str): Path to the prompt file to analyze
        directory_path (str): Directory or glob pattern for dependency search
        output (Optional[str]): Where to save modified prompt
        csv (Optional[str]): CSV file path for dependency info
        force_scan (bool): Force rescanning all files
        include_docs (bool): Include .md/.txt/.rst files
        no_dedup (bool): Skip inline content deduplication
        concurrency (int): Parallel LLM worker count (default: 1)

    Returns:
        Optional[Tuple[str, float, str]]:
            - result (str): Modified prompt content
            - total_cost (float): Cost in USD
            - model_name (str): AI model name
    """
    print("\n" + "=" * 60)
    print("AUTO-DEPS COMMAND EXAMPLE")
    print("=" * 60)

    output_dir = setup_output_directory()
    paths = create_mock_project(output_dir)

    runner = CliRunner()

    mock_result = (
        "Modified prompt with dependencies included",
        0.02,
        "gpt-4",
    )

    with patch("pdd.commands.maintenance.auto_deps_main", return_value=mock_result):

        @click.group()
        @click.pass_context
        def cli(ctx):
            ctx.ensure_object(dict)
            ctx.obj = {
                "strength": 0.5,
                "temperature": 0.0,
                "quiet": False,
            }

        cli.add_command(auto_deps)

        result = runner.invoke(
            cli,
            [
                "auto-deps",
                str(paths["prompt_file"]),
                str(paths["examples_dir"]),
                "--output", str(output_dir / "calculator_with_deps.prompt"),
                "--csv", str(paths["csv_file"]),
                "--force-scan",
            ],
            catch_exceptions=False,
        )

        print(f"Command exit code: {result.exit_code}")
        print(f"Command output:\n{result.output}")


def example_setup_command():
    """
    Demonstrate the setup command.

    The setup command:
    1. Installs shell tab completion
    2. Runs the setup utility (API keys, model config, etc.)

    No @track_cost decorator (no LLM calls).

    Returns:
        None
    """
    print("\n" + "=" * 60)
    print("SETUP COMMAND EXAMPLE")
    print("=" * 60)

    runner = CliRunner()

    with patch("pdd.cli.install_completion") as mock_install, \
         patch("pdd.commands.maintenance._run_setup_utility") as mock_setup:

        @click.group()
        @click.pass_context
        def cli(ctx):
            ctx.ensure_object(dict)
            ctx.obj = {"quiet": False}

        cli.add_command(setup)

        result = runner.invoke(cli, ["setup"], catch_exceptions=False)

        print(f"Command exit code: {result.exit_code}")
        print(f"Command output:\n{result.output}")
        print(f"install_completion called: {mock_install.called}")
        print(f"_run_setup_utility called: {mock_setup.called}")


def example_deprecated_log_flag():
    """
    Demonstrate that --log is deprecated in favor of --dry-run.
    The command emits a warning and treats --log as --dry-run.
    """
    print("\n" + "=" * 60)
    print("DEPRECATED --log FLAG EXAMPLE")
    print("=" * 60)

    runner = CliRunner()

    mock_result = ({"dry_run": True}, 0.0, "none")

    with patch("pdd.commands.maintenance.sync_main", return_value=mock_result) as mock_sync:

        @click.group()
        @click.pass_context
        def cli(ctx):
            ctx.ensure_object(dict)
            ctx.obj = {
                "strength": 0.5,
                "temperature": 0.0,
                "time": 0.25,
                "verbose": False,
                "force": False,
                "quiet": False,
                "output_cost": None,
                "review_examples": False,
                "local": True,
                "context": None,
            }

        cli.add_command(sync)

        result = runner.invoke(
            cli, ["sync", "my_module", "--log"], catch_exceptions=False
        )

        print(f"Command exit code: {result.exit_code}")
        print(f"Command output:\n{result.output}")
        # The --log flag should have been converted to dry_run=True
        if mock_sync.called:
            call_kwargs = mock_sync.call_args
            print(f"sync_main called with dry_run={call_kwargs.kwargs.get('dry_run', call_kwargs[1].get('dry_run', 'N/A'))}")


def main():
    """Main function to run all examples."""
    example_sync_command()
    example_sync_dry_run()
    example_sync_github_issue()
    example_auto_deps_command()
    example_setup_command()
    example_deprecated_log_flag()

    print("\n" + "=" * 60)
    print("All examples completed successfully!")


if __name__ == "__main__":
    main()
