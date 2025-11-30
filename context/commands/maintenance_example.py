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
    output_dir = Path("./output")
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
    # Create directory structure
    prompts_dir = output_dir / "prompts"
    src_dir = output_dir / "src"
    examples_dir = output_dir / "examples"
    
    for d in [prompts_dir, src_dir, examples_dir]:
        d.mkdir(parents=True, exist_ok=True)
    
    # Create a sample prompt file
    prompt_file = prompts_dir / "calculator_python.prompt"
    prompt_file.write_text("""
% Create a Python calculator module with the following functions:
% - add(a, b): Returns the sum of two numbers
% - subtract(a, b): Returns the difference of two numbers
% - multiply(a, b): Returns the product of two numbers
% - divide(a, b): Returns the quotient of two numbers (handle division by zero)
""")
    
    # Create a sample code file for auto-deps
    example_file = examples_dir / "math_utils_example.py"
    example_file.write_text("""
# Example showing math utilities usage
from math_utils import square, cube

result = square(5)  # Returns 25
cube_result = cube(3)  # Returns 27
""")
    
    # Create a CSV file for auto-deps
    csv_file = output_dir / "project_dependencies.csv"
    csv_file.write_text("full_path,file_summary,date\n")
    
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
    Demonstrate the sync command usage.
    
    The sync command synchronizes prompts with code and tests. It:
    1. Finds prompt files matching the basename pattern
    2. Generates/updates code from prompts
    3. Creates examples and tests
    4. Fixes any issues found
    
    Command signature:
        sync(ctx, basename, max_attempts, budget, skip_verify, skip_tests, 
             target_coverage, log)
    
    Parameters:
        ctx (click.Context): Click context with global options in ctx.obj:
            - strength (float): AI model strength 0.0-1.0
            - temperature (float): AI model temperature
            - time (float): Reasoning allocation 0.0-1.0
            - verbose (bool): Verbose output
            - force (bool): Overwrite files without confirmation
            - quiet (bool): Minimal output
            - output_cost (Optional[str]): Path to CSV for cost tracking
            - review_examples (bool): Review generated examples
            - local (bool): Use local models if available
            - context (Optional[Path]): Path to a context directory
        basename (str): Base name of prompt file (e.g., 'calculator' for 
                       'prompts/calculator_python.prompt')
        max_attempts (int): Maximum fix attempts (default: 3)
        budget (float): Maximum cost in USD for sync process (default: 20.0)
        skip_verify (bool): Skip functional verification step
        skip_tests (bool): Skip unit test generation
        target_coverage (float): Desired code coverage percentage (default: 0.0)
        log (bool): Display sync logs instead of running sync
    
    Returns:
        Optional[Tuple[str, float, str]]: On success returns:
            - result (str): JSON string with sync results
            - total_cost (float): Total cost in USD
            - model_name (str): Name of the AI model used
        Returns None on error.
    """
    print("\n" + "=" * 60)
    print("SYNC COMMAND EXAMPLE")
    print("=" * 60)
    
    output_dir = setup_output_directory()
    paths = create_mock_project(output_dir)
    
    # Create a CLI runner for testing Click commands
    runner = CliRunner()
    
    # Mock the sync_main function to avoid actual LLM calls
    mock_result = (
        {"overall_success": True, "languages_processed": ["python"]},
        0.05,  # Cost in USD
        "gpt-4"
    )
    
    with patch("pdd.commands.maintenance.sync_main", return_value=mock_result):
        # Create a Click group to hold our command with context
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
        
        # Invoke the sync command
        result = runner.invoke(
            cli,
            [
                "sync",
                "calculator",  # basename argument
                "--max-attempts", "3",
                "--budget", "10.0",
                "--skip-verify",
                "--target-coverage", "80.0",
            ],
            catch_exceptions=False
        )
        
        print(f"Command exit code: {result.exit_code}")
        print(f"Command output:\n{result.output}")


def example_auto_deps_command():
    """
    Demonstrate the auto-deps command usage.
    
    The auto-deps command analyzes a prompt file and searches for potential
    dependencies in a directory, then inserts relevant includes into the prompt.
    
    Command signature:
        auto_deps(ctx, prompt_file, directory_path, output, csv, force_scan)
    
    Parameters:
        ctx (click.Context): Click context with global options in ctx.obj
        prompt_file (str): Path to the prompt file to analyze
        directory_path (str): Directory or glob pattern to search for dependencies
                             (e.g., 'examples/**/*.py' or 'context/')
        output (Optional[str]): Where to save the modified prompt file
        csv (Optional[str]): Path to CSV file for dependency information
                            (default: 'project_dependencies.csv')
        force_scan (bool): Force rescanning even if files exist in CSV
    
    Returns:
        Optional[Tuple[str, float, str]]: On success returns:
            - result (str): The modified prompt content
            - total_cost (float): Total cost in USD
            - model_name (str): Name of the AI model used
        Returns None on error.
    """
    print("\n" + "=" * 60)
    print("AUTO-DEPS COMMAND EXAMPLE")
    print("=" * 60)
    
    output_dir = setup_output_directory()
    paths = create_mock_project(output_dir)
    
    runner = CliRunner()
    
    # Mock the auto_deps_main function
    mock_result = (
        "Modified prompt with dependencies included",
        0.02,  # Cost in USD
        "gpt-4"
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
        
        # Invoke the auto-deps command
        result = runner.invoke(
            cli,
            [
                "auto-deps",
                str(paths["prompt_file"]),  # prompt_file argument
                str(paths["examples_dir"]),  # directory_path argument
                "--output", str(output_dir / "calculator_with_deps.prompt"),
                "--csv", str(paths["csv_file"]),
                "--force-scan",
            ],
            catch_exceptions=False
        )
        
        print(f"Command exit code: {result.exit_code}")
        print(f"Command output:\n{result.output}")


def example_setup_command():
    """
    Demonstrate the setup command usage.
    
    The setup command runs the interactive setup utility which:
    1. Installs shell tab completion
    2. Captures API keys
    3. Creates ~/.pdd configuration files
    4. Writes starter prompts
    
    Command signature:
        setup(ctx)
    
    Parameters:
        ctx (click.Context): Click context with global options in ctx.obj:
            - quiet (bool): Suppress output messages
    
    Returns:
        None: This command does not return a value.
    
    Note:
        This command is interactive and modifies system configuration.
        In this example, we mock the underlying functions to demonstrate
        the command structure without making actual system changes.
    """
    print("\n" + "=" * 60)
    print("SETUP COMMAND EXAMPLE")
    print("=" * 60)
    
    runner = CliRunner()
    
    # Mock both install_completion and _run_setup_utility
    # Note: cli_module is imported inside setup() as a local variable,
    # so we patch the actual function in pdd.cli instead
    with patch("pdd.cli.install_completion") as mock_install_completion:
        with patch("pdd.commands.maintenance._run_setup_utility") as mock_setup:
            @click.group()
            @click.pass_context
            def cli(ctx):
                ctx.ensure_object(dict)
                ctx.obj = {
                    "quiet": False,
                }
            
            cli.add_command(setup)
            
            result = runner.invoke(
                cli,
                ["setup"],
                catch_exceptions=False
            )
            
            print(f"Command exit code: {result.exit_code}")
            print(f"Command output:\n{result.output}")
            
            print(f"install_completion called: {mock_install_completion.called}")
            print(f"_run_setup_utility called: {mock_setup.called}")


def example_programmatic_usage():
    """
    Demonstrate calling sync command's callback programmatically.
    
    This shows how to directly invoke the underlying function associated
    with a Click command, bypassing the CLI parsing, but still respecting
    Click's context management (specifically for @click.pass_context).
    """
    print("\n" + "=" * 60)
    print("PROGRAMMATIC USAGE EXAMPLE")
    print("=" * 60)

    # Create a mock context for programmatic calls
    mock_obj = {
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
    # Manually create a context. We need to push this onto the stack
    # for @click.pass_context to work correctly when calling .callback() directly.
    ctx = click.Context(sync, obj=mock_obj)

    # Mock the sync_main function
    mock_result = (
        {"overall_success": True, "languages_processed": ["python"], "mocked_call": True},
        0.08,  # Cost in USD
        "claude-3-opus-20240229"
    )

    with patch("pdd.commands.maintenance.sync_main", return_value=mock_result):
        # Push the context onto Click's stack using ctx.scope() context manager
        # and remove ctx from callback arguments as it's injected by @click.pass_context
        with ctx.scope():
            result = sync.callback(
                basename="calculator",
                max_attempts=5,
                budget=15.0,
                skip_verify=False,
                skip_tests=False,
                target_coverage=90.0,
                log=False,
            )
        print(f"Programmatic sync result: {result}")
        # Note: sync command converts the result dict to a string (see maintenance.py line 77)
        # so we compare against the stringified version
        expected = (str(mock_result[0]), mock_result[1], mock_result[2])
        assert result == expected


def main():
    """Main function to run all examples."""
    setup_output_directory()  # Clean output dir at start
    
    example_sync_command()
    example_auto_deps_command()
    example_setup_command()
    example_programmatic_usage()
    
    print("\n" + "=" * 60)
    print("All examples completed successfully!")


if __name__ == "__main__":
    main()
