#!/usr/bin/env python3
"""
Example usage of the PDD CLI module.

This example demonstrates how to use the main CLI entry point and its
global options programmatically. The CLI module provides:

1. PDDCLI - A custom Click Group with enhanced help formatting and error handling
2. cli - The main entry point with global options for all PDD commands
3. process_commands - A result callback that summarizes command execution

The CLI supports the following global options:
- --force: Overwrite existing files without confirmation
- --strength: AI model strength (0.0-1.0, default 0.5)
- --temperature: AI model temperature (0.0-2.0, default 0.0)
- --time: Reasoning allocation for LLMs (0.0-1.0)
- --verbose: Increase output verbosity
- --quiet: Decrease output verbosity
- --output-cost: Path to CSV file for cost tracking
- --review-examples: Review few-shot examples before execution
- --local: Run commands locally instead of cloud
- --context: Override automatic context detection
- --list-contexts: List available contexts and exit
- --core-dump: Write debug bundle for bug reports

File Structure (relative to project root):
    pdd/
        core/
            cli.py          # The CLI module being demonstrated
            errors.py       # Error handling utilities
            dump.py         # Core dump functionality
            utils.py        # CLI utility functions
    output/                 # Directory for example outputs
"""

import os
import sys
from click.testing import CliRunner

# Import the CLI entry point from the pdd.core.cli module
from pdd.core.cli import cli, PDDCLI


def example_show_help():
    """
    Demonstrate displaying the CLI help message.
    
    The PDDCLI class customizes the help output to include a
    "Generate Suite" section highlighting related commands:
    - generate: Create runnable code from a prompt file
    - test: Generate or enhance unit tests for a code file
    - example: Generate example code from a prompt and implementation
    
    Returns:
        str: The help output text
    """
    runner = CliRunner()
    result = runner.invoke(cli, ['--help'])
    print("=== CLI Help Output ===")
    print(result.output)
    return result.output


def example_show_version():
    """
    Demonstrate displaying the CLI version.
    
    Returns:
        str: The version string output
    """
    runner = CliRunner()
    result = runner.invoke(cli, ['--version'])
    print("=== CLI Version ===")
    print(result.output)
    return result.output


def example_list_contexts():
    """
    Demonstrate listing available contexts from .pddrc configuration.
    
    The --list-contexts flag reads the nearest .pddrc file (searching
    upward from the current directory), prints available context names
    one per line, and exits with status 0.
    
    Returns:
        tuple: (exit_code, output_text)
            - exit_code (int): 0 on success, non-zero on error
            - output_text (str): List of context names or error message
    """
    runner = CliRunner()
    result = runner.invoke(cli, ['--list-contexts'])
    print("=== Available Contexts ===")
    print(result.output)
    return result.exit_code, result.output


def example_invoke_with_global_options():
    """
    Demonstrate invoking the CLI with various global options.
    
    This example shows how global options are passed and stored in
    the Click context object (ctx.obj). These options affect all
    subcommands:
    
    Global Options Demonstrated:
        --strength (float): AI model strength from 0.0 (cheapest) to 1.0 (most powerful)
            Default: 0.5
        --temperature (float): AI model temperature from 0.0 to 2.0
            Default: 0.0 (deterministic)
        --time (float): Reasoning allocation for LLMs from 0.0 to 1.0
            Default: Uses DEFAULT_TIME from pdd package
        --verbose (bool): Enable detailed output
            Default: False
        --quiet (bool): Minimize output (suppresses verbose)
            Default: False
        --force (bool): Overwrite files without confirmation
            Default: False
        --local (bool): Run locally instead of cloud
            Default: False
    
    Returns:
        dict: The context object containing all parsed options
    """
    runner = CliRunner()
    
    # Invoke with multiple global options
    # Note: Without a subcommand, CLI shows help and exits gracefully
    result = runner.invoke(cli, [
        '--strength', '0.8',
        '--temperature', '0.5',
        '--time', '0.3',
        '--verbose',
        '--force',
        '--local'
    ])
    
    print("=== CLI Invocation with Global Options ===")
    print(f"Exit code: {result.exit_code}")
    print(f"Output:\n{result.output}")
    
    return result


def example_quiet_mode():
    """
    Demonstrate quiet mode which suppresses verbose output.
    
    When --quiet is enabled:
    - Verbose mode is automatically disabled even if --verbose is passed
    - Minimal information is displayed
    - Auto-update messages are suppressed
    - Command summaries are suppressed
    
    Returns:
        tuple: (exit_code, output_text)
    """
    runner = CliRunner()
    
    # Quiet mode suppresses most output
    result = runner.invoke(cli, ['--quiet'])
    
    print("=== Quiet Mode ===")
    print(f"Exit code: {result.exit_code}")
    print(f"Output length: {len(result.output)} characters")
    
    return result.exit_code, result.output


def example_cost_tracking_setup():
    """
    Demonstrate setting up cost tracking with --output-cost.
    
    The --output-cost option enables cost tracking and specifies
    where to save the CSV file with usage details.
    
    CSV Output Columns:
        - timestamp: Date and time of command execution
        - model: AI model used for the operation
        - command: PDD command that was executed
        - cost: Estimated cost in USD (e.g., 0.05 for 5 cents)
        - input_files: List of input files involved
        - output_files: List of output files generated/modified
    
    Args:
        None
    
    Returns:
        str: Path to the cost tracking CSV file
    """
    # Ensure output directory exists
    os.makedirs('./output', exist_ok=True)
    
    cost_file = './output/pdd_costs.csv'
    
    runner = CliRunner()
    result = runner.invoke(cli, [
        '--output-cost', cost_file,
        '--quiet'
    ])
    
    print("=== Cost Tracking Setup ===")
    print(f"Cost tracking file: {cost_file}")
    print(f"Exit code: {result.exit_code}")
    
    return cost_file


def example_context_override():
    """
    Demonstrate context override with --context option.
    
    The --context option allows overriding automatic context detection
    to use a specific context from .pddrc configuration.
    
    Context settings can include:
        - generate_output_path: Where generated code files are saved
        - test_output_path: Where test files are saved
        - example_output_path: Where example files are saved
        - default_language: Default programming language
        - target_coverage: Default test coverage target (percentage)
        - strength: Default AI model strength (0.0-1.0)
        - temperature: Default AI model temperature
        - budget: Default budget for iterative commands (in USD)
        - max_attempts: Default maximum attempts for fixing operations
    
    Returns:
        tuple: (exit_code, output_text)
    """
    runner = CliRunner()
    
    # This will fail validation if 'backend' context doesn't exist
    # but demonstrates the usage pattern
    result = runner.invoke(cli, [
        '--context', 'default',
        '--quiet'
    ])
    
    print("=== Context Override ===")
    print(f"Exit code: {result.exit_code}")
    if result.exception:
        print(f"Note: Context validation requires .pddrc file")
    
    return result.exit_code, result.output


def example_core_dump_flag():
    """
    Demonstrate the --core-dump flag for debug bundles.
    
    When --core-dump is set, PDD captures:
        - Full CLI command and arguments
        - Relevant logs and internal trace information
        - Prompt files, generated code, and key metadata
    
    The core dump is saved to .pdd/core_dumps/ directory and can be
    attached to bug reports for maintainers to reproduce issues.
    
    Returns:
        tuple: (exit_code, output_text)
    """
    runner = CliRunner()
    
    result = runner.invoke(cli, [
        '--core-dump',
        '--quiet'
    ])
    
    print("=== Core Dump Flag ===")
    print(f"Exit code: {result.exit_code}")
    print("Core dump would be saved to .pdd/core_dumps/")
    
    return result.exit_code, result.output


def example_pddcli_class_usage():
    """
    Demonstrate the PDDCLI custom Click Group class.
    
    PDDCLI extends click.Group with:
    
    1. Custom help formatting (format_help method):
       - Adds "Generate Suite" section with related commands
       - Shows generate, test, and example commands together
    
    2. Centralized error handling (invoke method):
       - Catches exceptions and routes to handle_error()
       - Writes core dumps even on failure
       - Returns appropriate exit codes:
         - 0: Success
         - 1: General error
         - 2: Usage error (invalid arguments)
    
    Returns:
        type: The PDDCLI class for inspection
    """
    print("=== PDDCLI Class ===")
    print(f"Class name: {PDDCLI.__name__}")
    print(f"Base class: {PDDCLI.__bases__}")
    print(f"Custom methods: format_help, invoke")
    
    # Show that cli uses PDDCLI
    print(f"CLI uses PDDCLI: {type(cli).__name__ == 'PDDCLI'}")
    
    return PDDCLI


def main():
    """
    Run all CLI examples.
    
    This demonstrates the complete functionality of the PDD CLI module
    including help display, version info, global options, and special
    flags like --list-contexts and --core-dump.
    """
    print("\n" + "="*60)
    print("PDD CLI Module Examples")
    print("="*60 + "\n")
    
    # Ensure output directory exists
    os.makedirs('./output', exist_ok=True)
    
    # Run examples
    example_show_version()
    print("\n" + "-"*40 + "\n")
    
    example_pddcli_class_usage()
    print("\n" + "-"*40 + "\n")
    
    example_invoke_with_global_options()
    print("\n" + "-"*40 + "\n")
    
    example_quiet_mode()
    print("\n" + "-"*40 + "\n")
    
    example_cost_tracking_setup()
    print("\n" + "-"*40 + "\n")
    
    example_core_dump_flag()
    print("\n" + "-"*40 + "\n")
    
    # These may produce errors if .pddrc doesn't exist, which is expected
    example_list_contexts()
    print("\n" + "-"*40 + "\n")
    
    example_context_override()
    print("\n" + "-"*40 + "\n")
    
    # Show help last as it's verbose
    example_show_help()
    
    print("\n" + "="*60)
    print("All CLI examples completed")
    print("="*60 + "\n")


if __name__ == '__main__':
    main()