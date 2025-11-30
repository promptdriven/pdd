#!/usr/bin/env python3
"""
Example usage of the pdd.core.errors module.

This module provides centralized error handling for the PDD CLI, including:
- Rich console output with custom theming for consistent styling
- Error buffer collection for optional core dumps
- Graceful error handling without crashing the CLI

The module exports:
- console: A Rich Console instance with custom theme for styled output
- handle_error(exception, command_name, quiet): Records and optionally prints errors
- get_core_dump_errors(): Returns list of collected error details
- clear_core_dump_errors(): Clears the error buffer
"""

import os

# Ensure output directory exists (relative to this script's location)
script_dir = os.path.dirname(os.path.abspath(__file__))
output_dir = os.path.join(script_dir, "output")
os.makedirs(output_dir, exist_ok=True)

# Import the error handling components from the errors module
from pdd.core.errors import (
    console,
    handle_error,
    get_core_dump_errors,
    clear_core_dump_errors,
)


def main():
    """
    Demonstrates the error handling functionality of the errors module.
    
    This example shows:
    1. Using the Rich console with custom theme styles
    2. Handling different exception types
    3. Collecting errors for core dump analysis
    4. Quiet mode vs verbose error output
    """
    
    # ==========================================================================
    # Example 1: Using the Rich console with custom theme
    # ==========================================================================
    # The console object has predefined styles: info, warning, error, success, path, command
    
    console.print("[info]This is an info message (cyan)[/info]")
    console.print("[warning]This is a warning message (yellow)[/warning]")
    console.print("[success]This is a success message (green)[/success]")
    console.print("[path]This is a path style (dim blue)[/path]")
    console.print("[command]This is a command style (bold magenta)[/command]")
    console.print()
    
    # ==========================================================================
    # Example 2: Handling a FileNotFoundError
    # ==========================================================================
    # Parameters:
    #   exception (Exception): The exception that was raised
    #   command_name (str): Name of the CLI command that encountered the error
    #   quiet (bool): If True, suppresses console output; errors still recorded
    
    console.print("[info]--- Handling FileNotFoundError (verbose mode) ---[/info]")
    file_error = FileNotFoundError("config.yaml not found in project root")
    handle_error(
        exception=file_error,
        command_name="generate",
        quiet=False  # Will print error to console
    )
    console.print()
    
    # ==========================================================================
    # Example 3: Handling a ValueError in quiet mode
    # ==========================================================================
    # In quiet mode, errors are recorded but not printed to console
    
    console.print("[info]--- Handling ValueError (quiet mode - no output expected) ---[/info]")
    value_error = ValueError("Invalid strength value: must be between 0.0 and 1.0")
    handle_error(
        exception=value_error,
        command_name="sync",
        quiet=True  # Will NOT print error to console, but still records it
    )
    console.print("[success]ValueError was handled silently (recorded but not printed)[/success]")
    console.print()
    
    # ==========================================================================
    # Example 4: Handling an IOError
    # ==========================================================================
    
    console.print("[info]--- Handling IOError ---[/info]")
    io_error = IOError("Failed to write to output file: permission denied")
    handle_error(
        exception=io_error,
        command_name="test",
        quiet=False
    )
    console.print()
    
    # ==========================================================================
    # Example 5: Handling a generic/unexpected exception
    # ==========================================================================
    
    console.print("[info]--- Handling unexpected RuntimeError ---[/info]")
    runtime_error = RuntimeError("Unexpected state in workflow execution")
    handle_error(
        exception=runtime_error,
        command_name="crash",
        quiet=False
    )
    console.print()
    
    # ==========================================================================
    # Example 6: Retrieving collected errors for core dump
    # ==========================================================================
    # get_core_dump_errors() returns a list of dictionaries with error details:
    #   - command (str): The command name where error occurred
    #   - type (str): The exception class name (e.g., "FileNotFoundError")
    #   - message (str): The exception message
    #   - traceback (str): Full formatted traceback string
    
    console.print("[info]--- Retrieving collected errors ---[/info]")
    errors = get_core_dump_errors()
    console.print(f"[success]Total errors collected: {len(errors)}[/success]")
    
    for i, error in enumerate(errors, 1):
        console.print(f"\n[command]Error {i}:[/command]")
        console.print(f"  Command: [path]{error['command']}[/path]")
        console.print(f"  Type: {error['type']}")
        console.print(f"  Message: {error['message']}")
        # Traceback is available but typically long, showing first line only
        traceback_preview = error['traceback'].split('\n')[0] if error['traceback'] else "N/A"
        console.print(f"  Traceback (first line): {traceback_preview}...")
    
    # ==========================================================================
    # Example 7: Writing errors to a file for core dump
    # ==========================================================================
    
    import json
    
    core_dump_path = os.path.join(output_dir, "core_dump_errors.json")
    with open(core_dump_path, "w") as f:
        json.dump(errors, f, indent=2)
    console.print(f"\n[success]Core dump written to: output/core_dump_errors.json[/success]")
    
    # ==========================================================================
    # Example 8: Clearing the error buffer
    # ==========================================================================
    # clear_core_dump_errors() removes all collected errors from the buffer
    
    console.print("\n[info]--- Clearing error buffer ---[/info]")
    clear_core_dump_errors()
    errors_after_clear = get_core_dump_errors()
    console.print(f"[success]Errors after clearing: {len(errors_after_clear)}[/success]")
    
    # ==========================================================================
    # Example 9: Demonstrating error handling doesn't raise exceptions
    # ==========================================================================
    # handle_error() does NOT re-raise exceptions - it gracefully handles them
    # This allows the CLI to continue or exit cleanly
    
    console.print("\n[info]--- Demonstrating graceful handling (no exception raised) ---[/info]")
    critical_error = Exception("Critical failure in processing")
    handle_error(
        exception=critical_error,
        command_name="fix",
        quiet=False
    )
    console.print("[success]Execution continued after handle_error() - no exception raised![/success]")


if __name__ == "__main__":
    main()
