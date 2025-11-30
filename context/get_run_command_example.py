#!/usr/bin/env python3
"""Example usage of the get_run_command module.

This module provides functions to retrieve run commands for programming languages
based on file extensions. It reads from a CSV configuration file located at
$PDD_PATH/data/language_format.csv.

The CSV file should have columns:
    - extension: The file extension (e.g., .py, .js)
    - run_command: The command template with {file} placeholder (e.g., python {file})

Prerequisites:
    - PDD_PATH environment variable must be set
    - language_format.csv must exist at $PDD_PATH/data/language_format.csv
"""

from pdd.get_run_command import get_run_command, get_run_command_for_file


def main():
    """Demonstrate usage of get_run_command module functions."""
    
    # ==========================================================================
    # Example 1: Get run command template for a Python file extension
    # ==========================================================================
    # Input: extension (str) - File extension with or without leading dot
    #        Examples: ".py", "py", ".JS", "js"
    # Output: str - Run command template with {file} placeholder
    #         Returns empty string if extension not found in CSV
    
    print("Example 1: Get run command for .py extension")
    print("-" * 50)
    
    python_command = get_run_command(".py")
    print(f"Extension: .py")
    print(f"Run command template: '{python_command}'")
    # Expected output: "python {file}" or similar
    print()
    
    # ==========================================================================
    # Example 2: Extension normalization (without dot, uppercase)
    # ==========================================================================
    # The function normalizes extensions:
    #   - Adds leading dot if missing
    #   - Converts to lowercase for matching
    
    print("Example 2: Extension normalization")
    print("-" * 50)
    
    # Without leading dot
    js_command = get_run_command("js")
    print(f"Extension: 'js' (no dot) -> Run command: '{js_command}'")
    
    # Uppercase extension
    py_upper_command = get_run_command(".PY")
    print(f"Extension: '.PY' (uppercase) -> Run command: '{py_upper_command}'")
    print()
    
    # ==========================================================================
    # Example 3: Get complete run command for a specific file
    # ==========================================================================
    # Input: file_path (str) - Full or relative path to the file to run
    # Output: str - Complete run command with {file} replaced by actual path
    #         Returns empty string if no run command available
    
    print("Example 3: Get complete run command for a file")
    print("-" * 50)
    
    file_path = "./output/my_script.py"
    complete_command = get_run_command_for_file(file_path)
    print(f"File path: {file_path}")
    print(f"Complete run command: '{complete_command}'")
    # Expected output: "python ./output/my_script.py" or similar
    print()
    
    # ==========================================================================
    # Example 4: Handle unknown extension
    # ==========================================================================
    # Returns empty string for extensions not in the CSV
    
    print("Example 4: Unknown extension handling")
    print("-" * 50)
    
    unknown_command = get_run_command(".xyz")
    print(f"Extension: .xyz")
    print(f"Run command: '{unknown_command}' (empty if not found)")
    
    if not unknown_command:
        print("No run command available for this extension")
    print()
    
    # ==========================================================================
    # Example 5: File without extension
    # ==========================================================================
    # Returns empty string for files without extensions
    
    print("Example 5: File without extension")
    print("-" * 50)
    
    no_ext_command = get_run_command_for_file("./output/Makefile")
    print(f"File: ./output/Makefile")
    print(f"Run command: '{no_ext_command}' (empty for no extension)")
    print()
    
    # ==========================================================================
    # Example 6: Various language extensions
    # ==========================================================================
    
    print("Example 6: Multiple language extensions")
    print("-" * 50)
    
    extensions = [".py", ".js", ".rb", ".sh", ".java"]
    for ext in extensions:
        cmd = get_run_command(ext)
        status = cmd if cmd else "(not configured)"
        print(f"{ext:8} -> {status}")


if __name__ == "__main__":
    main()
