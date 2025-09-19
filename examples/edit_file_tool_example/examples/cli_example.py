# To run this example:
# From project root: python examples/cli_example.py
# Note: sys.path manipulation in this script ensures imports work from project root

import asyncio
import os
import shutil
import subprocess
import sys
from pathlib import Path

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

# Although we are demonstrating the CLI, we import these for model validation in the script
# This import is safe because it doesn't depend on the API key being set.
from edit_file_tool.claude_api import SUPPORTED_MODELS, DEFAULT_MODEL

# --- Helper Functions ---

def print_scenario_header(title: str):
    """Prints a formatted header for each demonstration scenario."""
    print("\n" + "=" * 70)
    print(f"--- SCENARIO: {title} ---")
    print("=" * 70)

def print_command(command_list: list[str]):
    """Prints the command to be executed in a readable format."""
    print(f"\n> Executing command:\n  {' '.join(command_list)}")

def read_file_content(file_path: Path) -> str:
    """
    Safely reads the content of a file.

    Args:
        file_path: The path to the file to read.

    Returns:
        The content of the file as a string, or an error message if reading fails.
    """
    if not file_path.exists():
        return f"File '{file_path.name}' does not exist."
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return f.read()
    except Exception as e:
        return f"Error reading file: {e}"

def run_cli_command(command: list[str], custom_env: dict | None = None) -> subprocess.CompletedProcess:
    """
    Runs a CLI command using subprocess and returns the result.

    Args:
        command: A list of strings representing the command and its arguments.
        custom_env: An optional custom environment for the subprocess.

    Returns:
        A CompletedProcess object with stdout, stderr, and returncode.
    """
    print_command(command)
    # We use sys.executable to ensure we're using the same Python interpreter
    # that is running this script.
    # We use '-m edit_file_tool.cli' to run the module directly, which is a
    # robust way to invoke it without relying on shell PATH resolution.
    full_command = [sys.executable, "-m", "edit_file_tool.cli"] + command
    
    # The `text=True` argument decodes stdout/stderr as text using the default encoding.
    # `capture_output=True` is a convenient way to get stdout and stderr.
    result = subprocess.run(
        full_command,
        capture_output=True,
        text=True,
        encoding='utf-8',
        errors='replace',
        env=custom_env
    )
    return result

def print_cli_result(result: subprocess.CompletedProcess):
    """
    Prints the stdout and stderr from a subprocess result.

    Args:
        result: The CompletedProcess object from a subprocess run.
    """
    print("\n--- Tool Output ---")
    if result.stdout:
        print(result.stdout.strip())
    if result.stderr:
        print("--- Errors/Warnings ---")
        print(result.stderr.strip())
    print("-------------------")
    print(f"Exit Code: {result.returncode}")


# --- Main Demonstration ---

def demonstrate_cli_usage():
    """
    Demonstrates the primary features of the edit_file_tool/cli.py module.

    This function showcases how to use the `edit-file` command-line tool
    for various scenarios, including:
    1. A simple, successful file edit.
    2. Using options like --verbose, --model, and --cache.
    3. Handling of a non-existent file path.
    4. Handling of a missing API key.
    """
    print_scenario_header("Module Demonstration: edit_file_tool/cli.py")

    if not os.environ.get("ANTHROPIC_API_KEY"):
        print("\nERROR: ANTHROPIC_API_KEY environment variable not set.")
        print("Please set your API key to run this example:")
        print("export ANTHROPIC_API_KEY='your-api-key-here'")
        return

    # Setup a temporary directory for the demonstration
    temp_dir = Path("./examples/temp_cli_demo")
    original_cwd = Path.cwd()

    try:
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
        temp_dir.mkdir(parents=True)
        print(f"Created temporary directory for demonstration: {temp_dir.resolve()}")

        # --- Scenario 1: Basic Successful Edit ---
        print_scenario_header("Basic Successful Edit")
        file_to_edit_1 = temp_dir / "config.txt"
        initial_content_1 = "version = 1.0"
        with open(file_to_edit_1, "w", encoding='utf-8') as f:
            f.write(initial_content_1)

        print(f"Initial content of '{file_to_edit_1.name}':\n---\n{initial_content_1}\n---")
        
        command_1 = [str(file_to_edit_1), "Update the version to 1.1"]
        result_1 = run_cli_command(command_1)
        print_cli_result(result_1)

        final_content_1 = read_file_content(file_to_edit_1)
        print(f"\nFinal content of '{file_to_edit_1.name}':\n---\n{final_content_1}\n---")
        if "version = 1.1" in final_content_1 and result_1.returncode == 0:
            print("Verification: SUCCESS - File content was updated correctly.")
        else:
            print("Verification: FAILED - File content was not updated as expected.")

        # --- Scenario 2: Using Options (--verbose, --model, --cache) ---
        print_scenario_header("Using Options: --verbose, --model, --cache")
        file_to_edit_2 = temp_dir / "main.py"
        initial_content_2 = "def hello():\n    print('Hello, old world!')"
        with open(file_to_edit_2, "w", encoding='utf-8') as f:
            f.write(initial_content_2)
        
        print(f"Initial content of '{file_to_edit_2.name}':\n---\n{initial_content_2}\n---")
        
        # Use a specific model and force caching
        model_to_use = os.getenv("EDIT_FILE_TOOL_MODEL", DEFAULT_MODEL)
        if model_to_use not in SUPPORTED_MODELS:
            print(f"Warning: Model '{model_to_use}' not in supported list. Using default.")
            model_to_use = DEFAULT_MODEL

        command_2 = [
            str(file_to_edit_2),
            "Change the printed string to 'Hello, new world!'",
            "--verbose",
            "--model", model_to_use,
            "--cache", "always"
        ]
        result_2 = run_cli_command(command_2)
        print_cli_result(result_2)

        final_content_2 = read_file_content(file_to_edit_2)
        print(f"\nFinal content of '{file_to_edit_2.name}':\n---\n{final_content_2}\n---")
        if "'Hello, new world!'" in final_content_2 and result_2.returncode == 0:
            print("Verification: SUCCESS - File was updated using specified options.")
        else:
            print("Verification: FAILED - File was not updated as expected.")

        # --- Scenario 3: Error Handling - File Not Found ---
        print_scenario_header("Error Handling: File Not Found")
        non_existent_file = temp_dir / "ghost.txt"
        print(f"Attempting to edit a non-existent file: '{non_existent_file}'")
        
        command_3 = [str(non_existent_file), "This should fail."]
        result_3 = run_cli_command(command_3)
        print_cli_result(result_3)

        if result_3.returncode != 0 and "Error: Failed to edit file" in result_3.stderr:
            print("\nVerification: SUCCESS - The tool correctly handled a non-existent file and exited with an error.")
        else:
            print("\nVerification: FAILED - The error was not handled as expected.")

        # --- Scenario 4: Error Handling - Missing API Key ---
        print_scenario_header("Error Handling: Missing ANTHROPIC_API_KEY")
        print("Temporarily unsetting ANTHROPIC_API_KEY for this subprocess call...")
        
        # Create a copy of the environment and remove the key
        env_without_key = os.environ.copy()
        if "ANTHROPIC_API_KEY" in env_without_key:
            del env_without_key["ANTHROPIC_API_KEY"]

        command_4 = [str(file_to_edit_1), "This will also fail."]
        result_4 = run_cli_command(command_4, custom_env=env_without_key)
        print_cli_result(result_4)

        if result_4.returncode != 0 and "ANTHROPIC_API_KEY environment variable is not set" in result_4.stderr:
            print("\nVerification: SUCCESS - The tool correctly detected the missing API key and exited.")
        else:
            print("\nVerification: FAILED - The missing API key error was not handled as expected.")

    except Exception as e:
        print(f"\nAn unexpected error occurred during the demonstration: {e}")
    finally:
        # Cleanup
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
            print(f"\nCleaned up temporary directory: {temp_dir.resolve()}")

    print("\n" + "=" * 70)
    print("--- DEMONSTRATION COMPLETE ---")
    print("=" * 70)


if __name__ == "__main__":
    demonstrate_cli_usage()
