
"""
Example usage of the agentic_split module.

This script demonstrates how to invoke the `run_agentic_split` function.
Since the module relies on file system checks and an orchestrator, this example
mocks those dependencies to simulate a successful split workflow without
requiring actual files or LLM calls.

Scenario:
    We simulate splitting a large Python file 'large_module.py' into smaller units.
    The function validates the file, detects language, checks for prompt and test files,
    then calls the orchestrator.
"""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure the project root is in sys.path so we can import the module
# Assuming this script is in a subdirectory (e.g., context/) relative to the project root
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

try:
    from pdd.agentic_split import run_agentic_split
except ImportError:
    print("Error: Could not import 'pdd.agentic_split'.")
    print("Ensure your PYTHONPATH is set correctly or the file structure matches.")
    sys.exit(1)


def mock_get_language(extension: str) -> str:
    """Mock get_language to return 'python' for .py files."""
    if extension == '.py':
        return 'python'
    return None


def mock_run_agentic_split_orchestrator(**kwargs) -> tuple:
    """Mock the orchestrator to simulate a successful split."""
    return (True, "Split successful: Created utils.py and main.py", 1.50, "claude-3-opus", ["prompts/utils_python.prompt", "utils.py", "main.py"])


def main():
    """Main function to run the agentic split simulation."""
    # Define simulation parameters
    target_file = "large_module.py"
    params = {
        "verbose": True,
        "quiet": False,
        "diagnose_only": False,
        "propose_only": False,
        "delete_dead": True,
        "force_split": False
    }

    print("Starting Agentic Split Simulation...")
    print("-" * 50)

    # Patch dependencies and file system checks
    with patch("pdd.agentic_split.get_language", side_effect=mock_get_language), \
         patch("pdd.agentic_split.run_agentic_split_orchestrator", side_effect=mock_run_agentic_split_orchestrator), \
         patch("pathlib.Path.exists", return_value=True), \
         patch("pathlib.Path.is_file", return_value=True):

        # Run the function
        success, message, total_cost, model_used, changed_files = run_agentic_split(
            target_file=target_file,
            **params
        )

    print("-" * 50)
    print("Simulation Complete.")
    print(f"Success: {success}")
    print(f"Message: {message}")
    print(f"Total Cost: ${total_cost:.2f}")
    print(f"Model Used: {model_used}")
    print(f"Changed Files: {changed_files}")
    print("\nNext steps: Review changed files and run tests.")


if __name__ == "__main__":
    main()