# To run this example:
# From project root: python examples/core_example.py
# Note: sys.path manipulation in this script ensures imports work from project root

import asyncio
import logging
import os
import shutil
import sys
from pathlib import Path

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from edit_file_tool.core import edit_file
from edit_file_tool.utils import get_logger, format_cost

# Set up a logger to see the verbose output from the core module
log = get_logger(__name__)
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# --- Helper Functions ---

def print_scenario_header(title: str):
    """Prints a formatted header for each demonstration scenario."""
    print("\n" + "=" * 60)
    print(f"--- SCENARIO: {title} ---")
    print("=" * 60)

async def read_file_content(file_path: Path) -> str:
    """Safely reads the content of a file."""
    if not file_path.exists():
        return "File does not exist."
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return f.read()
    except Exception as e:
        return f"Error reading file: {e}"

# --- Main Demonstration ---

async def demonstrate_core_orchestrator():
    """
    Demonstrates the primary features of the edit_file_tool/core.py module.

    This function showcases the end-to-end file editing workflow orchestrated
    by the `edit_file` function, including:
    1. A simple, successful file edit.
    2. A more complex, multi-step edit requiring several interactions.
    3. Handling of a non-existent file path.
    4. Handling of reaching the maximum number of iterations.
    """
    print_scenario_header("Module Demonstration: edit_file_tool/core.py")

    if not os.environ.get("ANTHROPIC_API_KEY"):
        log.error("ANTHROPIC_API_KEY environment variable not set.")
        print("Please set your API key to run this example:")
        print("export ANTHROPIC_API_KEY='your-api-key-here'")
        return

    # Setup a temporary directory for the demonstration
    temp_dir = Path("./examples/temp_core_demo")
    original_cwd = Path.cwd()

    try:
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
        temp_dir.mkdir(parents=True)
        os.chdir(temp_dir)
        log.info(f"Created and changed to temporary directory: {Path.cwd()}")

        # --- Scenario 1: Simple Successful Edit ---
        print_scenario_header("Simple Successful Edit")
        file_to_edit_1 = Path("greeting.txt")
        initial_content_1 = "Hello, universe!"
        with open(file_to_edit_1, "w", encoding='utf-8') as f:
            f.write(initial_content_1)

        print(f"Initial content of '{file_to_edit_1}':\n---\n{initial_content_1}\n---")
        instructions_1 = "In the file greeting.txt, please change the word 'universe' to 'world'."
        print(f"Instruction: \"{instructions_1}\"")
        print("Calling edit_file with verbose=True...")

        success, final_message, total_cost = await edit_file(
            file_path=str(file_to_edit_1),
            edit_instructions=instructions_1,
            model="claude-3-5-sonnet-20240620",
            use_cache="auto",
            verbose=True,
            max_iterations=5
        )

        print("\n--- Result ---")
        print(f"Success: {success}")
        print(f"Final LLM Message: {final_message}")
        print(f"Total Cost: {format_cost(total_cost)}")

        final_content_1 = await read_file_content(file_to_edit_1)
        print(f"\nFinal content of '{file_to_edit_1}':\n---\n{final_content_1}\n---")
        if "Hello, world!" in final_content_1:
            print("Verification: SUCCESS - File content was updated correctly.")
        else:
            print("Verification: FAILED - File content was not updated as expected.")

        # --- Scenario 2: Multi-Step Edit ---
        print_scenario_header("Multi-Step Edit on a Python File")
        file_to_edit_2 = Path("calculator.py")
        initial_content_2 = "def add(a, b):\n    return a + b"
        with open(file_to_edit_2, "w", encoding='utf-8') as f:
            f.write(initial_content_2)

        print(f"Initial content of '{file_to_edit_2}':\n---\n{initial_content_2}\n---")
        instructions_2 = (
            "I have two requests for calculator.py. "
            "First, rename the function 'add' to 'sum_numbers'. "
            "Second, add a Python docstring to the function that explains it takes two numbers and returns their sum."
        )
        print(f"Instruction: \"{instructions_2}\"")
        print("Calling edit_file...")

        success, final_message, total_cost = await edit_file(
            file_path=str(file_to_edit_2),
            edit_instructions=instructions_2,
            model="claude-3-5-sonnet-20240620",
            use_cache="auto",
            verbose=False, # Set to False for a cleaner output for this scenario
            max_iterations=10
        )

        print("\n--- Result ---")
        print(f"Success: {success}")
        print(f"Final LLM Message: {final_message}")
        print(f"Total Cost: {format_cost(total_cost)}")

        final_content_2 = await read_file_content(file_to_edit_2)
        print(f"\nFinal content of '{file_to_edit_2}':\n---\n{final_content_2}\n---")
        if "def sum_numbers(a, b):" in final_content_2 and '"""' in final_content_2:
             print("Verification: SUCCESS - Both edits were applied correctly.")
        else:
            print("Verification: FAILED - The file was not updated with both changes.")

        # --- Scenario 3: Handling a Non-Existent File ---
        print_scenario_header("Error Handling: File Not Found")
        non_existent_file = "this_file_does_not_exist.md"
        print(f"Attempting to edit a non-existent file: '{non_existent_file}'")

        success, error_message, total_cost = await edit_file(
            file_path=non_existent_file,
            edit_instructions="This should not matter.",
            model="claude-3-5-sonnet-20240620",
            use_cache=False,
            verbose=False,
            max_iterations=5
        )

        print("\n--- Result ---")
        print(f"Success: {success}")
        print(f"Error Message: {error_message}")
        print(f"Total Cost: {format_cost(total_cost)} (should be $0.0000 as no API call was made)")
        if not success and "Could not read file" in error_message:
            print("Verification: SUCCESS - The function correctly handled the file not found error.")
        else:
            print("Verification: FAILED - The error was not handled as expected.")

        # --- Scenario 4: Handling Max Iterations Reached ---
        print_scenario_header("Error Handling: Max Iterations Reached")
        file_to_edit_3 = Path("ambiguous.txt")
        with open(file_to_edit_3, "w", encoding='utf-8') as f:
            f.write("A file with some text.")

        print(f"Using an ambiguous instruction to trigger a loop: 'Make this file better.'")
        print("Setting max_iterations to a low value (3) to force the error.")

        success, error_message, total_cost = await edit_file(
            file_path=str(file_to_edit_3),
            edit_instructions="Make this file better.",
            model="claude-3-5-sonnet-20240620",
            use_cache=False,
            verbose=False,
            max_iterations=3
        )

        print("\n--- Result ---")
        print(f"Success: {success}")
        print(f"Error Message: {error_message}")
        print(f"Total Cost: {format_cost(total_cost)} (cost was incurred during attempts)")
        if not success and "Max iterations" in error_message:
            print("Verification: SUCCESS - The function correctly terminated after reaching max iterations.")
        else:
            print("Verification: FAILED - The max iterations limit was not handled as expected.")

    except Exception as e:
        log.critical(f"An unexpected error occurred during the demonstration: {e}", exc_info=True)
    finally:
        # Cleanup
        os.chdir(original_cwd)
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
            log.info(f"Cleaned up temporary directory: {temp_dir}")

    print("\n" + "=" * 60)
    print("--- DEMONSTRATION COMPLETE ---")
    print("=" * 60)


if __name__ == "__main__":
    try:
        asyncio.run(demonstrate_core_orchestrator())
    except Exception as e:
        print(f"\nA critical error occurred at the top level: {e}")
