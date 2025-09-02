import os
import sys
import json

# --- Configuration ---

# Assume the script is run from the 'pdd' directory and the 'edit_file.py' module
# is in the parent directory. Adjust if the structure is different.
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
# Construct the absolute path to the directory containing edit_file.py
# Assuming edit_file.py is in the parent directory of the 'pdd' directory
MODULE_DIR = os.path.abspath(os.path.join(SCRIPT_DIR, '..'))

# Add the module directory to the Python path
if MODULE_DIR not in sys.path:
    sys.path.insert(0, MODULE_DIR)

# Now import the function from the module
# The module file name is assumed to be 'edit_file.py'
try:
    from pdd.edit_file import run_edit_in_subprocess
except ImportError as e:
    print(f"Error: Could not import 'run_edit_in_subprocess' function from {MODULE_DIR}/edit_file.py")
    print(f"Make sure the module exists and the path is correct.")
    print(f"Original error: {e}")
    sys.exit(1)

# Get the path to the 'pdd' directory from the environment variable
# This is where output files (dummy file, config) will be created.
PDD_PATH = os.environ.get("PDD_PATH")
if not PDD_PATH:
    print("Error: PDD_PATH environment variable is not set.")
    print("Please set PDD_PATH to the absolute path of the 'pdd' directory.")
    sys.exit(1)
elif not os.path.isdir(PDD_PATH):
    print(f"Error: PDD_PATH ('{PDD_PATH}') is not a valid directory.")
    sys.exit(1)

# Define the names for test files
EXAMPLE_FILE_NAME = "example_file_to_edit.txt"
# PREPROCESS_FILE_NAME = "/Users/gregtanaka/pdd/staging/regression/foo.py" # Removed
# Note: The edit_file module now finds the config within the package by default.
# This path is kept here for context but might not be directly used by edit_file.
MCP_CONFIG_FILE_PATH = os.path.join(PDD_PATH, "pdd", "mcp_config.json") # Updated path

# --- Helper Function to Create Files ---

def create_example_files():
    """Creates the necessary dummy input file and MCP config file."""
    # 1. Define the output directory path
    output_dir = os.path.join(PDD_PATH, "output")
    # Create the output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)
    
    # 2. Create the dummy text file to be edited within the output directory
    example_file_path = os.path.join(output_dir, EXAMPLE_FILE_NAME)
    print(f"Creating dummy file: {example_file_path}")
    initial_content = """Line 1: This is the original text.
Line 2: Keep this line.
Line 3: This line will be modified.
Line 4: Another line.
"""
    with open(example_file_path, "w") as f:
        f.write(initial_content)
    print("Initial file content:")
    print("-" * 20)
    print(initial_content.strip())
    print("-" * 20)

# Define the instructions for each test case
EXAMPLE_INSTRUCTIONS = """1. Change the word 'original' to 'UPDATED' on Line 1.
2. Replace Line 3 entirely with 'Line 3: This line has been REPLACED.'
3. Add a new line at the end: 'Line 5: Added by the agent.'"""

# PREPROCESS_INSTRUCTIONS = """ ... """ # Removed

def run_edit_file_test(file_name, instructions, verify_example=False):
    """
    Runs the edit_file test on a specific file with given instructions.
    
    Args:
        file_name: Name of the file to edit
        instructions: Instructions for editing
        verify_example: Whether to verify specific checks for the example file
    """
    file_path = os.path.join(PDD_PATH, file_name)
    
    print(f"\n{'=' * 50}")
    print(f"RUNNING TEST FOR: {file_name}")
    print(f"{'=' * 50}")
    
    print(f"\n--- Calling edit_file ---")
    print(f"File to edit: {file_path}")
    print(f"Instructions summary: {instructions.split('\\n')[0]}...")

    # Call the run_edit_in_subprocess function (no need for await since it's synchronous)
    success, error_message = run_edit_in_subprocess(
        file_path=file_path,
        edit_instructions=instructions
    )

    print("\n--- edit_file Result ---")
    print(f"Success: {success}")
    if error_message:
        print(f"Error Message: {error_message}")
    else:
        print("Error Message: None")

    print("\n--- Final File Content ---")
    # Check the content of the file after the operation
    if os.path.exists(file_path):
        with open(file_path, "r") as f:
            final_content = f.read()
        print("-" * 20)
        print(final_content.strip())
        print("-" * 20)

        # For the example file, run specific verification checks
        if verify_example:
            verification_results = {
                "edit_success": success,
                "file_exists": True,
                "checks": {
                    "updated_line1": "UPDATED" in final_content,
                    "replaced_line3": "Line 3: This line has been REPLACED." in final_content,
                    "added_line5": "Line 5: Added by the agent." in final_content,
                    "removed_original": "original" not in final_content,
                    "removed_will_be_modified": "will be modified" not in final_content
                }
            }

            print("\n--- Verification Results ---")
            print(f"Edit operation reported: {'Success' if success else 'Failure'}")
            if error_message:
                print(f"Edit operation error: {error_message}")
            
            print("\nDetailed Verification:")
            all_checks_passed = True
            for check_name, result in verification_results["checks"].items():
                print(f"- {check_name}: {'✓' if result else '✗'}")
                if not result:
                    all_checks_passed = False
            
            if all_checks_passed and success:
                print("\nVerification Status: All changes were applied successfully ✓")
            elif all_checks_passed and not success:
                print("\nVerification Status: ⚠️ Warning - Content looks correct but edit reported failure")
                print("This might indicate an internal process issue that didn't affect the final result")
            elif not all_checks_passed and success:
                print("\nVerification Status: ⚠️ Warning - Edit reported success but some changes are missing")
            else:
                print("\nVerification Status: ✗ Edit failed and changes are incomplete")
    else:
        print(f"File not found after edit attempt: {file_path}")

# --- Main Example Function ---

def run_example():
    """
    Demonstrates how to use the edit_file async function on two different test cases.

    Prerequisites:
    1.  `PDD_PATH` environment variable must be set to the 'pdd' directory path.
    2.  The `edit_file.py` module must be importable (e.g., in the parent directory).
    3.  Required packages installed (`langchain`, `langgraph`, `langchain-mcp-adapters`,
        `langchain-openai` or `langchain-anthropic`, `openai` or `anthropic`).
    4.  LLM API keys (e.g., `OPENAI_API_KEY` or `ANTHROPIC_API_KEY`) must be set as
        environment variables for the LLM used within `edit_file.py`.
    5.  The MCP text editor service must be runnable via the command specified in
        `mcp_config.json` (e.g., `uvx mcp-text-editor`). `uvx` and the package
        need to be installed/available.
    """
    print("--- Starting edit_file Examples ---")

    # Create the necessary files in the PDD_PATH directory
    create_example_files()
    
    # Run test 1: Example file (now located in the output directory)
    example_file_rel_path = os.path.join("output", EXAMPLE_FILE_NAME)
    run_edit_file_test(example_file_rel_path, EXAMPLE_INSTRUCTIONS, verify_example=True)
    
    # Run test 2: Preprocess.py file # Removed
    # run_edit_file_test(PREPROCESS_FILE_NAME, PREPROCESS_INSTRUCTIONS) # Removed

    print("\n--- All Examples Finished ---")

# --- Run the Example ---

if __name__ == "__main__":
    # Ensure PDD_PATH is set before running
    if not PDD_PATH:
        print("Error: PDD_PATH environment variable must be set before running the example.")
        sys.exit(1)

    # Run the main function (no need for asyncio.run anymore)
    run_example()