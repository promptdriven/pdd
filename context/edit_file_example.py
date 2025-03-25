import asyncio
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
    from pdd.edit_file import edit_file
except ImportError as e:
    print(f"Error: Could not import 'edit_file' function from {MODULE_DIR}/edit_file.py")
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

# Define the name for the dummy file and config file within the PDD_PATH directory
TEST_FILE_NAME = "example_file_to_edit.txt"
TEST_FILE_PATH = os.path.join(PDD_PATH, TEST_FILE_NAME)
MCP_CONFIG_FILE_PATH = os.path.join(PDD_PATH, "mcp_config.json") # Config file used by the module

# --- Helper Function to Create Files ---

def create_example_files():
    """Creates the necessary dummy input file and MCP config file."""
    # 1. Create the dummy text file to be edited
    print(f"Creating dummy file: {TEST_FILE_PATH}")
    initial_content = """Line 1: This is the original text.
Line 2: Keep this line.
Line 3: This line will be modified.
Line 4: Another line.
"""
    with open(TEST_FILE_PATH, "w") as f:
        f.write(initial_content)
    print("Initial file content:")
    print("-" * 20)
    print(initial_content.strip())
    print("-" * 20)

    # 2. Create the mcp_config.json file required by the edit_file module
    #    This configuration tells the module how to launch the MCP text editor service.
    #    Ensure 'uvx mcp-text-editor' is runnable in your environment.
    print(f"Creating MCP config file: {MCP_CONFIG_FILE_PATH}")
    mcp_config = {
        "text_editor_server": {
            # Command to launch the MCP server (using uvx runner)
            "command": "uvx",
            # Arguments for the command (specifying the text editor package)
            "args": ["mcp-text-editor"],
            # Transport mechanism (stdio is common for local processes)
            "transport": "stdio"
        }
    }
    with open(MCP_CONFIG_FILE_PATH, 'w') as f:
        json.dump(mcp_config, f, indent=2)
    print(f"{MCP_CONFIG_FILE_PATH} created.")

# --- Main Example Function ---

async def run_example():
    """
    Demonstrates how to use the edit_file async function.

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
    print("--- Starting edit_file Example ---")

    # Create the necessary files in the PDD_PATH directory
    create_example_files()

    # Define the instructions for editing the file
    # Note: The effectiveness depends heavily on the LLM's ability to understand
    # the instructions and use the MCP tool correctly.
    instructions = """1. Change the word 'original' to 'UPDATED' on Line 1.
2. Replace Line 3 entirely with 'Line 3: This line has been REPLACED.'
3. Add a new line at the end: 'Line 5: Added by the agent.'"""

    print("\n--- Calling edit_file ---")
    print(f"File to edit: {TEST_FILE_PATH}")
    print(f"Instructions: {instructions}")

    # Call the async function from the imported module
    # It requires the absolute path to the file and the edit instructions.
    # It returns a tuple: (success_boolean, error_message_or_None)
    # Note: This example does not use try/except as requested. Errors during
    # the edit_file execution (like connection issues, LLM errors, tool errors)
    # will be caught within the function and returned in the result tuple.
    success, error_message = await edit_file(
        file_path=TEST_FILE_PATH,
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
    if os.path.exists(TEST_FILE_PATH):
        with open(TEST_FILE_PATH, "r") as f:
            final_content = f.read()
        print("-" * 20)
        print(final_content.strip())
        print("-" * 20)

        # More detailed verification with specific checks
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
        print(f"File not found after edit attempt: {TEST_FILE_PATH}")
        verification_results = {
            "edit_success": success,
            "file_exists": False,
            "checks": {}
        }

    # Clean up the created files (optional)
    print(f"\nCleaning up {TEST_FILE_PATH} and {MCP_CONFIG_FILE_PATH}")
    if os.path.exists(TEST_FILE_PATH):
        os.remove(TEST_FILE_PATH)
    if os.path.exists(MCP_CONFIG_FILE_PATH):
        os.remove(MCP_CONFIG_FILE_PATH)
    print(f"\n(Keeping {TEST_FILE_PATH} and {MCP_CONFIG_FILE_PATH} for inspection)")

    print("\n--- Example Finished ---")

# --- Run the Example ---

if __name__ == "__main__":
    # Ensure PDD_PATH is set before running
    if not PDD_PATH:
        print("Error: PDD_PATH environment variable must be set before running the example.")
        sys.exit(1)

    # Run the async main function
    asyncio.run(run_example())