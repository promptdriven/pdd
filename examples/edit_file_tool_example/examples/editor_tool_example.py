# To run this example:
# From project root: python examples/editor_tool_example.py
# Note: sys.path manipulation in this script ensures imports work from project root

import asyncio
import os
import shutil
import sys
from pathlib import Path

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

# Import the necessary class from the editor_tool module
from edit_file_tool.editor_tool import EditTool20250124, EditResult


def print_result(description: str, result: EditResult):
    """
    Helper function to neatly print the outcome of a tool operation.

    Args:
        description (str): A string describing the operation that was performed.
        result (EditResult): The result object returned by the tool.
    """
    print(f"\n--- {description} ---")
    if result.success:
        print("Status: SUCCESS")
        print("Output:")
        print(result.output)
    else:
        print("Status: FAILED")
        print(f"Error: {result.error}")
    print("-" * (len(description) + 8))


async def demonstrate_editor_tool():
    """
    A comprehensive demonstration of the EditTool20250124 class.

    This function showcases:
    1.  Creating a new file.
    2.  Viewing file and directory contents.
    3.  Inserting text at various positions in a file.
    4.  Replacing a unique string within a file.
    5.  Undoing the last modification to a file.
    6.  Graceful handling of common errors (e.g., file exists, not found).
    7.  Robust security validation to prevent directory traversal.
    """
    print("=====================================================")
    print("=    Demonstrating edit_file_tool/editor_tool.py    =")
    print("=====================================================")

    # Create a temporary directory for our file operations.
    temp_dir = Path("./examples/temp_editor_tool_demo")
    tool = EditTool20250124()

    try:
        print(f"\nSetting up a temporary directory at: {temp_dir}")
        temp_dir.mkdir(parents=True, exist_ok=True)
        os.chdir(temp_dir)
        print(f"Changed current working directory to: {Path.cwd()}")

        # --- 1. Create a new file ---
        file_path = "my_project/main.py"
        initial_content = 'def main():\n    print("Initial version")'
        result = await tool(
            command="create",
            path=file_path,
            file_text=initial_content
        )
        print_result(f"1. Creating new file '{file_path}'", result)

        # --- 2. View the created file ---
        result = await tool(command="view", path=file_path)
        print_result(f"2. Viewing file '{file_path}'", result)

        # --- 3. Insert text into the file ---
        # Insert after line 2
        result = await tool(
            command="insert",
            path=file_path,
            insert_line=2,
            new_str='    # This is an inserted line.'
        )
        print_result(f"3a. Inserting text into '{file_path}' after line 2", result)

        # View the result
        result = await tool(command="view", path=file_path)
        print_result(f"3b. Viewing '{file_path}' after insertion", result)

        # Insert at the top of the file
        result = await tool(
            command="insert",
            path=file_path,
            insert_line=0,
            new_str='import os'
        )
        print_result(f"3c. Inserting text at the top of '{file_path}'", result)

        # View the result again
        result = await tool(command="view", path=file_path)
        print_result(f"3d. Viewing '{file_path}' after second insertion", result)

        # --- 4. Replace a unique string ---
        result = await tool(
            command="str_replace",
            path=file_path,
            old_str='"Initial version"',
            new_str='"Final version"'
        )
        print_result(f"4a. Replacing a string in '{file_path}'", result)

        # View the result
        result = await tool(command="view", path=file_path)
        print_result(f"4b. Viewing '{file_path}' after replacement", result)

        # --- 5. Undo the last edit ---
        result = await tool(command="undo_edit", path=file_path)
        print_result(f"5a. Undoing the last edit on '{file_path}'", result)

        # View the reverted file
        result = await tool(command="view", path=file_path)
        print_result(f"5b. Viewing '{file_path}' after undo", result)

        # --- 6. View a directory ---
        # Create another file to have more content in the directory
        await tool(command="create", path="my_project/utils.py", file_text="# Utilities")
        result = await tool(command="view", path="my_project")
        print_result("6. Viewing contents of directory 'my_project'", result)

        # --- 7. Demonstrate Error Handling ---
        print("\n\n=====================================================")
        print("=           Demonstrating Error Handling          =")
        print("=====================================================")

        # a) Trying to create a file that already exists
        result = await tool(
            command="create",
            path=file_path,
            file_text="This will fail"
        )
        print_result("7a. Error: Creating a file that already exists", result)

        # b) Trying to view a file that does not exist
        result = await tool(command="view", path="non_existent_file.txt")
        print_result("7b. Error: Viewing a non-existent file", result)

        # c) Trying to insert at an invalid line number
        result = await tool(
            command="insert",
            path=file_path,
            insert_line=999,
            new_str="# This will fail"
        )
        print_result("7c. Error: Inserting at an out-of-bounds line", result)

        # d) Trying to replace a string that is not found
        result = await tool(
            command="str_replace",
            path=file_path,
            old_str="non_existent_string",
            new_str="wont_matter"
        )
        print_result("7d. Error: Replacing a non-existent string", result)

        # e) Trying to replace a string that appears multiple times
        multi_file = "multi.txt"
        await tool(command="create", path=multi_file, file_text="test\ntest")
        result = await tool(
            command="str_replace",
            path=multi_file,
            old_str="test",
            new_str="replace"
        )
        print_result("7e. Error: Replacing a string with multiple occurrences", result)

        # f) Trying to undo an edit when no backup is available
        result = await tool(command="undo_edit", path=file_path)
        print_result("7f. Error: Undoing an edit twice", result)

        # --- 8. Demonstrate Security Validations ---
        print("\n\n=====================================================")
        print("=         Demonstrating Security Validations      =")
        print("=====================================================")

        # a) Attempting directory traversal
        malicious_path_1 = "../test.txt"
        result = await tool(command="view", path=malicious_path_1)
        print_result(f"8a. Security: Blocking directory traversal '{malicious_path_1}'", result)

        # b) Attempting to access an absolute path
        # Use a path that is common on both POSIX and Windows for the example
        absolute_path = Path(project_root).resolve().parent / "some_other_file"
        result = await tool(command="view", path=str(absolute_path))
        print_result(f"8b. Security: Blocking absolute path '{absolute_path}'", result)

        # c) On POSIX, attempting to use a Windows-style absolute path
        if os.name == 'posix':
            win_path = "C:\\Users\\test.txt"
            result = await tool(command="view", path=win_path)
            print_result(f"8c. Security: Blocking Windows-style path on POSIX '{win_path}'", result)

    except Exception as e:
        print(f"\nAn unexpected error occurred during the demonstration: {e}")
    finally:
        # --- Cleanup ---
        # Change back to the original directory before cleaning up
        os.chdir(project_root)
        if temp_dir.exists():
            print(f"\nCleaning up temporary directory: {temp_dir}")
            shutil.rmtree(temp_dir)
            print("Cleanup complete.")

    print("\n=====================================================")
    print("=              Demonstration Complete             =")
    print("=====================================================")


if __name__ == "__main__":
    # Run the asynchronous demonstration function.
    try:
        asyncio.run(demonstrate_editor_tool())
    except Exception as e:
        print(f"A critical error occurred: {e}")
