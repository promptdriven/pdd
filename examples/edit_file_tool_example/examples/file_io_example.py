# To run this example:
# From project root: python examples/file_io_example.py
# Note: sys.path manipulation in this script ensures imports work from project root

import asyncio
import sys
import shutil
from pathlib import Path

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

# Import the necessary functions from the file_io module
from edit_file_tool.file_io import read_file_async, write_file_async


async def demonstrate_file_io():
    """
    A comprehensive demonstration of the file_io module's capabilities.

    This function showcases:
    1.  Successful asynchronous file writing and reading.
    2.  Automatic creation of parent directories during a write operation.
    3.  Graceful error handling for non-existent files.
    4.  Robust security validation to prevent directory traversal attacks.
    5.  Correct handling of attempts to read or write to a directory.
    """
    print("=====================================================")
    print("=      Demonstrating edit_file_tool/file_io.py      =")
    print("=====================================================")

    # Create a temporary directory for our file operations.
    # This ensures our example is self-contained and doesn't alter other files.
    temp_dir = Path("./examples/temp_file_io_demo")
    try:
        print(f"\nSetting up a temporary directory at: {temp_dir}")
        temp_dir.mkdir(parents=True, exist_ok=True)

        # --- Scenario 1: Successful Write and Read ---
        print("\n--- 1. Testing Successful Write and Read ---")
        file_path_1 = temp_dir / "test_file_1.txt"
        content_to_write = "Hello, this is a test of the asynchronous file writer."
        print(f"Attempting to write to: {file_path_1}")
        print(f"Content: '{content_to_write}'")

        success, error = await write_file_async(file_path_1, content_to_write)
        if success:
            print("SUCCESS: write_file_async completed without errors.")
        else:
            print(f"FAILURE: write_file_async returned an error: {error}")

        print(f"\nNow, attempting to read from: {file_path_1}")
        read_content, error = await read_file_async(file_path_1)
        if error:
            print(f"FAILURE: read_file_async returned an error: {error}")
        elif read_content == content_to_write:
            print("SUCCESS: Read content matches the written content.")
            print(f"Read Content: '{read_content}'")
        else:
            print("FAILURE: Read content does not match the written content.")

        # --- Scenario 2: Writing to a path with non-existent parent directories ---
        print("\n--- 2. Testing Write with Automatic Parent Directory Creation ---")
        file_path_2 = temp_dir / "new_parent_dir" / "test_file_2.txt"
        print(f"Attempting to write to a nested path: {file_path_2}")
        print("The 'new_parent_dir' directory does not exist yet.")

        success, error = await write_file_async(file_path_2, "This should work.")
        if success and file_path_2.exists():
            print("SUCCESS: File was created, and parent directory was made automatically.")
        else:
            print(f"FAILURE: Could not write to nested path. Error: {error}")

        # --- Scenario 3: Handling File Not Found on Read ---
        print("\n--- 3. Testing Error Handling for Non-Existent File ---")
        non_existent_file = temp_dir / "i_do_not_exist.txt"
        print(f"Attempting to read a file that does not exist: {non_existent_file}")

        content, error = await read_file_async(non_existent_file)
        if content is None and error:
            print("SUCCESS: Gracefully handled FileNotFoundError.")
            print(f"Received expected error message: {error}")
        else:
            print("FAILURE: Did not handle FileNotFoundError as expected.")

        # --- Scenario 4: Security - Preventing Directory Traversal ---
        print("\n--- 4. Testing Security Against Directory Traversal ---")
        # This path attempts to go outside the current working directory.
        malicious_path = Path("../../../etc/passwd")
        print(f"Attempting to read a sensitive file outside the CWD: {malicious_path}")

        content, error = await read_file_async(malicious_path)
        if content is None and error and "outside the allowed directory" in error:
            print("SUCCESS: Directory traversal attempt was blocked.")
            print(f"Received expected security error: {error}")
        else:
            print("FAILURE: Security validation did not block directory traversal.")

        print(f"\nAttempting to write to a sensitive file outside the CWD: {malicious_path}")
        success, error = await write_file_async(malicious_path, "hacked")
        if not success and error and "outside the allowed directory" in error:
            print("SUCCESS: Directory traversal attempt for writing was blocked.")
            print(f"Received expected security error: {error}")
        else:
            print("FAILURE: Security validation did not block write directory traversal.")

        # --- Scenario 5: Handling IsADirectoryError ---
        print("\n--- 5. Testing Error Handling for Reading a Directory ---")
        print(f"Attempting to read the temporary directory itself: {temp_dir}")
        content, error = await read_file_async(temp_dir)
        if content is None and error and "is a directory" in error:
            print("SUCCESS: Gracefully handled reading a directory.")
            print(f"Received expected error: {error}")
        else:
            print("FAILURE: Did not correctly handle reading a directory.")

        print(f"\nAttempting to write to the temporary directory itself: {temp_dir}")
        success, error = await write_file_async(temp_dir, "some content")
        if not success and error and "is a directory" in error:
            print("SUCCESS: Gracefully handled writing to a directory.")
            print(f"Received expected error: {error}")
        else:
            print("FAILURE: Did not correctly handle writing to a directory.")

    except Exception as e:
        print(f"\nAn unexpected error occurred during the demonstration: {e}")
    finally:
        # --- Cleanup ---
        # Always remove the temporary directory and its contents.
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
        asyncio.run(demonstrate_file_io())
    except Exception as e:
        print(f"A critical error occurred: {e}")
