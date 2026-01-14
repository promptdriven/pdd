import asyncio
import os
import sys

# Ensure the 'src' directory is in the python path so we can import the package
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, "..", ".."))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# Import the public API from the package
# Note: In a real environment, this would be 'from edit_file_tool import ...'
from edit_file_tool import edit_file, EditTool20250124, __version__


async def run_example() -> None:
    """
    Demonstrates the high-precision file editing capabilities of the edit_file_tool library.
    """
    print(f"Using edit-file-tool version: {__version__}")

    # 1. Basic Async Usage with edit_file
    test_file = "demo_file.txt"
    with open(test_file, "w") as f:
        f.write("Hello World\nThis is a test file.")

    print(f"\nEditing {test_file} using edit_file()...")
    try:
        # We ensure the call matches the expected signature: file_path, old_str, new_str
        await edit_file(
            file_path=test_file,
            old_str="World",
            new_str="Software Engineer"
        )

        if os.path.exists(test_file):
            with open(test_file, "r") as f:
                content = f.read()
                print("Updated Content:")
                print(content)
    except TypeError as e:
        print(f"Signature Error: {e}")
    except Exception as e:
        print(f"Error during edit_file: {e}")

    # 2. Using the EditTool20250124 Class
    if EditTool20250124 is not None:
        print("\nInitializing EditTool20250124...")
        try:
            tool = EditTool20250124()
            print(f"Tool initialized: {tool}")
        except Exception as e:
            print(f"Error initializing tool: {e}")
    else:
        print("\nEditTool20250124 is not available (missing optional dependencies).")

    # Cleanup
    if os.path.exists(test_file):
        os.remove(test_file)


if __name__ == "__main__":
    asyncio.run(run_example())