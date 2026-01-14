# To run this example:
# From project root: python examples/cache_manager_utility_example.py
# Note: sys.path manipulation in this script ensures imports work from project root
import sys
from pathlib import Path
import logging
import shutil
import tempfile

project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from edit_file_tool.cache_manager_utility import should_use_cache

def demonstrate_cache_decision() -> None:
    """Demonstrate cache decisions for small, medium, large, and missing files."""
    logging.basicConfig(
        level=logging.DEBUG,
        format="[CACHE-EXAMPLE] %(levelname)s: %(message)s",
    )

    workspace_dir = Path(tempfile.mkdtemp(prefix="cache_example_"))
    try:
        small_file = workspace_dir / "small.txt"
        medium_file = workspace_dir / "medium.txt"
        large_file = workspace_dir / "large.txt"
        # Create a very small file (less than 1 KB)
        with open(small_file, "w", encoding="utf-8") as output:
            output.write("Simple text\n" * 2)

        # Create a medium file (around 2.5 KB) with some code-like lines
        with open(medium_file, "w", encoding="utf-8") as output:
            for idx in range(80):
                output.write(f"def func_{idx}(): pass\n")
            output.write("# end of medium file\n")
            output.write("""for item in items:\n    print(item)\n""")

        # Create a large file (over 5 KB) by repeating a longer line pattern
        with open(large_file, "w", encoding="utf-8") as output:
            for idx in range(200):
                output.write(f"line_{idx}: value = {idx} * 42\n")

        # Evaluate cache usage decisions for each file
        small_size = small_file.stat().st_size
        print("[STEP] Small file decision:")
        result_small = should_use_cache(str(small_file), small_size, use_cache="auto")
        print(f"  Small file size {small_size} bytes => cache={result_small}")

        medium_size = medium_file.stat().st_size
        print("[STEP] Medium file decision (auto mode):")
        result_medium = should_use_cache(str(medium_file), medium_size)
        print(f"  Medium file size {medium_size} bytes => cache={result_medium}")

        large_size = large_file.stat().st_size
        print("[STEP] Large file forced cache (always override):")
        result_large = should_use_cache(str(large_file), large_size, use_cache=True)
        print(f"  Large file size {large_size} bytes => cache={result_large}")

        missing_file = workspace_dir / "missing.txt"
        missing_size = 3072
        print("[STEP] Missing file demonstration (auto mode):")
        result_missing = should_use_cache(str(missing_file), missing_size)
        print("  Missing file path is not present; module logs warning and returns:", result_missing)

        print("[STEP] Invalid use_cache value handling:")
        try:
            should_use_cache(str(small_file), small_size, use_cache="invalid-mode")
        except ValueError as exc:
            print("  Caught ValueError for invalid use_cache:", exc)

    finally:
        shutil.rmtree(workspace_dir, ignore_errors=True)
        print("[CLEANUP] Removed temporary workspace at", workspace_dir)


if __name__ == "__main__":
    demonstrate_cache_decision()