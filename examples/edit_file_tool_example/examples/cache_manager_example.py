# To run this example:
# From project root: python examples/cache_manager_example.py
# Note: sys.path manipulation in this script ensures imports work from project root

import sys
from pathlib import Path
from typing import Union

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from edit_file_tool.cache_manager import CacheManager

def demonstrate_cache_manager():
    """
    Demonstrates the usage of the CacheManager class.

    This function runs through several scenarios to show how CacheManager
    makes decisions based on user flags and file characteristics.
    """
    print("--- Initializing CacheManager Demonstration ---")
    manager = CacheManager()

    # --- Scenario 1: Explicit User Overrides ---
    print("\n=== SCENARIO 1: Explicit User Overrides ===")
    print("The manager should respect 'always'/'never' flags regardless of content.")

    dummy_content = "This content does not matter for this test."
    run_test_case(
        manager,
        "Explicitly enable with 'always'",
        dummy_content,
        "always",
        expected=True
    )
    run_test_case(
        manager,
        "Explicitly enable with boolean True",
        dummy_content,
        True,
        expected=True
    )
    run_test_case(
        manager,
        "Explicitly disable with 'never'",
        dummy_content,
        "never",
        expected=False
    )
    run_test_case(
        manager,
        "Explicitly disable with boolean False",
        dummy_content,
        False,
        expected=False
    )

    # --- Scenario 2: 'auto' mode based on file size ---
    print("\n=== SCENARIO 2: 'auto' mode based on file size ===")
    print("The manager uses file size for quick decisions on very small or large files.")

    # Small file (< 1KB)
    small_content = "a" * 500  # 500 bytes
    run_test_case(
        manager,
        "Auto-detect a small file (< 1KB)",
        small_content,
        "auto",
        expected=False
    )

    # Large file (> 4KB)
    large_content = "a" * 5000  # 5000 bytes
    run_test_case(
        manager,
        "Auto-detect a large file (> 4KB)",
        large_content,
        "auto",
        expected=True
    )

    # --- Scenario 3: 'auto' mode for medium files (complexity analysis) ---
    print("\n=== SCENARIO 3: 'auto' mode for medium files (complexity analysis) ===")
    print("For files between 1KB and 4KB, the manager analyzes content complexity.")

    # Medium, Complex File (should be cached)
    # This content is designed to pass all complexity checks.
    complex_line = "import os; def my_func(x): return os.path.join('path', x)\n"
    # 60 lines * ~65 chars/line = ~3900 bytes (in medium range)
    medium_complex_content = complex_line * 60
    run_test_case(
        manager,
        "Auto-detect a medium, COMPLEX file",
        medium_complex_content,
        "auto",
        expected=True
    )

    # Medium, Simple File (low line count)
    # ~2KB, but only one line. Fails the line count check.
    medium_simple_low_lines = "a" * 2000
    run_test_case(
        manager,
        "Auto-detect a medium, SIMPLE file (low line count)",
        medium_simple_low_lines,
        "auto",
        expected=False
    )

    # Medium, Simple File (low density)
    # Many lines, but mostly whitespace. Fails the density check.
    low_density_line = "a" + (" " * 50) + "\n"  # Density is ~1/52
    # 60 lines * 52 chars/line = ~3120 bytes (in medium range)
    medium_simple_low_density = low_density_line * 60
    run_test_case(
        manager,
        "Auto-detect a medium, SIMPLE file (low content density)",
        medium_simple_low_density,
        "auto",
        expected=False
    )

    # --- Scenario 4: Edge Cases ---
    print("\n=== SCENARIO 4: Edge Cases ===")
    print("The manager should handle edge cases like empty files gracefully.")

    run_test_case(
        manager,
        "Handle an empty file",
        "",
        "auto",
        expected=False
    )

    print("\n--- CacheManager Demonstration Complete ---")


def run_test_case(
    manager: CacheManager,
    description: str,
    content: str,
    flag: Union[str, bool],
    expected: bool
):
    """
    A helper function to run a single test case and print the results.

    Args:
        manager: An instance of the CacheManager.
        description: A string describing the test case.
        content: The file content string to be analyzed.
        flag: The cache flag to be passed to the manager.
        expected: The expected boolean result.
    """
    print(f"\n- Test Case: {description}")
    try:
        content_size = len(content.encode('utf-8'))
        print(f"  - Input Content Size: {content_size} bytes")
        print(f"  - Input Cache Flag: '{flag}'")
        print(f"  - Expected Decision: {expected}")

        # Call the method being demonstrated
        actual = manager.should_use_cache(content, flag)

        print(f"  - Actual Decision:   {actual}")

        if actual == expected:
            print("  - Result: PASS")
        else:
            print(f"  - Result: FAIL (Expected {expected}, but got {actual})")

    except Exception as e:
        print(f"  - Result: ERROR - An unexpected exception occurred: {e}")
    print("-" * 20)


if __name__ == "__main__":
    demonstrate_cache_manager()