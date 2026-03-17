"""
Example: summarize_directory

Demonstrates all features of the summarize_directory module:
  1. Basic summarization of files in a directory
  2. Input validation (directory_path, strength, temperature, verbose, csv_file)
  3. Cache reuse via csv_file with content_hash matching
  4. Progress callback for TUI integration
  5. Binary file filtering
  6. Error handling (LLM failures recorded, not crashed)
  7. The 'time' parameter controlling LLM thinking effort
  8. Relative paths in CSV output
"""

import os
import sys
import tempfile
import shutil
from unittest.mock import patch

# Ensure the parent directory is in the path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.summarize_directory import summarize_directory, FileSummary


def mock_llm_invoke(*args, **kwargs):
    """Mock for llm_invoke to make the example run standalone."""
    return {
        'result': FileSummary(
            file_summary="This is a mock summary of the file.",
            key_exports=["add", "subtract"],
            dependencies=["os", "sys"]
        ),
        'cost': 0.0015,
        'model_name': "mock-gpt-4o"
    }


def main():
    print("=" * 60)
    print("Example: summarize_directory")
    print("=" * 60)

    # Create a temporary directory with sample files
    test_dir = tempfile.mkdtemp(prefix="pdd_example_")
    try:
        # Create sample source files
        math_path = os.path.join(test_dir, "math_utils.py")
        with open(math_path, "w") as f:
            f.write("def add(a: int, b: int) -> int:\n    return a + b\n")

        helper_path = os.path.join(test_dir, "helpers.py")
        with open(helper_path, "w") as f:
            f.write("import os\ndef get_cwd():\n    return os.getcwd()\n")

        # Create a binary file (should be filtered out automatically)
        binary_path = os.path.join(test_dir, "logo.png")
        with open(binary_path, "wb") as f:
            f.write(b'\x89PNG\r\n\x1a\n')

        print(f"Created sample directory at {test_dir}")
        print(f"  - math_utils.py (source file)")
        print(f"  - helpers.py    (source file)")
        print(f"  - logo.png      (binary, should be filtered)")

        # ------------------------------------------------------------------
        # 1. Basic summarization with verbose output
        # ------------------------------------------------------------------
        print("\n--- 1. Basic summarization (verbose=True) ---")
        with patch('pdd.summarize_directory.llm_invoke', side_effect=mock_llm_invoke):
            csv_output, total_cost, model_name = summarize_directory(
                directory_path=test_dir,
                strength=0.5,
                temperature=0.0,
                time=0.3,       # Controls LLM thinking effort
                verbose=True,
            )

        print(f"Model used: {model_name}")
        print(f"Total cost: ${total_cost:.6f}")
        print(f"CSV Output:\n{csv_output}")

        # ------------------------------------------------------------------
        # 2. Cache reuse via csv_file
        #    (hash match + non-empty key_exports + non-empty dependencies = cache hit)
        # ------------------------------------------------------------------
        print("--- 2. Cache reuse (re-run with csv_file) ---")
        with patch('pdd.summarize_directory.llm_invoke', side_effect=mock_llm_invoke):
            csv_output2, total_cost2, model_name2 = summarize_directory(
                directory_path=test_dir,
                strength=0.5,
                temperature=0.0,
                time=0.3,
                verbose=True,
                csv_file=csv_output,  # Pass previous output as cache
            )

        print(f"Total cost on re-run: ${total_cost2:.6f}  (should be $0 if cached)")
        print(f"CSV Output (cached):\n{csv_output2}")

        # ------------------------------------------------------------------
        # 3. Progress callback (for TUI integration)
        # ------------------------------------------------------------------
        print("--- 3. Progress callback ---")
        progress_log = []

        def my_progress_callback(current: int, total: int) -> None:
            progress_log.append((current, total))
            print(f"  Progress: {current}/{total}")

        with patch('pdd.summarize_directory.llm_invoke', side_effect=mock_llm_invoke):
            summarize_directory(
                directory_path=test_dir,
                strength=0.5,
                temperature=0.0,
                progress_callback=my_progress_callback,
            )

        print(f"  Callback was called {len(progress_log)} times: {progress_log}")

        # ------------------------------------------------------------------
        # 4. Input validation
        # ------------------------------------------------------------------
        print("\n--- 4. Input validation ---")
        try:
            summarize_directory(directory_path="", strength=0.5, temperature=0.0)
        except ValueError as e:
            print(f"  Caught expected error: {e}")

        try:
            summarize_directory(directory_path="/tmp", strength=1.5, temperature=0.0)
        except ValueError as e:
            print(f"  Caught expected error: {e}")

        try:
            summarize_directory(directory_path="/tmp", strength=0.5, temperature=-1.0)
        except ValueError as e:
            print(f"  Caught expected error: {e}")

        try:
            summarize_directory(
                directory_path="/tmp", strength=0.5, temperature=0.0,
                csv_file="bad,columns\n1,2"
            )
        except ValueError as e:
            print(f"  Caught expected error: {e}")

        # ------------------------------------------------------------------
        # 5. Error handling (LLM failure is recorded, not crashed)
        # ------------------------------------------------------------------
        print("\n--- 5. Error handling (LLM failure) ---")

        def failing_llm(*args, **kwargs):
            raise RuntimeError("LLM service unavailable")

        with patch('pdd.summarize_directory.llm_invoke', side_effect=failing_llm):
            csv_err, cost_err, model_err = summarize_directory(
                directory_path=test_dir,
                strength=0.5,
                temperature=0.0,
            )

        print(f"  Cost after errors: ${cost_err:.6f}")
        print(f"  CSV still produced (errors recorded in file_summary):")
        for line in csv_err.strip().split('\n')[:3]:
            print(f"    {line}")

    finally:
        shutil.rmtree(test_dir)
        print("\nCleaned up temporary directory.")


if __name__ == "__main__":
    main()
