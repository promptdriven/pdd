import os
import sys
import shutil
from pathlib import Path

# Import the main function from the module
from pdd.fix_error_loop import fix_error_loop


def main():
    """
    Demonstrates how to use the fix_error_loop function to automatically
    repair broken code based on unit test failures.
    """
    print("=== pdd.fix_error_loop Example ===")

    # Ensure we have an output directory for our temporary files
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    # Define paths for our files
    code_file = output_dir / "broken_math.py"
    test_file = output_dir / "test_broken_math.py"
    prompt_file = output_dir / "fix_prompt.txt"
    error_log_file = output_dir / "fix_error_log.txt"

    # 1. Create a deliberately broken code file
    code_content = """
def add_numbers(a, b):
    # Bug: subtracts instead of adds
    return a - b
"""
    code_file.write_text(code_content, encoding="utf-8")

    # 2. Create a unit test that will fail
    test_content = """
from broken_math import add_numbers

def test_add_numbers():
    assert add_numbers(2, 3) == 5
"""
    test_file.write_text(test_content, encoding="utf-8")

    # 3. Create a prompt file explaining what needs to be fixed
    prompt_content = "Fix the add_numbers function so it actually adds the two arguments."
    prompt_file.write_text(prompt_content, encoding="utf-8")

    print(f"Created test scenario in {output_dir}")
    print("Running fix_error_loop... (This may take a moment as it invokes the LLM/pytest)")

    # 4. Run the fix loop
    # We use sys.executable as the verification program to run pytest
    # Set agentic_fallback=False for a simpler, localized test
    success, final_test, final_code, attempts, cost, model = fix_error_loop(
        unit_test_file=str(test_file),
        code_file=str(code_file),
        prompt_file=str(prompt_file),
        prompt=prompt_content,
        verification_program=sys.executable,  # uses current python environment
        strength=0.7,
        temperature=0.2,
        max_attempts=2,
        budget=1.0,  # maximum dollars to spend
        error_log_file=str(error_log_file),
        verbose=True,
        agentic_fallback=False,  # Disable full agent fallback for this quick example
        protect_tests=True       # Instruct the LLM not to change the tests, only the code
    )

    # 5. Output the results
    print("\n=== Fix Loop Results ===")
    print(f"Success: {success}")
    print(f"Attempts: {attempts}")
    print(f"Estimated Cost: ${cost:.6f}")
    print(f"Model Used: {model}")

    print("\n--- Final Code ---")
    print(final_code)

    if error_log_file.exists():
        print(f"\nDetailed logs were written to: {error_log_file}")


if __name__ == "__main__":
    # The fix loop requires an LLM to actually suggest code changes.
    # Often, this relies on API keys being present in the environment.
    # If you run this without keys, it will likely fail on the LLM step but still
    # demonstrate the loop initialization and fallback mechanisms.
    main()