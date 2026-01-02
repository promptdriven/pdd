import sys
import os
from pathlib import Path
from typer.testing import CliRunner

# Add the project root to sys.path to ensure imports work correctly
# This assumes the script is located in examples/ relative to the project root
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

# Import the Typer app object from the CLI module
from src.cli.pddl import app

def create_dummy_prompt(file_path: Path):
    """Creates a sample prompt file for testing purposes."""
    content = """
    Act as a Python Developer.
    Create a script to parse CSV files.
    """
    file_path.write_text(content, encoding="utf-8")
    print(f"Created dummy prompt at: {file_path}")

def main():
    """
    Demonstrates how to invoke the PDD CLI programmatically.
    """
    runner = CliRunner()
    
    # Create a temporary file for linting
    dummy_file = Path("temp_prompt.md")
    create_dummy_prompt(dummy_file)

    try:
        print("\n--- 1. Invoking 'rules' command ---")
        # Equivalent to running: python -m src.cli.pddl rules
        result_rules = runner.invoke(app, ["rules"])
        if result_rules.exit_code == 0:
            print("Successfully listed rules.")
            # Print first few lines of output to verify
            print("\nOutput snippet:")
            print("\n".join(result_rules.stdout.splitlines()[:5]))
        else:
            print("Failed to list rules.")

        print("\n--- 2. Invoking 'lint' command (Text Mode) ---")
        # Equivalent to running: python -m src.cli.pddl lint temp_prompt.md
        result_lint = runner.invoke(app, ["lint", str(dummy_file)])
        
        print(f"Exit Code: {result_lint.exit_code}")
        # Note: Exit code 1 is expected if the dummy prompt has issues (which it does, intentionally)
        if result_lint.exit_code in [0, 1]:
            print("Linting completed (issues found is normal).")
            print("\nOutput snippet:")
            # Print the score line
            for line in result_lint.stdout.splitlines():
                if "Score:" in line:
                    print(line)
        else:
            print(f"Linting failed with runtime error: {result_lint.stderr}")

        print("\n--- 3. Invoking 'lint' command (JSON Mode) ---")
        # Equivalent to running: python -m src.cli.pddl lint temp_prompt.md --format json
        result_json = runner.invoke(app, ["lint", str(dummy_file), "--format", "json"])
        
        if result_json.exit_code in [0, 1]:
            print("JSON Linting completed.")
            print(f"Output starts with: {result_json.stdout[:50]}...")
        
        print("\n--- 4. Invoking 'explain' command ---")
        # Equivalent to running: python -m src.cli.pddl explain PDD001
        result_explain = runner.invoke(app, ["explain", "PDD001"])
        if result_explain.exit_code == 0:
            print("Explanation retrieved successfully.")
            print("\nOutput snippet:")
            print("\n".join(result_explain.stdout.splitlines()[:3]))

    finally:
        # Cleanup
        if dummy_file.exists():
            dummy_file.unlink()
            print(f"\nCleaned up {dummy_file}")

if __name__ == "__main__":
    main()