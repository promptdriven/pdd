import json
from pathlib import Path

# In a real project, pdd-cli would be an installed package.
# For this example, we assume the 'pdd' directory is in the python path.
from pdd.sync_orchestration import sync_orchestration, META_DIR

def setup_example_project(root_dir: Path):
    """
    Creates the necessary directories and a dummy prompt file for the example.
    This simulates a basic PDD project layout within the './output' directory.

    Args:
        root_dir (Path): The root directory for the mock project (e.g., './output').
    """
    # Define project file directories
    prompts_dir = root_dir / "prompts"
    src_dir = root_dir / "src"
    examples_dir = root_dir / "examples"
    tests_dir = root_dir / "tests"

    # Create project file directories
    for dir_path in [prompts_dir, src_dir, examples_dir, tests_dir]:
        dir_path.mkdir(parents=True, exist_ok=True)

    # Create the initial prompt file, which is the starting point for the sync
    prompt_content = "Create a Python function that adds two numbers."
    (prompts_dir / "calculator_python.prompt").write_text(prompt_content)
    print(f"Created mock project structure in: {root_dir.resolve()}")

    # The sync orchestrator uses a '.pdd/meta' directory in the CWD for logs and locks.
    # We ensure it exists for the example run.
    META_DIR.mkdir(parents=True, exist_ok=True)
    print(f"Ensured PDD metadata directory exists at: {META_DIR.resolve()}")


if __name__ == "__main__":
    """
    A concise example demonstrating how to use the `sync_orchestration` module.

    This script showcases two primary functionalities:
    1. Running a full PDD sync process for a given `basename`.
    2. Viewing the log of a previously completed sync process.
    """
    output_directory = Path("./output")
    print("--- Setting up mock project for demonstration ---")
    setup_example_project(output_directory)

    # --- 1. Run a full sync orchestration ---
    # This simulates the `pdd sync calculator` command. The orchestrator will
    # determine the necessary steps (generate, example, test, etc.) based on
    # the state of the files and execute them using mock functions.
    print("\n--- Example 1: Running a full sync process ---")
    # We pass the paths to our mock project directories.
    # `quiet=True` is used to suppress the detailed output of the mock
    # sub-commands for a cleaner example output.
    sync_result = sync_orchestration(
        basename="calculator",
        language="python",
        prompts_dir=str(output_directory / "prompts"),
        code_dir=str(output_directory / "src"),
        examples_dir=str(output_directory / "examples"),
        tests_dir=str(output_directory / "tests"),
        budget=5.0,  # Set a budget of $5.00 for the entire process
        quiet=True
    )

    print("\n--- Sync Process Finished ---")
    # The result is a dictionary containing a summary of the entire operation.
    print(json.dumps(sync_result, indent=2, default=str))

    if sync_result.get('success'):
        print("\n✅ Sync completed successfully.")
    else:
        print(f"\n❌ Sync failed. Errors: {sync_result.get('errors')}")


    # --- 2. View the sync state (dry-run mode) ---
    # This simulates the `pdd sync --dry-run calculator` command.
    # It displays the current sync state without executing any operations.
    print("\n--- Example 2: Viewing the sync state (dry-run) ---")
    dry_run_result = sync_orchestration(
        basename="calculator",
        language="python",
        prompts_dir=str(output_directory / "prompts"),
        code_dir=str(output_directory / "src"),
        examples_dir=str(output_directory / "examples"),
        tests_dir=str(output_directory / "tests"),
        dry_run=True,  # This flag changes the function's behavior to analyze without executing
        verbose=False  # Set to True for more detailed output
    )

    print("\n--- Dry-Run Analysis Finished ---")
    # The result dictionary contains the analysis of what would be done.
    print(json.dumps(dry_run_result, indent=2, default=str))