import os
import sys
import shutil
from pathlib import Path

# Ensure the pdd package is discoverable by inserting the project root into sys.path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.sync_orchestration import sync_orchestration

def main():
    """
    Demonstrates how to invoke the sync_orchestration workflow.
    
    sync_orchestration coordinates the complete Prompt-Driven Development (PDD)
    lifecycle (auto-deps -> generate -> example -> crash -> verify -> test -> fix -> update).

    Inputs:
        basename (str): The base name for the module prompt (e.g. 'calculator').
        target_coverage (float): Desired code coverage percentage. Defaults to 90.0.
        language (str): Target language of the generated code. Defaults to 'python'.
        prompts_dir (str): Directory where prompt files reside. Defaults to 'prompts'.
        code_dir (str): Directory where generated code will be saved. Defaults to 'src'.
        examples_dir (str): Directory where examples will be saved. Defaults to 'examples'.
        tests_dir (str): Directory where tests will be saved. Defaults to 'tests'.
        dry_run (bool): If True, analyzes and returns current sync state logs without modifying code.
        quiet (bool): Suppresses animation / visual CLI output if True.
        force (bool): Overwrites target files without interactive CLI confirmation.
        strength (float): AI model strength setting from 0.0 to 1.0.

    Returns:
        Dict[str, Any]: A dictionary containing:
            - success (bool): Overall completion status.
            - operations_completed (List[str]): List of completed operation stages.
            - skipped_operations (List[str]): List of skipped operation stages.
            - total_cost (float): Total LLM cost in USD.
            - total_time (float): Total elapsed time in seconds.
            - errors (List[str]): Captured errors.
            - summary (str): A descriptive overview message.
    """
    # Setup clean output directory structures relative to current directory
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    code_dir = output_dir / "src"
    examples_dir = output_dir / "examples"
    tests_dir = output_dir / "tests"

    prompts_dir.mkdir(parents=True, exist_ok=True)
    code_dir.mkdir(parents=True, exist_ok=True)
    examples_dir.mkdir(parents=True, exist_ok=True)
    tests_dir.mkdir(parents=True, exist_ok=True)

    # Generate a dummy prompt so the orchestrator has a target to analyze
    basename = "calculator"
    prompt_file = prompts_dir / f"{basename}_python.prompt"
    prompt_file.write_text(
        "Write a Python Calculator class with add, subtract, and multiply methods.",
        encoding="utf-8"
    )

    print("--- 1. Running Sync Orchestration in Dry-Run (Heuristic Analysis) Mode ---")
    # We execute with dry_run=True to inspect the current state changes cleanly
    # without making active LLM calls or mutating state files.
    dry_run_results = sync_orchestration(
        basename=basename,
        target_coverage=90.0,
        language="python",
        prompts_dir=str(prompts_dir),
        code_dir=str(code_dir),
        examples_dir=str(examples_dir),
        tests_dir=str(tests_dir),
        dry_run=True,
        quiet=True,
        force=True
    )

    print(f"Success                  : {dry_run_results.get('success')}")
    print(f"Log Entries Found        : {len(dry_run_results.get('log_entries', []))}")
    
    # Optional: If an API key is present, we can demonstrate a live sync
    # otherwise we skip gracefully to comply with non-interactive headless requirements.
    api_key = os.environ.get("OPENAI_API_KEY") or os.environ.get("GEMINI_API_KEY")
    if api_key:
        print("\n--- 2. Live Key Detected: Running Live Orchestration Flow ---")
        live_results = sync_orchestration(
            basename=basename,
            target_coverage=90.0,
            language="python",
            prompts_dir=str(prompts_dir),
            code_dir=str(code_dir),
            examples_dir=str(examples_dir),
            tests_dir=str(tests_dir),
            dry_run=False,
            quiet=True,
            force=True,
            budget=2.0,  # Strict $2 limit for example
            strength=0.0  # Cheapest model for speed/cost
        )
        print(f"Sync Success             : {live_results.get('success')}")
        print(f"Operations Executed      : {live_results.get('operations_completed')}")
        print(f"Total LLM Cost (USD)     : ${live_results.get('total_cost', 0.0):.4f}")
        print(f"Execution Summary        : {live_results.get('summary')}")
    else:
        print("\n--- 2. Skipping Live Orchestration (No API key in env) ---")

    # Cleanup generated artifacts
    if output_dir.exists():
        shutil.rmtree(output_dir, ignore_errors=True)

if __name__ == "__main__":
    main()