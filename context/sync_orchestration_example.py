"""
Example demonstrating the usage of the sync_orchestration module.

This script sets up a dummy project structure with a prompt file, and then
uses the `sync_orchestration` function in `dry_run` mode to analyze the state
of the module and determine what operations would be performed, without actually
making any LLM calls or mutating the files.
"""

import os
import sys
import json
from pathlib import Path

# Ensure the pdd package is importable
current_dir = Path(__file__).resolve().parent
project_root = current_dir.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from pdd.sync_orchestration import sync_orchestration


def main() -> None:
    """
    Runs a dry-run sync orchestration on a dummy module to demonstrate the API.
    """
    print("=== sync_orchestration Example ===")

    # 1. Setup dummy project structure in ./output
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    src_dir = output_dir / "src"
    
    prompts_dir.mkdir(parents=True, exist_ok=True)
    src_dir.mkdir(parents=True, exist_ok=True)
    
    basename = "calculator"
    language = "python"
    
    prompt_path = prompts_dir / f"{basename}_{language}.prompt"
    prompt_path.write_text(
        "<pdd-reason>Calculate things</pdd-reason>\n"
        "Create a calculator module with an add function.",
        encoding="utf-8"
    )
    
    print(f"Created mock prompt at: {prompt_path}")
    
    # 2. Call the orchestrator in dry_run mode
    # In dry_run mode, it analyzes what needs to be done but doesn't execute the LLM steps.
    print("\nRunning sync_orchestration (dry_run=True, quiet=True)...")
    
    result = sync_orchestration(
        basename=basename,
        language=language,
        target_coverage=90.0,
        prompts_dir=str(prompts_dir),
        code_dir=str(src_dir),
        examples_dir=str(output_dir / "examples"),
        tests_dir=str(output_dir / "tests"),
        budget=10.0,           # Maximum cost allowed (USD)
        max_attempts=3,        # Max retry attempts for fix loops
        dry_run=True,          # Only analyze, don't execute
        quiet=True,            # Suppress TUI and rich output
        force=True,            # Auto-confirm any prompts
        agentic_mode=False
    )
    
    # 3. Display the results
    # The result is a dictionary containing success status, summaries, and logs.
    print("\n--- Orchestration Result ---")
    print(f"Success: {result.get('success')}")
    
    if 'log_entries' in result:
        print(f"Log Entries Found: {len(result['log_entries'])}")
        for entry in result['log_entries']:
            print(f"  - Operation: {entry.get('operation')} | Reason: {entry.get('reason')}")
    else:
        print(f"Summary: {result.get('summary')}")
        print(f"Operations Completed: {result.get('operations_completed')}")
        print(f"Total Cost: ${result.get('total_cost', 0.0):.2f}")

if __name__ == "__main__":
    main()