"""
Example demonstrating how to use the PDD sync_orchestration module.

This script sets up a mock PDD project structure in the './output' directory,
creates a development prompt file, and runs the orchestrator in dry-run mode
to analyze the workspace and determine the synchronization plan.
"""

from __future__ import annotations

import json
import os
import shutil
import sys
from pathlib import Path

# Ensure absolute reference for the pdd package in this environment
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.sync_orchestration import sync_orchestration

# Define the temporary sandbox output directory relative to this script
OUTPUT_DIR = Path("./output").resolve()


def setup_mock_project() -> tuple[Path, dict[str, str]]:
    """Creates a mock project structure and prompt files under the './output' directory."""
    # Clean up any existing outputs to ensure a fresh, predictable state
    if OUTPUT_DIR.exists():
        shutil.rmtree(OUTPUT_DIR)

    # Create standard PDD directories
    prompts_dir = OUTPUT_DIR / "prompts"
    code_dir = OUTPUT_DIR / "src"
    examples_dir = OUTPUT_DIR / "examples"
    tests_dir = OUTPUT_DIR / "tests"

    for directory in [prompts_dir, code_dir, examples_dir, tests_dir]:
        directory.mkdir(parents=True, exist_ok=True)

    # Create a basic prompt file for a factorial utility
    prompt_file = prompts_dir / "factorial_python.prompt"
    prompt_file.write_text(
        "Generate a simple factorial function called 'factorial(n: int) -> int'.",
        encoding="utf-8",
    )

    # Return configured relative paths for the orchestrator
    path_configs = {
        "prompts_dir": str(prompts_dir),
        "code_dir": str(code_dir),
        "examples_dir": str(examples_dir),
        "tests_dir": str(tests_dir),
    }
    return prompt_file, path_configs


def main() -> None: 
    print("=== PDD Sync Orchestrator Example ===")

    # Setup the local file environment
    prompt_file, paths = setup_mock_project()
    basename = "factorial"
    language = "python"

    print(f"Mock Project Configured:")
    print(f"  Basename: '{basename}'")
    print(f"  Language: '{language}'")
    print(f"  Prompt File: {prompt_file}\n")

    # Run the orchestrator in dry_run mode.
    # Dry-run resolves the state from disk and shows what sync would decide to do.
    # It does not acquire locks, execute code generation, or incur LLM costs.
    print("Executing sync_orchestration (dry-run mode)...")
    results = sync_orchestration(
        basename=basename,
        target_coverage=90.0,      # Target code coverage threshold (%)
        language=language,
        prompts_dir=paths["prompts_dir"],
        code_dir=paths["code_dir"],
        examples_dir=paths["examples_dir"],
        tests_dir=paths["tests_dir"],
        max_attempts=3,            # Max fix iterations inside loops
        budget=10.0,               # Maximum allowed monetary budget (USD)
        skip_verify=False,
        skip_tests=False,
        dry_run=True,              # Preview state analysis safely
        force=True,                # Run non-interactively
        verbose=True,              # Output detailed state evaluation logs
        quiet=False,
    )

    # Print out structured results of the dry-run analysis
    print("\n--- Sync Orchestration Results ---")
    print(json.dumps(results, indent=2, default=str))

    # Clean up generated files
    if OUTPUT_DIR.exists():
        shutil.rmtree(OUTPUT_DIR)
        print("\nCleaned up mock project directory.")


if __name__ == "__main__":
    main()