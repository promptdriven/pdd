"""
Example demonstrating how to use the pdd.sync_orchestration module.

This script sets up a mock PDD project under the './output' directory and executes the
`sync_orchestration` function, which acts as the core workflow engine behind the
`pdd sync` command.

It showcases:
  1. Setting up a temporary workspace for a mock module ('math_helper')
  2. Resolving PDD conventions for paths
  3. Running sync_orchestration in Dry-Run mode to analyze current state and logs
  4. Executing a live (or mock-key gated) sync loop with visualization parameters
"""

from __future__ import annotations

import os
import sys
import json
import shutil
from pathlib import Path

# Ensure absolute reference for the pdd package in this environment
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.sync_orchestration import sync_orchestration
from pdd.sync_determine_operation import PDD_DIR, META_DIR


def setup_pdd_workspace() -> dict[str, Path]:
    """
    Creates the standardized PDD directory layout inside the './output' folder
    to prepare for the orchestrator execution.
    """
    base_dir = Path("./output").resolve()
    base_dir.mkdir(parents=True, exist_ok=True)

    # Standard directories
    dirs = {
        "prompts": base_dir / "prompts",
        "code": base_dir / "src",
        "examples": base_dir / "examples",
        "tests": base_dir / "tests",
        "meta": base_dir / ".pdd" / "meta",
        "locks": base_dir / ".pdd" / "locks",
    }

    for d in dirs.values():
        d.mkdir(parents=True, exist_ok=True)

    # 1. Create a mock prompt file (authoritative specification)
    prompt_file = dirs["prompts"] / "math_helper_python.prompt"
    prompt_file.write_text(
        "Generate a simple math helper containing a 'square' function.",
        encoding="utf-8"
    )

    # 2. Create a mock code file
    code_file = dirs["code"] / "math_helper.py"
    code_file.write_text(
        "def square(x: int) -> int:\n    return x * x\n",
        encoding="utf-8"
    )

    return dirs


def main() -> None:
    print("=== PDD Sync Orchestrator Example ===")

    # Setup the workspace under ./output
    dirs = setup_pdd_workspace()
    basename = "math_helper"
    language = "python"

    # Set temporary environment flags to force local-mode configuration
    os.environ["PDD_FORCE"] = "1"

    print(f"\n--- 1. Running Sync Orchestration (Dry-Run Mode) ---")
    # Dry-Run mode reads the current codebase layout and displays the decision matrix
    # without running any destructive code mutations.
    dry_run_result = sync_orchestration(
        basename=basename,
        language=language,
        prompts_dir=str(dirs["prompts"]),
        code_dir=str(dirs["code"]),
        examples_dir=str(dirs["examples"]),
        tests_dir=str(dirs["tests"]),
        dry_run=True,   # Enables read-only state review
        quiet=False,
        verbose=True
    )
    print("Dry-Run completed successfully.")

    print(f"\n--- 2. Executing Standard Orchestration (Skip LLM Gates) ---")
    # We run the orchestrator with skip_verify and skip_tests set to True
    # to demonstrate the execution pipeline without making costly LLM calls.
    sync_result = sync_orchestration(
        basename=basename,
        language=language,
        prompts_dir=str(dirs["prompts"]),
        code_dir=str(dirs["code"]),
        examples_dir=str(dirs["examples"]),
        tests_dir=str(dirs["tests"]),
        skip_verify=True,
        skip_tests=True,
        quiet=True,    # Headless mode execution
        budget=5.0     # $5.00 limit
    )

    print("\nOrchestration Result summary:")
    print(f"  • Success Indicator  : {sync_result.get('success')}")
    print(f"  • Completed Steps    : {sync_result.get('operations_completed')}")
    print(f"  • Skipped Steps      : {sync_result.get('skipped_operations')}")
    print(f"  • Total Accum. Cost  : ${sync_result.get('total_cost'):.4f}")
    print(f"  • Summary            : {sync_result.get('summary')}")

    # Gated live orchestration demonstration (gated by Gemini or OpenAI keys)
    api_key = os.environ.get("GEMINI_API_KEY") or os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("\n[INFO] GEMINI_API_KEY or OPENAI_API_KEY is not set.")
        print("Set one of these keys to run a live prompt-to-code compilation.")
        sys.exit(0)

    print(f"\n--- 3. Running Live Compile (Keys Present) ---")
    live_result = sync_orchestration(
        basename=basename,
        language=language,
        prompts_dir=str(dirs["prompts"]),
        code_dir=str(dirs["code"]),
        examples_dir=str(dirs["examples"]),
        tests_dir=str(dirs["tests"]),
        quiet=True,
        force=True
    )
    print(f"Live compile summary: {live_result.get('summary')}")


if __name__ == "__main__":
    main()