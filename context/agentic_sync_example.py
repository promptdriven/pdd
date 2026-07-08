from __future__ import annotations

import json
import os
import sys
from pathlib import Path

# Ensure we can import from the pdd package
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.agentic_sync import run_global_sync, run_agentic_sync

def setup_mock_project(base_dir: Path) -> None:
    """
    Set up a mock PDD project structure in the specified directory.
    This creates a mock architecture.json, .pddrc, and prompt file
    for dry-run synchronization analysis.
    """
    base_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a mock architecture.json defining a single module
    architecture_data = {
        "modules": [
            {
                "filename": "math_utils_python.prompt",
                "filepath": "math_utils.py",
                "reason": "Provides basic mathematical helper functions.",
                "dependencies": []
            }
        ]
    }
    (base_dir / "architecture.json").write_text(
        json.dumps(architecture_data, indent=2), encoding="utf-8"
    )

    # 2. Create a mock .pddrc configuration file
    pddrc_data = {
        "version": "1.0",
        "contexts": {
            "default": {
                "defaults": {
                    "generate_output_path": ".",
                    "prompts_dir": "prompts",
                    "default_language": "python"
                }
            }
        }
    }
    (base_dir / ".pddrc").write_text(
        json.dumps(pddrc_data, indent=2), encoding="utf-8"
    )

    # 3. Create the prompts directory and a mock prompt file
    prompts_dir = base_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    prompt_content = (
        "<pdd-reason>Provides basic mathematical helper functions.</pdd-reason>\n\n"
        "Generate a Python helper module containing basic math functions such as add and subtract."
    )
    (prompts_dir / "math_utils_python.prompt").write_text(
        prompt_content, encoding="utf-8"
    )


def main() -> None:
    """
    Demonstrate the usage of run_global_sync in dry-run mode.
    This showcases how PDD analyzes project prompts and builds sync plans.
    """
    print("--- PDD Agentic Sync Module Demonstration ---")

    # Define the isolated output directory for the mock workspace
    output_dir = Path("./output").resolve()
    setup_mock_project(output_dir)

    # Change the current working directory to our mock project root so that
    # PDD context discovery and architecture loaders locate the workspace.
    original_cwd = os.getcwd()
    os.chdir(output_dir)

    try:
        print("\n[1] Running global sync in dry-run mode...")
        # run_global_sync returns a 4-tuple: (success, message, total_cost, model_used)
        # - success: True if the sync plan completed without error.
        # - message: Summary of the sync results or planning decisions.
        # - total_cost: Cumulative token costs in USD (0.0 for dry-run).
        # - model_used: Label of the LLM or process used ("global-sync").
        success, message, cost, model = run_global_sync(
            dry_run=True,
            quiet=False,
            verbose=False
        )

        print(f"\nSync Execution Successful: {success}")
        print(f"Planning Result Message: {message}")
        print(f"Estimated Cost: ${cost:.2f}")
        print(f"Execution Mode: {model}")

    finally:
        # Always restore the original working directory
        os.chdir(original_cwd)

    print("\n--- Demonstration Complete ---")


if __name__ == "__main__":
    main()