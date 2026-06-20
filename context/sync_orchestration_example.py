"""
Example demonstrating how to use the PDD sync_orchestration module.

This module automates the complete PDD (Prompt-Driven Development) workflow loop
consisting of:
  1. auto-deps (injecting prompt dependencies)
  2. generate (creating code from the prompt)
  3. example (creating a minimal usage example)
  4. crash (resolving runtime errors)
  5. verify (validating output against prompt intent)
  6. test (generating unit tests)
  7. fix (resolving unit test failures)
  8. update (back-propagating learnings to the prompt)

Inputs to sync_orchestration:
    - basename (str): The logical name of the module to sync.
    - target_coverage (float): Desired code coverage percentage (default: 90.0).
    - language (str): Programming language target (default: "python").
    - prompts_dir (str): Path to prompts directory.
    - code_dir (str): Path to source code directory.
    - examples_dir (str): Path to examples directory.
    - tests_dir (str): Path to tests directory.
    - max_attempts (int): Max attempts in iterative loops (default: 3).
    - budget (float): Max total cost allowed for LLM operations in USD (default: 10.0).
    - skip_verify (bool): If True, skips functional verification.
    - skip_tests (bool): If True, skips unit test generation and fixing.
    - dry_run (bool): If True, displays live sync analysis without executing actions.
    - force (bool): If True, bypasses interactive confirmation prompts.
    - strength (float): LLM model power setting from 0.0 to 1.0 (default: 0.5).
    - temperature (float): LLM sampling randomness (default: 0.0).
    - quiet (bool): If True, runs silently without interactive TUI panels.

Outputs of sync_orchestration:
    - A dictionary containing:
        - success (bool): Overall success status.
        - summary (str): Concise human-readable execution summary.
        - operations_completed (list): List of completed operations.
        - skipped_operations (list): List of skipped operations.
        - total_cost (float): Total LLM cost accumulated during the run in USD.
        - total_time (float): Wall-clock execution time in seconds.
        - final_state (dict): Map of target file types and their resolution path/existence.
        - errors (list): List of encountered error messages.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

# Add project root to sys.path to resolve absolute imports correctly
project_root = Path(__file__).resolve().parents[1]
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from pdd.sync_orchestration import sync_orchestration


def setup_mock_environment() -> tuple[Path, dict[str, Path]]:
    """Sets up a mock workspace in the './output' directory."""
    base_dir = Path("./output")
    base_dir.mkdir(parents=True, exist_ok=True)

    # Configure subdirectories
    dirs = {
        "prompts": base_dir / "prompts",
        "src": base_dir / "src",
        "examples": base_dir / "examples",
        "tests": base_dir / "tests",
    }
    for d in dirs.values():
        d.mkdir(parents=True, exist_ok=True)

    # Create a mock prompt file representing a basic calculator module
    prompt_file = dirs["prompts"] / "calculator_python.prompt"
    prompt_content = """---
name: calculator_python
language: Python
---
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "add", "signature": "(a: int, b: int) -> int"}
    ]
  }
}
</pdd-interface>

Create a simple calculator module that implements an add function.
"""
    prompt_file.write_text(prompt_content, encoding="utf-8")

    return base_dir, dirs


def main() -> None:
    print("=== PDD Sync Orchestrator Example ===")

    # Setup the workspace environment
    base_dir, dirs = setup_mock_environment()
    basename = "calculator"

    # Verify LLM Credentials are present for executing the orchestration logic
    api_key = os.environ.get("OPENAI_API_KEY") or os.environ.get("GEMINI_API_KEY")
    if not api_key:
        print("Neither OPENAI_API_KEY nor GEMINI_API_KEY is set.")
        print("Sync operations require LLM access. Exiting example gracefully.")
        sys.exit(0)

    # -------------------------------------------------------------------------
    # Scenario 1: Dry-Run Mode (Pre-flight Sync Analysis)
    # -------------------------------------------------------------------------
    print("\n--- Running Sync in Dry-Run Mode ---")
    dry_run_result = sync_orchestration(
        basename=basename,
        language="python",
        prompts_dir=str(dirs["prompts"]),
        code_dir=str(dirs["src"]),
        examples_dir=str(dirs["examples"]),
        tests_dir=str(dirs["tests"]),
        dry_run=True,
        quiet=True,
    )

    print("Dry-Run Analysis Result:")
    print(f"  • Success Status: {dry_run_result.get('success')}")
    print(f"  • Log Entries Evaluated: {len(dry_run_result.get('log_entries', []))}")

    # -------------------------------------------------------------------------
    # Scenario 2: Headless Workflow Execution (With Skip Handling)
    # -------------------------------------------------------------------------
    print("\n--- Running Headless Sync Workflow (Skip Tests & Verification) ---")
    
    # Run the orchestrator with tests and verification skipped for demonstration.
    # Passing force=True and quiet=True prevents interactive UI panels.
    sync_result = sync_orchestration(
        basename=basename,
        language="python",
        prompts_dir=str(dirs["prompts"]),
        code_dir=str(dirs["src"]),
        examples_dir=str(dirs["examples"]),
        tests_dir=str(dirs["tests"]),
        skip_tests=True,
        skip_verify=True,
        force=True,
        quiet=True,
        budget=2.0,  # Cap budget at $2.00 USD
    )

    print("\nWorkflow Execution Results:")
    print(f"  • Overall Success       : {sync_result.get('success')}")
    print(f"  • Summary Summary       : {sync_result.get('summary')}")
    print(f"  • Completed Operations  : {sync_result.get('operations_completed')}")
    print(f"  • Skipped Operations    : {sync_result.get('skipped_operations')}")
    print(f"  • Total LLM Spend       : ${sync_result.get('total_cost', 0.0):.4f} USD")
    print(f"  • Last Model Invoked    : {sync_result.get('model_name')}")
    print(f"  • Total Time Elapsed    : {sync_result.get('total_time', 0.0):.2f}s")
    
    print("\nFinal Workspace State on Disk:")
    for file_type, info in sync_result.get("final_state", {}).items():
        print(f"  - {file_type:<10}: Exists={info['exists']}, Path={Path(info['path']).name}")


if __name__ == "__main__":
    main()