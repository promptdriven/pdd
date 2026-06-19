#!/usr/bin/env python3
"""
Example demonstrating how to use pdd.sync_determine_operation.

This script shows how to resolve code/test/example file paths for a PDD module
and dynamically analyze the workspace state to select the next logical sync operation.
"""

import os
import sys
import json
from pathlib import Path

# Add the workspace root to sys.path so the 'pdd' package can be found
workspace_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(workspace_root))

from pdd.sync_determine_operation import (
    get_pdd_file_paths,
    sync_determine_operation,
    Fingerprint,
    SyncDecision,
    get_meta_dir,
)


def main() -> None:
    # 1. Setup our non-interactive mock project directory in './output'
    output_dir = Path("./output").resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(exist_ok=True)

    # We will simulate a PDD module named 'user_auth' written in 'Python'
    basename = "user_auth"
    language = "Python"
    target_coverage = 80.0  # target unit test coverage threshold (percentage)

    # Create the initial prompt file. Without this file, the sync module
    # cannot analyze the state for the 'user_auth' module.
    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    prompt_file.write_text(
        "Generate a secure password hasher utilizing bcrypt.",
        encoding="utf-8"
    )

    print(f"--- Step 1: Resolving Expected Paths for '{basename}' ---")
    # Resolve expected file locations based on configuration rules.
    # get_pdd_file_paths parameters:
    #   - basename (str): The module identity path (e.g., 'user_auth')
    #   - language (str): The target programming language (e.g., 'Python')
    #   - prompts_dir (str): Relative path to prompts folder
    # Returns:
    #   - Dict[str, Path] containing mapped keys: 'prompt', 'code', 'example', 'test', 'test_files'
    paths = get_pdd_file_paths(
        basename=basename,
        language=language,
        prompts_dir=str(prompts_dir),
    )

    for file_type, file_path in paths.items():
        print(f"  • {file_type.capitalize()}: {file_path}")

    print("\n--- Step 2: Running Sync Analysis (No History -> Expect 'generate') ---")
    # sync_determine_operation parameters:
    #   - basename (str): Module identity
    #   - language (str): Programming language
    #   - target_coverage (float): Target test coverage required to consider complete (0.0 to 100.0)
    #   - budget (float): Maximum allowed budget in dollars for the analysis (Default: 10.0)
    #   - log_mode (bool): If True, bypasses locking entirely (Default: False)
    #   - prompts_dir (str): Location of prompt files
    #   - skip_tests (bool): Skip test generation steps
    #   - skip_verify (bool): Skip verification steps
    # Returns:
    #   - SyncDecision: dataclass representing the determined operation, reasons, and cost metrics.
    decision: SyncDecision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=target_coverage,
        prompts_dir=str(prompts_dir),
        log_mode=True,  # Disable system-level file locking in this demo context
    )

    print(f"Recommended Operation: {decision.operation.upper()}")
    print(f"Reason: {decision.reason}")
    print(f"Estimated Cost: ${decision.estimated_cost:.3f} (Unit: Dollars)")
    print(f"Confidence Level: {decision.confidence * 100:.1f}%")

    print("\n--- Step 3: Mocking State Fingerprint (Expect 'nothing' / 'all_synced') ---")
    # Simulate that generation has completed previously by writing a Fingerprint file
    # into the metadata directory.
    meta_dir = get_meta_dir(paths=paths)
    meta_dir.mkdir(parents=True, exist_ok=True)
    fingerprint_file = meta_dir / f"{basename}_{language.lower()}.json"

    # Touch the expected code, example, and test files so they exist on disk
    paths["code"].parent.mkdir(parents=True, exist_ok=True)
    paths["code"].write_text("def hash_password(pw): return pbkdf2(pw)", encoding="utf-8")
    paths["example"].parent.mkdir(parents=True, exist_ok=True)
    paths["example"].write_text("print(hash_password('secret'))", encoding="utf-8")
    paths["test"].parent.mkdir(parents=True, exist_ok=True)
    paths["test"].write_text("def test_hash(): assert True", encoding="utf-8")

    # Create dummy hashes representing current files
    fingerprint_data = {
        "pdd_version": "1.0.0",
        "timestamp": "2023-10-27T10:00:00Z",
        "command": "verify",
        "prompt_hash": "dummy_prompt_hash",
        "code_hash": "dummy_code_hash",
        "example_hash": "dummy_example_hash",
        "test_hash": "dummy_test_hash",
    }
    
    with open(fingerprint_file, "w", encoding="utf-8") as f:
        json.dump(fingerprint_data, f)

    # Execute determination again with files and fingerprint fully matched
    completed_decision: SyncDecision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=target_coverage,
        prompts_dir=str(prompts_dir),
        skip_tests=True,   # Speed up demo and satisfy completed state easily
        skip_verify=True,
        log_mode=True,
    )

    print(f"Recommended Operation: {completed_decision.operation.upper()}")
    print(f"Reason: {completed_decision.reason}")


if __name__ == "__main__":
    main()