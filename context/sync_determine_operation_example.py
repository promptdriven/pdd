"""
Example demonstrating how to use pdd.sync_determine_operation.
This script sets up a simulated PDD workspace and determines the next sync operation.
"""

import json
import os
import shutil
import sys
from pathlib import Path

# Import the core synchronization and path resolution APIs
from pdd.sync_determine_operation import (
    get_pdd_file_paths,
    sync_determine_operation,
    SyncDecision,
)


def run_example():
    """
    Sets up a temporary PDD project structure, runs state analysis to determine
    the next required synchronization operation, and prints the decision results.

    Input Parameters Analysed by sync_determine_operation:
    -----------------------------------------------------
    - basename (str): The unique PDD module name (e.g., 'calculator').
    - language (str): Target language of the code (e.g., 'Python').
    - target_coverage (float): Desired test coverage threshold as a percentage (e.g., 90.0).
    - budget (float): Maximum dollar limit allocated for LLM operations in USD.
    - prompts_dir (str): Root directory where prompt files are stored.
    - skip_tests (bool): If True, bypasses test verification requirements.
    - skip_verify (bool): If True, bypasses runtime validation of example files.
    - read_only (bool): If True, analyzes state without mutating metadata or acquiring file locks.

    Output (SyncDecision Dataclass):
    --------------------------------
    - operation (str): Selected sync action (e.g., 'generate', 'test', 'all_synced', 'nothing').
    - reason (str): Human-readable justification of why the decision was made.
    - confidence (float): AI/Heuristic confidence rating (0.0 to 1.0).
    - estimated_cost (float): Expected cost of running the selected operation in USD.
    - details (dict): Low-level context maps used for debugging state transitions.
    """
    print("--- Setting up simulated workspace under './output' ---")
    
    # Define and clean workspace paths relative to project root
    workspace_root = Path("./output")
    prompts_dir = workspace_root / "prompts"
    meta_dir = workspace_root / ".pdd" / "meta"
    
    # Ensure a clean slate for the example run
    if workspace_root.exists():
        shutil.rmtree(workspace_root)
        
    prompts_dir.mkdir(parents=True, exist_ok=True)
    meta_dir.mkdir(parents=True, exist_ok=True)

    module_basename = "calculator"
    target_language = "Python"

    # Step 1: Create a mock prompt file representing a newly added unit
    prompt_file_path = prompts_dir / f"{module_basename}_{target_language}.prompt"
    prompt_file_path.write_text(
        "Generate a class `Calculator` with `add` and `subtract` methods.", 
        encoding="utf-8"
    )
    print(f"Created mock prompt file: {prompt_file_path}")

    # Step 2: Resolve the expected output artifact paths
    print("\n--- Resolving expected output paths ---")
    artifact_paths = get_pdd_file_paths(
        basename=module_basename,
        language=target_language,
        prompts_dir=str(prompts_dir)
    )

    for artifact_type, path in artifact_paths.items():
        # Represent lists (like test_files) nicely
        path_str = [str(p) for p in path] if isinstance(path, list) else str(path)
        print(f"  {artifact_type.capitalize()}: {path_str}")

    # Step 3: Run determination logic on the newly created unit (expect 'generate')
    print("\n--- Determining initial sync operation (New prompt, no code) ---")
    decision: SyncDecision = sync_determine_operation(
        basename=module_basename,
        language=target_language,
        target_coverage=90.0,     # Target coverage: 90%
        budget=10.0,              # Budget limit: $10.00 USD
        prompts_dir=str(prompts_dir),
        read_only=True            # Run without acquiring system file-locks
    )

    print(f"Recommended Operation: {decision.operation.upper()}")
    print(f"Reason:                {decision.reason}")
    print(f"Estimated Cost:        ${decision.estimated_cost:.2f} USD")
    print(f"Confidence:            {decision.confidence * 100}%")

    # Step 4: Simulate code creation to showcase dynamic transition
    print("\n--- Simulating code file generation ---")
    code_file_path = Path(artifact_paths["code"])
    code_file_path.parent.mkdir(parents=True, exist_ok=True)
    code_file_path.write_text(
        "class Calculator:\n    def add(self, a, b): return a + b", 
        encoding="utf-8"
    )
    print(f"Created simulated code file at: {code_file_path}")

    # Step 5: Re-evaluate state (now should suggest creating an 'example' usage file)
    print("\n--- Re-determining sync operation (Code exists, example missing) ---")
    next_decision: SyncDecision = sync_determine_operation(
        basename=module_basename,
        language=target_language,
        target_coverage=90.0,
        budget=10.0,
        prompts_dir=str(prompts_dir),
        read_only=True
    )

    print(f"Recommended Operation: {next_decision.operation.upper()}")
    print(f"Reason:                {next_decision.reason}")
    print(f"Estimated Cost:        ${next_decision.estimated_cost:.2f} USD")

    # Clean up created files and folders
    print("\n--- Cleaning up simulated workspace ---")
    if workspace_root.exists():
        shutil.rmtree(workspace_root)
    print("Cleanup complete.")

