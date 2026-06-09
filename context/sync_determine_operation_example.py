"""
Example demonstrating how to resolve file paths and determine the next PDD 
sync operation based on the current disk state and metadata.

This example is non-interactive and runs completely to completion.
"""

import os
import sys
import json
from pathlib import Path

# Add the workspace root to sys.path for importing the pdd package
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.sync_determine_operation import (
    get_pdd_file_paths,
    sync_determine_operation,
    SyncDecision
)


def run_sync_analysis_example() -> None: 
    """
    Demonstrates file path resolution and sync decision-making for a PDD unit.
    
    Creates a mock environment under the './output' directory to simulate 
    a new prompt file requiring code generation.
    """
    # Define a clean output space
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    # 1. Setup a Mock PDD Unit (Calculator in Python)
    basename = "calculator"
    language = "Python"
    target_coverage = 90.0  # target unit test coverage percentage (0.0 to 100.0)

    # Write a mock prompt file to initiate the workflow
    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    prompt_file.write_text(
        "Generate a simple Calculator class with add and subtract methods.", 
        encoding="utf-8"
    )

    print(f"--- 1. Resolved PDD File Artifact Paths ---")
    # Resolve the expected locations for code, tests, and examples based on conventions
    # Inputs:
    #   - basename (str): The unique module identifier
    #   - language (str): Target language of the project
    #   - prompts_dir (str): Relative path to prompts source folder
    # Outputs:
    #   - Dict[str, Path]: Maps artifact keys ('prompt', 'code', 'test', 'example') to Path objects
    paths = get_pdd_file_paths(
        basename=basename,
        language=language,
        prompts_dir=str(prompts_dir)
    )

    for artifact, path in paths.items():
        # Handle 'test_files' list separately from single Path structures
        path_str = ", ".join(str(p) for p in path) if isinstance(path, list) else str(path)
        print(f"  • {artifact:<10} -> {path_str}")

    print(f"\n--- 2. Determining Initial Sync Operation ---")
    # Execute the core deterministic decision logic
    # Inputs:
    #   - basename (str): PDD unit base name
    #   - language (str): Target language
    #   - target_coverage (float): Target test coverage
    #   - log_mode (bool): If True, bypass locks entirely for read-only analysis
    #   - prompts_dir (str): Prompts root directory
    # Outputs:
    #   - SyncDecision (dataclass): Contains next operation, reasoning, and estimated costs
    decision: SyncDecision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=target_coverage,
        prompts_dir=str(prompts_dir),
        log_mode=True  # Bypasses local lock-file generation for clean dry-run behavior
    )

    # Display decision details
    print(f"  • Recommended Operation : {decision.operation.upper()}")
    print(f"  • Decision Rationale    : {decision.reason}")
    print(f"  • Estimated LLM Cost    : ${decision.estimated_cost:.2f} (USD)")
    print(f"  • Confidence Level      : {decision.confidence * 100:.1f}%")
    
    if decision.details:
        print(f"  • Decision Details      : {json.dumps(decision.details)}")


if __name__ == "__main__":
    run_sync_analysis_example()