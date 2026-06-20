#!/usr/bin/env python3
"""
Example demonstrating how to use the sync_determine_operation module to analyze
a PDD unit's state and determine the next required sync operation.
"""

import os
import sys
from pathlib import Path

# Ensure the pdd package is discoverable by adding the project root to sys.path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.sync_determine_operation import (
    get_pdd_file_paths,
    sync_determine_operation,
    SyncDecision,
)


def main() -> None:
    # 1. Setup a mock environment inside the designated './output' directory
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    # Define the module metadata we want to inspect
    basename = "calculator"
    language = "Python"
    target_coverage = 80.0  # target test coverage percentage (0.0 to 100.0)

    # Create a mock prompt file (required for the module to resolve paths correctly)
    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    prompt_file.write_text(
        "Generate a robust Calculator class in Python supporting basic arithmetic operations.",
        encoding="utf-8",
    )

    print("--- 1. Resolving PDD File Paths ---")
    # Resolve the expected file paths for prompt, code, example, and tests
    # inputs:
    #   - basename: short name of the module (e.g. 'calculator')
    #   - language: target programming language (e.g. 'Python')
    #   - prompts_dir: directory where prompt files reside
    # returns:
    #   - Dict[str, Path] mapping file keys ('prompt', 'code', 'example', 'test', 'test_files') to Paths
    pdd_paths = get_pdd_file_paths(
        basename=basename,
        language=language,
        prompts_dir=str(prompts_dir),
    )

    for file_type, path in pdd_paths.items():
        if isinstance(path, list):
            print(f"  • {file_type}: {[str(p.relative_to(output_dir.parent)) for p in path]}")
        else:
            print(f"  • {file_type}: {path.relative_to(output_dir.parent)}")

    print("\n--- 2. Determining the Next Sync Operation ---")
    # Determine the next operation based on the current file state and metadata history.
    # Since this is a new module with no fingerprint or run history, the analyzer
    # should deterministically recommend a 'generate' operation.
    # We pass `read_only=True` and `log_mode=True` to run the analysis safely without mutating disk locks.
    # inputs:
    #   - basename: 'calculator'
    #   - language: 'Python'
    #   - target_coverage: 80.0 (desired coverage %)
    #   - log_mode: True (bypasses SyncLock mechanism entirely for read-only analysis)
    #   - prompts_dir: Directory containing prompt files
    #   - read_only: True (prevents metadata mutation)
    # returns:
    #   - SyncDecision: dataclass containing operation, reason, confidence, and estimated_cost
    decision: SyncDecision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=target_coverage,
        log_mode=True,
        prompts_dir=str(prompts_dir),
        read_only=True,
    )

    print(f"Recommended Operation : {decision.operation.upper()}")
    print(f"Reason                : {decision.reason}")
    print(f"Decision Confidence   : {decision.confidence:.2f}")
    print(f"Estimated Cost (USD)  : ${decision.estimated_cost:.2f}")

    if decision.details:
        print(f"Decision Details      : {decision.details}")


if __name__ == "__main__":
    main()