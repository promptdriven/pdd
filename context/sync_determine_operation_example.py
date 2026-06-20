import os
import sys
import json
from pathlib import Path

# Add the parent directory of the script's directory to sys.path to allow importing the pdd package
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.sync_determine_operation import (
    get_pdd_file_paths,
    sync_determine_operation,
    SyncDecision,
)

def main():
    """
    This example demonstrates how to use the 'sync_determine_operation' module
    to resolve file paths and determine the next logical development step
    (e.g., generate, test, fix, or update) based on the project's current state.
    """
    print("=== Initializing PDD Sync Decision Example ===")

    # Define our output directory for the mock workspace
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    # Define context variables
    basename = "calculator"
    language = "Python"
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a mock prompt file
    # This represents a prompt describing our desired module.
    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    prompt_file.write_text(
        "Create a robust calculator with basic arithmetic operations.", 
        encoding="utf-8"
    )
    print(f"Created mock prompt file: {prompt_file.relative_to(Path.cwd())}")

    # 2. Resolve PDD paths for the module
    # get_pdd_file_paths determines where code, test, and example files are
    # located relative to the workspace configuration.
    print("\n--- Resolving File Paths ---")
    paths = get_pdd_file_paths(
        basename=basename,
        language=language,
        prompts_dir=str(prompts_dir)
    )

    # Documenting the expected returned paths structure:
    # - 'prompt': Path to the original prompt file
    # - 'code': Expected path for generated implementation code
    # - 'example': Expected path for usage example code
    # - 'test': Expected path for test files
    # - 'test_files': List of all matching test files for multi-file test coverage
    for key, path in paths.items():
        if isinstance(path, list):
            paths_str = ", ".join(str(p.relative_to(Path.cwd())) for p in path)
            print(f"  • {key}: [{paths_str}]")
        else:
            print(f"  • {key}: {path.relative_to(Path.cwd())}")

    # 3. Determine the next PDD operation
    # sync_determine_operation analyzes the disk state and metadata to select
    # the next action in the PDD workflow.
    #
    # Parameters explained:
    # - basename (str): The logical name of the module.
    # - language (str): The programming language.
    # - target_coverage (float): The desired test coverage percentage (e.g., 90.0).
    # - budget (float): Maximum dollar budget to allow for LLM operations.
    # - prompts_dir (str): Location of the prompts folder.
    # - read_only (bool): If True, skips mutating any state files while analyzing.
    print("\n--- Running State Analysis ---")
    decision: SyncDecision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=90.0,
        budget=10.0,
        prompts_dir=str(prompts_dir),
        read_only=True
    )

    # 4. Display the Sync Decision Results
    # Output properties of SyncDecision:
    # - operation (str): The selected action (e.g., 'generate', 'test', 'fix', 'nothing')
    # - reason (str): Human-readable explanation of why this decision was made
    # - confidence (float): Certainty score of the decision engine (0.0 to 1.0)
    # - estimated_cost (float): Estimated cost in dollars for the chosen operation
    # - details (dict): Extra debugging contexts/metadata
    print("\n--- Determined Sync Decision ---")
    print(f"  • Recommended Operation : {decision.operation.upper()}")
    print(f"  • Reason                : {decision.reason}")
    print(f"  • Confidence Score      : {decision.confidence:.2f}")
    print(f"  • Estimated LLM Cost    : ${decision.estimated_cost:.2f}")
    
    if decision.details:
        print(f"  • Details               : {json.dumps(decision.details)}")

    print("\n=== Example Run Completed Successfully ===")

if __name__ == "__main__":
    main()