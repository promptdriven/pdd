import os
import sys
from pathlib import Path
from pdd.sync_determine_operation import sync_determine_operation

def main():
    """
    Example demonstrating how to use the sync_determine_operation module.
    This script creates a dummy prompt file and evaluates the next sync operation.
    """
    # 1. Setup an output directory for our example files
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    # 2. Create a dummy prompt file
    basename = "example_module"
    language = "python"
    prompt_path = prompts_dir / f"{basename}_{language}.prompt"
    
    # Create a prompt that requests a simple function
    prompt_content = "Task: Create a simple greeting function.\n<include>some_dependency.py</include>"
    prompt_path.write_text(prompt_content, encoding="utf-8")

    print(f"Created dummy prompt at: {prompt_path}")
    print("Analyzing sync state (read-only mode)...\n")

    # 3. Call sync_determine_operation
    # We use log_mode=True (which implies read_only) to safely evaluate the state
    # without acquiring file locks or mutating actual metadata.
    decision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=80.0,        # Target test coverage percentage
        budget=5.0,                  # Operation budget in dollars
        log_mode=True,               # Use read-only/log mode to skip locking
        prompts_dir=str(prompts_dir),# Path to the prompts directory
        skip_tests=False,            # Do not skip tests
        skip_verify=False            # Do not skip verification
    )

    # 4. Inspect the decision
    print("--- Sync Decision Results ---")
    print(f"Recommended Operation : {decision.operation}")
    print(f"Reason              : {decision.reason}")
    print(f"Estimated Cost      : ${decision.estimated_cost:.2f}")
    print(f"Confidence          : {decision.confidence:.2f}")
    if decision.details:
        print("Details             :")
        for key, value in decision.details.items():
            print(f"  - {key}: {value}")

if __name__ == "__main__":
    main()