import os
import sys
import json
from pathlib import Path
from typing import Dict, Any

# Import the necessary functions and dataclasses from the module
from pdd.sync_determine_operation import sync_determine_operation, SyncDecision

def main() -> None:
    """
    Demonstrates how to use the `sync_determine_operation` function to analyze
    the state of a module and decide the next appropriate synchronization operation.
    
    This example simulates a 'new module' scenario where only the prompt file exists,
    meaning the expected next operation should be 'generate' (or 'auto-deps').
    """
    # Setup output directory for our mock project structure
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    
    # Inputs for the operation
    basename = "demo_calculator"
    language = "python"
    target_coverage = 85.0  # Percentage
    budget = 5.0            # Dollars
    
    # Create a mock prompt file so the analyzer finds it
    # The expected prompt file name pattern is {basename}_{language}.prompt
    prompt_path = prompts_dir / f"{basename}_{language}.prompt"
    prompt_content = """
    Write a simple calculator class in Python with add and subtract methods.
    """
    prompt_path.write_text(prompt_content.strip())
    
    print(f"Analyzing sync state for module: '{basename}' ({language})")
    print(f"Target Coverage: {target_coverage}% | Budget: ${budget}")
    print(f"Prompts Directory: {prompts_dir}\n")
    
    # Determine the next operation
    # log_mode=True is used here to avoid creating file locks during analysis
    # read_only=True ensures we don't accidentally mutate the state
    decision: SyncDecision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=target_coverage,
        budget=budget,
        log_mode=True,       # Skip locking for read-only analysis
        prompts_dir=str(prompts_dir),
        skip_tests=False,
        skip_verify=False,
        read_only=True
    )
    
    # Display the results
    # For a new module with just a prompt, the expected operation is 'generate'
    print("--- Sync Decision Results ---")
    print(f"Operation:      {decision.operation}")
    print(f"Reason:         {decision.reason}")
    print(f"Confidence:     {decision.confidence * 100:.1f}%")
    print(f"Estimated Cost: ${decision.estimated_cost:.2f}")
    
    if decision.details:
        print("\nDetails:")
        print(json.dumps(decision.details, indent=2))

if __name__ == "__main__":
    main()