"""
Example demonstrating how to use the sync_determine_operation module to analyze
a PDD unit's state and determine the next sync operation.
"""

import os
import sys
from pathlib import Path
import json

# Import the core decision-making function and data structures
from pdd.sync_determine_operation import sync_determine_operation, SyncDecision

def main():
    """
    Demonstrates how to use sync_determine_operation to get the next
    recommended operation for a PDD unit based on its current file state.
    """
    # Create an output directory for our example files
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Set up a mock project structure in the output directory
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    
    # Create a mock prompt file
    basename = "calculator"
    language = "python"
    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    
    print(f"Creating mock prompt file at: {prompt_file}")
    prompt_file.write_text(
        "Create a simple calculator class with add and subtract methods.",
        encoding="utf-8"
    )
    
    print("\n--- Running Sync Analysis ---")
    print(f"Basename: {basename}")
    print(f"Language: {language}")
    
    # Call the decision-making logic in read-only/log mode to avoid mutating real metadata
    # Inputs:
    # - basename: The base name of the module (e.g., 'calculator')
    # - language: The programming language (e.g., 'python')
    # - target_coverage: Target test coverage percentage
    # - budget: Max cost in dollars for the operation
    # - log_mode: True to skip locking and run in read-only mode for analysis
    # - prompts_dir: The directory containing the prompt files
    decision: SyncDecision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=90.0,
        budget=1.0,
        log_mode=True,  # Read-only mode
        prompts_dir=str(prompts_dir)
    )
    
    # Display the results
    # Outputs:
    # - operation: The recommended next command (e.g., 'generate', 'test', 'fix')
    # - reason: Human-readable explanation for the decision
    # - estimated_cost: Estimated cost in dollars to run the operation
    # - confidence: 0.0 to 1.0 score of confidence in this decision
    print("\n--- Decision Results ---")
    print(f"Next Operation: {decision.operation}")
    print(f"Reason:         {decision.reason}")
    print(f"Estimated Cost: ${decision.estimated_cost:.2f}")
    print(f"Confidence:     {decision.confidence:.2f}")
    
    if decision.details:
        print("\nDecision Details:")
        print(json.dumps(decision.details, indent=2))
        
    print("\nExample complete.")

if __name__ == "__main__":
    main()