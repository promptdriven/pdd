"""
Example demonstrating how to use the sync_determine_operation module.

This script creates a dummy prompt file in an output directory, then uses
the sync_determine_operation function to analyze the state of the "demo_unit"
module. Because only the prompt exists (no code, tests, or examples), the
decision engine will logically recommend generating the code (or resolving dependencies).
"""

import os
import sys
from pathlib import Path

# Import the core decision-making function and data class
from pdd.sync_determine_operation import sync_determine_operation, SyncDecision

def main():
    # 1. Setup our dummy workspace
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    
    basename = "demo_unit"
    language = "python"
    
    # Create a mock prompt file so the analyzer has something to read.
    # We include an <include> tag to show how it triggers 'auto-deps' operations.
    prompt_path = prompts_dir / f"{basename}_{language}.prompt"
    prompt_content = """
<include>config.json</include>
Please create a simple calculator module.
"""
    prompt_path.write_text(prompt_content.strip(), encoding="utf-8")
    
    print(f"Created mock prompt at: {prompt_path}")
    print("-" * 50)
    
    # 2. Run the decision analyzer
    # Inputs:
    # - basename: The relative identifier for the module (e.g., 'demo_unit')
    # - language: The programming language (e.g., 'python')
    # - target_coverage: Desired test coverage percentage (float, e.g., 80.0)
    # - budget: Maximum budget in dollars for the operation (float)
    # - log_mode / read_only: If True, skips lock acquisition and metadata mutation
    # - prompts_dir: Directory where prompt files are stored
    print(f"Analyzing sync state for basename='{basename}', language='{language}'...")
    
    decision: SyncDecision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=80.0,
        budget=10.0,
        prompts_dir=str(prompts_dir),
        read_only=True  # Avoids locking and modifying actual metadata for this example
    )
    
    # 3. Inspect the decision
    # Outputs:
    # - operation: The recommended PDD command (e.g., 'auto-deps', 'generate', 'test')
    # - reason: Human-readable explanation of why this operation was chosen
    # - estimated_cost: Estimated cost in dollars to execute this operation
    # - confidence: Confidence level (0.0 to 1.0)
    print("\nDecision Results:")
    print(f"  Operation      : {decision.operation}")
    print(f"  Reason         : {decision.reason}")
    print(f"  Confidence     : {decision.confidence:.2f}")
    print(f"  Estimated Cost : ${decision.estimated_cost:.2f}")
    
    if decision.details:
        print("\nDecision Details (Internal state context):")
        for key, value in decision.details.items():
            print(f"  {key}: {value}")

if __name__ == "__main__":
    main()