"""
Example demonstrating how to use the sync_determine_operation module.
This script sets up a minimal project structure with a prompt file
and uses the module to determine the next PDD operation.
"""

import os
import sys
import shutil
from pathlib import Path
import json

# Import the function from the module
from pdd.sync_determine_operation import sync_determine_operation

def main():
    print("--- sync_determine_operation example ---")
    
    # 1. Set up a dummy project structure in the ./output directory
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    meta_dir = output_dir / ".pdd" / "meta"
    
    # Clean up existing output if any
    if output_dir.exists():
        shutil.rmtree(output_dir)
        
    prompts_dir.mkdir(parents=True, exist_ok=True)
    meta_dir.mkdir(parents=True, exist_ok=True)
    
    basename = "hello_world"
    language = "python"
    
    # Create a simple prompt file
    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    prompt_file.write_text(
        "Write a simple hello world function in Python.\n", 
        encoding="utf-8"
    )
    
    print(f"Created dummy prompt at: {prompt_file}")
    
    # 2. Run sync_determine_operation on the new unit
    # Since there's no code, example, or fingerprint yet, it should recommend 'generate'
    print("\nAnalyzing state for new module...")
    
    decision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=80.0,
        prompts_dir=str(prompts_dir),
        log_mode=True  # log_mode=True skips file locking for read-only analysis
    )
    
    print(f"Recommended Operation: {decision.operation}")
    print(f"Reason: {decision.reason}")
    print(f"Confidence: {decision.confidence:.2f}")
    if decision.details:
        print(f"Details: {json.dumps(decision.details, indent=2)}")
        
    # 3. Simulate code generation to see how the decision changes
    print("\nSimulating code generation (creating code file)...")
    code_file = output_dir / f"{basename}.py"
    code_file.write_text("def hello():\n    print('Hello World!')\n", encoding="utf-8")
    
    # We also need to simulate a fingerprint so it knows the code matches the prompt
    # For this example, we'll just show the decision when code exists but no fingerprint
    # The module will see a missing fingerprint and suggest generating one (or regenerating)
    decision_after_code = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=80.0,
        prompts_dir=str(prompts_dir),
        log_mode=True
    )
    
    print(f"Recommended Operation (after code exists but no meta): {decision_after_code.operation}")
    print(f"Reason: {decision_after_code.reason}")
    
    print("\nExample complete.")

if __name__ == "__main__":
    main()