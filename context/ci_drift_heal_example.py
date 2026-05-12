"""
Example demonstrating how to use the ci_drift_heal module.

This module is designed to run in CI pipelines to detect and auto-heal
prompt and example drift in PDD modules.
"""

import os
import sys
from unittest.mock import patch

# Import the functions from the module
from pdd.ci_drift_heal import main, detect_drift, DriftInfo


def demonstrate_detect_drift():
    """
    Demonstrates how to call detect_drift directly to get lists of drifted modules.
    """
    print("--- Demonstrating detect_drift ---")
    
    # Mock the internal detection to return some dummy drift data
    # so this example runs without a real PDD workspace.
    mock_prompt_drifts = [
        DriftInfo(
            basename="example_module",
            language="python",
            operation="update",
            reason="Code changed without prompt changes",
            code_path="pdd/example_module.py",
            prompt_path="prompts/example_module_python.prompt"
        )
    ]
    mock_example_drifts = [
        DriftInfo(
            basename="another_module",
            language="python",
            operation="example",
            reason="Prompt changed, example needs refresh",
            code_path="pdd/another_module.py",
            prompt_path="prompts/another_module_python.prompt",
            example_path="context/another_module_example.py"
        )
    ]
    
    with patch("pdd.ci_drift_heal.detect_drift", return_value=(mock_prompt_drifts, mock_example_drifts)):
        prompt_drifts, example_drifts = detect_drift(modules=None, diff_base="main")
        
        print(f"Detected {len(prompt_drifts)} modules needing prompt updates:")
        for drift in prompt_drifts:
            print(f"  - {drift.basename}: {drift.reason}")
            
        print(f"Detected {len(example_drifts)} modules needing example updates:")
        for drift in example_drifts:
            print(f"  - {drift.basename}: {drift.reason}")


def demonstrate_main():
    """
    Demonstrates how to run the main entry point which detects drift, heals it,
    and commits the changes.
    """
    print("\n--- Demonstrating main entry point ---")
    
    # We mock main so it doesn't actually try to run git commands or LLM calls in this example.
    with patch("pdd.ci_drift_heal.main", return_value=0) as mock_main:
        # Run main with a budget cap of $5.00, in push-to-main mode (skip_ci=True)
        # and comparing against the 'main' branch (diff_base='main')
        exit_code = main(
            modules=["example_module"],  # Only heal specific modules
            budget_cap=5.0,              # $5.00 limit for LLM costs
            skip_ci=True,                # Add [skip ci] to commit message
            diff_base="main"             # Base branch for drift detection
        )
        
        print(f"Main function returned exit code: {exit_code}")
        print(f"Main was called with arguments: {mock_main.call_args}")


if __name__ == "__main__":
    # Ensure output directory exists for any file operations
    output_dir = os.path.join(os.path.dirname(__file__), "..", "output")
    os.makedirs(output_dir, exist_ok=True)
    
    print("PDD CI Drift Heal Example")
    print("=========================")
    
    demonstrate_detect_drift()
    demonstrate_main()
    
    print("\nExample completed successfully.")