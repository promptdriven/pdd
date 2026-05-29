"""
Example demonstrating how to use the sync_determine_operation module to analyze
a Prompt-Driven Development (PDD) unit's state and determine the next required operation.
"""

import os
import json
from pathlib import Path

# Import the main decision-making function from the PDD module
from pdd.sync_determine_operation import sync_determine_operation


def setup_mock_project() -> Path:
    """Sets up a mock project structure in the output directory."""
    # Create the base output directory for the example
    base_dir = Path("./output/sync_demo").resolve()
    base_dir.mkdir(parents=True, exist_ok=True)

    # Create a prompts directory
    prompts_dir = base_dir / "prompts"
    prompts_dir.mkdir(exist_ok=True)

    # Create a mock prompt file for a "calculator" module
    prompt_file = prompts_dir / "calculator_python.prompt"
    prompt_content = """
    # Calculator Module
    Write a simple calculator class with add and subtract methods.
    """
    prompt_file.write_text(prompt_content.strip(), encoding="utf-8")

    # Create the .pdd metadata directory structure
    meta_dir = base_dir / ".pdd" / "meta"
    meta_dir.mkdir(parents=True, exist_ok=True)

    return base_dir


def main() -> None:
    # 1. Setup a dummy project environment
    project_root = setup_mock_project()
    print(f"Set up mock project at: {project_root}")

    # 2. Change working directory to the mock project root
    # to simulate running the CLI from the project root.
    original_cwd = os.getcwd()
    os.chdir(project_root)

    try:
        # 3. Define the parameters for the PDD unit we are analyzing
        basename = "calculator"
        language = "python"
        target_coverage = 90.0  # Desired test coverage percentage

        print(f"\nAnalyzing PDD unit: '{basename}' ({language})")
        print("This unit has a prompt file but no generated code, tests, or examples yet.")

        # 4. Call sync_determine_operation in read_only mode to get the decision
        # read_only=True ensures we don't accidentally mutate state while just analyzing
        decision = sync_determine_operation(
            basename=basename,
            language=language,
            target_coverage=target_coverage,
            prompts_dir="prompts",
            read_only=True
        )

        # 5. Output the resulting decision
        print("\n--- Sync Decision ---")
        print(f"Next Operation : {decision.operation}")
        print(f"Reason         : {decision.reason}")
        print(f"Confidence     : {decision.confidence:.2f}")
        print(f"Estimated Cost : ${decision.estimated_cost:.2f}")

        if decision.details:
            print("\nDecision Details:")
            print(json.dumps(decision.details, indent=2))

    finally:
        # Restore the original working directory
        os.chdir(original_cwd)


if __name__ == "__main__":
    main()
