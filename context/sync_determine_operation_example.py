import os
import sys
import shutil
from pathlib import Path
import json

# Add the PDD_PATH to sys.path if needed, but normally we assume pdd is installed
from pdd.sync_determine_operation import sync_determine_operation

def setup_mock_project(base_dir: Path, basename: str, language: str) -> None:
    """
    Creates a minimal mock project structure for the sync determination logic to analyze.
    """
    # Create directories
    base_dir.mkdir(parents=True, exist_ok=True)
    prompts_dir = base_dir / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    
    # Create a simple prompt file
    prompt_path = prompts_dir / f"{basename}_{language}.prompt"
    prompt_path.write_text("Task: Implement a basic calculator.", encoding="utf-8")
    
    # Create a code file to simulate partial progress
    code_path = base_dir / f"{basename}.py"
    code_path.write_text("class Calculator:\n    pass", encoding="utf-8")
    
    # Example and Test files are purposefully left out to simulate an incomplete sync state


def main() -> None:
    """
    Example showing how to use `sync_determine_operation` to analyze a module's state
    and determine the next action required to synchronize the project.
    """
    # 1. Prepare environment
    output_dir = Path("./output/sync_determination_example")
    if output_dir.exists():
        shutil.rmtree(output_dir)
    
    basename = "calculator"
    language = "python"
    
    # Set up files inside the output directory
    setup_mock_project(output_dir, basename, language)
    
    # Change working directory so the path resolution logic operates correctly
    original_cwd = Path.cwd()
    os.chdir(output_dir)
    
    print("--- PDD Sync Determination Example ---")
    print(f"Analyzing module: {basename} (Language: {language})")
    print("Current state: Prompt and Code exist. Example and Tests are missing.\n")
    
    # 2. Determine the next operation
    # We use log_mode=True to bypass file locking for this read-only demonstration
    decision = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=90.0,
        budget=5.0,
        log_mode=True,       # Read-only analysis without acquiring locks
        prompts_dir="prompts",
        skip_tests=False,
        skip_verify=False,
    )
    
    # 3. Print the decision
    print(f"Recommended Operation : {decision.operation}")
    print(f"Reason                : {decision.reason}")
    print(f"Confidence Level      : {decision.confidence:.2f}")
    print(f"Estimated Cost        : ${decision.estimated_cost:.2f}")
    
    if decision.details:
        print("\nDetails:")
        print(json.dumps(decision.details, indent=2))
        
    # Restore original working directory
    os.chdir(original_cwd)


if __name__ == "__main__":
    main()