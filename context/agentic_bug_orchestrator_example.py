"""
Example usage of the agentic_bug_orchestrator module.

This script demonstrates how to invoke the `run_agentic_bug_orchestrator` function.
Since the orchestrator relies on internal modules like `run_agentic_task` and `load_prompt_template`,
this example mocks those dependencies to simulate a successful bug investigation workflow
without making actual LLM calls or requiring a real GitHub issue.

Scenario:
    We simulate an issue where a user reports a "ZeroDivisionError" in a calculator app.
    The orchestrator will step through the 9-step process, finding the bug, generating a test,
    and creating a fix.
"""

import sys
import shutil
import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure the project root is in sys.path so we can import the module
# Adjust this path based on your actual project structure relative to this script
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

try:
    # Import the module to be tested
    # Note: We assume the file is at pdd/agentic_bug_orchestrator.py
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator
except ImportError:
    print("Error: Could not import 'pdd.agentic_bug_orchestrator'.")
    print("Ensure your PYTHONPATH is set correctly or the file structure matches.")
    sys.exit(1)


def mock_load_prompt_template(template_name: str) -> str:
    """
    Mock implementation of load_prompt_template.
    Returns a dummy prompt string based on the requested template name.
    """
    return f"MOCK PROMPT FOR: {template_name}\nContext: {{issue_content}}"


def mock_run_agentic_task(instruction: str, cwd: Path, verbose: bool, quiet: bool, label: str, timeout: float = 340.0, max_retries: int = 3):
    """
    Mock implementation of run_agentic_task.
    Simulates the output of an LLM agent for each step of the workflow.
    """
    step_num = label.replace("step", "").replace("_", ".")
    
    # Default return values
    success = True
    cost = 0.15  # Simulated cost per step
    provider = "gpt-4-mock"
    files = []
    output = ""

    if step_num == "1":
        output = "No duplicate issues found. Proceeding."
    elif step_num == "2":
        output = "Checked documentation. This behavior is not documented, likely a bug."
    elif step_num == "3":
        output = "Sufficient information provided in the issue description."
    elif step_num == "4":
        output = "Successfully reproduced the ZeroDivisionError with input (10, 0)."
    elif step_num == "5":
        output = "Root cause identified: 'divide' function lacks check for denominator == 0."
    elif step_num == "5.5":
        output = "DEFECT_TYPE: code"
    elif step_num == "6":
        output = "Plan: Create a test case 'test_divide_zero' asserting ValueError is raised."
    elif step_num == "7":
        output = "Generated file 'tests/test_calculator_bug.py'.\nFILES_CREATED: tests/test_calculator_bug.py"
        files = ["tests/test_calculator_bug.py"]
    elif step_num == "8":
        output = "Verification successful: The new test fails as expected against current code."
    elif step_num == "9":
        output = "E2E tests passed."
    elif step_num == "10":
        output = "Created draft PR #101 linking to issue #42."
    else:
        output = f"Unknown step executed: {step_num}"

    return success, output, cost, provider


def setup_dummy_git_repo(path: Path):
    """Initialize a dummy git repo so the orchestrator's git commands work."""
    path.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "init"], cwd=path, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "you@example.com"], cwd=path, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.name", "Your Name"], cwd=path, check=True, capture_output=True)
    # Create a dummy file to commit so we have a HEAD
    (path / "README.md".strip()).write_text("test repo")
    subprocess.run(["git", "add", "README.md"], cwd=path, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=path, check=True, capture_output=True)


def main():
    """Main function to run the agentic bug orchestrator simulation."""
    
    # Create a temporary workspace
    workspace_dir = Path("./temp_workspace")
    if workspace_dir.exists():
        shutil.rmtree(workspace_dir)
    
    print(f"Setting up temporary workspace at {workspace_dir}...")
    setup_dummy_git_repo(workspace_dir)

    # Define dummy issue data
    issue_data = {
        "issue_url": "https://github.com/example/calculator/issues/42",
        "issue_content": "When I divide by zero, the app crashes instead of raising a clean error.",
        "repo_owner": "example",
        "repo_name": "calculator",
        "issue_number": 42,
        "issue_author": "bug_hunter_99",
        "issue_title": "Crash on division by zero",
        "cwd": workspace_dir,
        "verbose": True,
        "quiet": False
    }

    print("Starting Agentic Bug Orchestrator Simulation...")
    print("-" * 60)

    try:
        # Patch the internal dependencies
        # We patch where they are imported IN the orchestrator module, not where they are defined
        with patch("pdd.agentic_bug_orchestrator.load_prompt_template", side_effect=mock_load_prompt_template), \
             patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task):

            # Run the orchestrator
            success, final_msg, total_cost, model, changed_files = run_agentic_bug_orchestrator(
                **issue_data
            )

        print("-" * 60)
        print("Simulation Complete.")
        print(f"Success: {success}")
        print(f"Final Message: {final_msg}")
        print(f"Total Cost: ${total_cost:.2f}")
        print(f"Model Used: {model}")
        print(f"Changed Files: {changed_files}")

    finally:
        # Cleanup
        if workspace_dir.exists():
            # We might need to force remove if git worktrees were created inside (though orchestrator puts them in .pdd)
            # For this simple test, standard rmtree is usually fine, but git sometimes holds locks.
            try:
                shutil.rmtree(workspace_dir)
                print("Cleaned up temporary workspace.")
            except Exception as e:
                print(f"Warning: Could not clean up workspace: {e}")


if __name__ == "__main__":
    main()