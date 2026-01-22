"""
Example usage of the agentic_bug_orchestrator module.

This script demonstrates how to invoke the `run_agentic_bug_orchestrator` function.
Since the orchestrator relies on internal modules like `run_agentic_task` and `load_prompt_template`,
this example mocks those dependencies to simulate a successful bug investigation workflow
without making actual LLM calls or requiring a real GitHub issue.

Scenario:
    We simulate an issue where a user reports a "ZeroDivisionError" in a calculator app.
    The orchestrator will step through the 11-step process (including step 5.5 for prompt
    classification), finding the bug, generating a test, and creating a fix.
"""

import sys
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


def mock_run_agentic_task(instruction: str, cwd: Path, verbose: bool, quiet: bool, label: str, **kwargs):
    """
    Mock implementation of run_agentic_task.
    Simulates the output of an LLM agent for each step of the 11-step workflow.
    """
    # Convert step label to identifier (step5_5 -> "5_5", step7 -> "7")
    step_id = label.replace("step", "")

    # Default return values
    success = True
    cost = 0.15  # Simulated cost per step
    provider = "gpt-4-mock"
    output = ""

    if step_id == "1":
        output = "No duplicate issues found. Proceeding."
    elif step_id == "2":
        output = "Checked documentation. This behavior is not documented, likely a bug."
    elif step_id == "3":
        output = "Sufficient information provided in the issue description."
    elif step_id == "4":
        output = "Successfully reproduced the ZeroDivisionError with input (10, 0)."
    elif step_id == "5":
        output = "Root cause identified: 'divide' function lacks check for denominator == 0."
    elif step_id == "5_5":
        output = "DEFECT_TYPE: code\nThis is a code bug - the prompt specifies division by zero should raise ValueError."
    elif step_id == "6":
        output = "Plan: Create a test case 'test_divide_zero' asserting ValueError is raised."
    elif step_id == "7":
        output = "Generated file 'tests/test_calculator_bug.py'.\nFILES_CREATED: tests/test_calculator_bug.py"
    elif step_id == "8":
        output = "Verification successful: The new test fails as expected against current code."
    elif step_id == "9":
        output = "E2E test created and verified.\nE2E_FILES_CREATED: tests/e2e/test_calculator_e2e.py"
    elif step_id == "10":
        output = "Created draft PR #101 linking to issue #42."
    else:
        output = "Unknown step executed."

    return success, output, cost, provider


def main():
    """Main function to run the agentic bug orchestrator simulation."""
    # Define dummy issue data
    issue_data = {
        "issue_url": "https://github.com/example/calculator/issues/42",
        "issue_content": "When I divide by zero, the app crashes instead of raising a clean error.",
        "repo_owner": "example",
        "repo_name": "calculator",
        "issue_number": 42,
        "issue_author": "bug_hunter_99",
        "issue_title": "Crash on division by zero",
        "cwd": Path("./temp_workspace"),
        "verbose": True,
        "quiet": False
    }

    print("Starting Agentic Bug Orchestrator Simulation...")
    print("-" * 60)

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


if __name__ == "__main__":
    main()