"""
Example usage of the agentic_change_orchestrator module.

This script demonstrates how to invoke the `run_agentic_change_orchestrator` function.
Since the orchestrator relies on internal modules like `run_agentic_task` and `load_prompt_template`,
this example mocks those dependencies to simulate a successful change workflow
without making actual LLM calls or requiring a real GitHub issue.

Scenario:
    We simulate an issue where a user requests adding a new validation feature
    to a user service module. The orchestrator will step through the 6-step process,
    identifying affected dev units and modifying the relevant prompts.
"""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure the project root is in sys.path so we can import the module
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

try:
    from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
except ImportError:
    print("Error: Could not import 'pdd.agentic_change_orchestrator'.")
    print("Ensure your PYTHONPATH is set correctly or the file structure matches.")
    sys.exit(1)


def mock_load_prompt_template(template_name: str) -> str:
    """
    Mock implementation of load_prompt_template.
    Returns a dummy prompt string based on the requested template name.
    """
    return f"MOCK PROMPT FOR: {template_name}\nContext: {{issue_content}}"


def mock_run_agentic_task(instruction: str, cwd: Path, verbose: bool, quiet: bool, label: str, timeout: float = None):
    """
    Mock implementation of run_agentic_task.
    Simulates the output of an LLM agent for each step of the 6-step change workflow.
    """
    step_num = label.replace("step", "")

    # Default return values
    success = True
    cost = 0.20  # Simulated cost per step
    provider = "anthropic"
    output = ""

    if step_num == "1":
        output = "No duplicate issues found. This is a new feature request."
    elif step_num == "2":
        output = "Checked documentation. This feature is not currently implemented."
    elif step_num == "3":
        output = """Dev units identified:
        - prompts/user_service_python.prompt (primary)
        - context/user_service_example.py (needs update)
        - prompts/validation_python.prompt (new)"""
    elif step_num == "4":
        output = """Prompt changes analyzed:
        1. user_service_python.prompt: Add requirement for email validation
        2. validation_python.prompt: Create new module for validation utilities
        3. user_service_example.py: Update to show validation usage"""
    elif step_num == "5":
        output = """FILES_MODIFIED: prompts/user_service_python.prompt, context/user_service_example.py
        FILES_CREATED: prompts/validation_python.prompt
        Changes applied successfully."""
    elif step_num == "6":
        output = "Verification complete. All modified prompts are syntactically valid."
    else:
        output = "Unknown step executed."

    return success, output, cost, provider


def main():
    """Main function to run the agentic change orchestrator simulation."""
    # Define dummy issue data
    issue_data = {
        "issue_url": "https://github.com/example/myapp/issues/239",
        "issue_content": "Add email validation to user registration. Should check format and domain.",
        "repo_owner": "example",
        "repo_name": "myapp",
        "issue_number": 239,
        "issue_author": "feature_requester",
        "issue_title": "Add email validation to user service",
        "cwd": Path("./temp_workspace"),
        "verbose": True,
        "quiet": False
    }

    print("Starting Agentic Change Orchestrator Simulation...")
    print("-" * 60)

    # Patch the internal dependencies
    with patch("pdd.agentic_change_orchestrator.load_prompt_template", side_effect=mock_load_prompt_template), \
         patch("pdd.agentic_change_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task):

        # Run the orchestrator
        success, final_msg, total_cost, model, changed_files = run_agentic_change_orchestrator(
            **issue_data
        )

    print("-" * 60)
    print("Simulation Complete.")
    print(f"Success: {success}")
    print(f"Final Message: {final_msg}")
    print(f"Total Cost: ${total_cost:.2f}")
    print(f"Model Used: {model}")
    print(f"Changed Files: {changed_files}")
    print("\nNext step: Run 'pdd sync' on modified prompts to regenerate code.")


if __name__ == "__main__":
    main()
