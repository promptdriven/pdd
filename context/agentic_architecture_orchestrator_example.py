"""
Example usage of the agentic_architecture_orchestrator module.

This script demonstrates how to invoke the `run_agentic_architecture_orchestrator` function.
Since the orchestrator relies on internal modules like `run_agentic_task` and `load_prompt_template`,
this example mocks those dependencies to simulate a successful architecture generation workflow
without making actual LLM calls or requiring a real GitHub issue.

Scenario:
    We simulate an issue where a user provides a PRD for a new web application.
    The orchestrator will step through the 8-step process plus a validation loop,
    generating architecture.json with proper dependency ordering and priorities.
"""

import sys
import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure the project root is in sys.path so we can import the module
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

try:
    from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator
except ImportError:
    print("Error: Could not import 'pdd.agentic_architecture_orchestrator'.")
    print("Ensure your PYTHONPATH is set correctly or the file structure matches.")
    sys.exit(1)


def mock_load_prompt_template(template_name: str) -> str:
    """
    Mock implementation of load_prompt_template.
    Returns a dummy prompt string based on the requested template name.
    """
    return f"MOCK PROMPT FOR: {template_name}\nContext: {{issue_content}}"


def mock_run_agentic_task(instruction: str, cwd: Path, verbose: bool, quiet: bool, label: str, timeout: float = None, max_retries: int = 3):
    """
    Mock implementation of run_agentic_task.
    Simulates the output of an LLM agent for each step of the 8-step architecture workflow.
    """
    step_part = label.replace("step", "").split("_")[0]
    step_num = step_part

    # Default return values
    success = True
    cost = 0.25  # Simulated cost per step
    provider = "anthropic"
    output = ""

    if step_num == "1":
        output = "PRD Analysis: Web app with user auth, product catalog, and checkout. Tech stack: Next.js, FastAPI, PostgreSQL."
    elif step_num == "2":
        output = "Module boundaries identified: auth, products, cart, checkout, shared models. Tech stack confirmed: Next.js 14, FastAPI, SQLAlchemy, PostgreSQL."
    elif step_num == "3":
        output = "Research complete. Found docs for Next.js App Router, FastAPI dependency injection, SQLAlchemy 2.0 patterns."
    elif step_num == "4":
        output = "Design complete. 6 modules identified with dependency graph. Priority order: models(1), auth(2), products(3), cart(4), checkout(5), frontend(6)."
    elif step_num == "5":
        output = "Dependencies researched. URLs collected: fastapi.tiangolo.com, docs.sqlalchemy.org, nextjs.org/docs."
    elif step_num == "6":
        output = '[{"filename": "models_Python.prompt", "priority": 1, "dependencies": []}, {"filename": "auth_Python.prompt", "priority": 2, "dependencies": ["models_Python.prompt"]}]'
    elif step_num == "7":
        output = "VALID"
    elif step_num == "8":
        output = "Fixed validation errors."
    else:
        output = f"Unknown step executed: {step_num}"

    return success, output, cost, provider


def main():
    """Main function to run the agentic architecture orchestrator simulation."""
    # Create a temporary directory for the simulation
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_cwd = Path(temp_dir)

        # Define dummy issue data
        issue_data = {
            "issue_url": "https://github.com/example/myapp/issues/42",
            "issue_content": "Build an e-commerce platform with user authentication, product catalog, shopping cart, and checkout flow. Use Next.js for frontend and FastAPI for backend with PostgreSQL.",
            "repo_owner": "example",
            "repo_name": "myapp",
            "issue_number": 42,
            "issue_author": "product_owner",
            "issue_title": "PRD: E-commerce Platform MVP",
            "cwd": temp_cwd,
            "verbose": True,
            "quiet": False
        }

        print("Starting Agentic Architecture Orchestrator Simulation...")
        print("-" * 60)

        # Patch the internal dependencies to avoid real API/filesystem operations
        with patch("pdd.agentic_architecture_orchestrator.load_prompt_template", side_effect=mock_load_prompt_template), \
             patch("pdd.agentic_architecture_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_architecture_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_architecture_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_architecture_orchestrator.clear_workflow_state", return_value=None):

            # Run the orchestrator
            success, final_msg, total_cost, model, output_files = run_agentic_architecture_orchestrator(
                **issue_data
            )

        print("-" * 60)
        print("Simulation Complete.")
        print(f"Success: {success}")
        print(f"Final Message: {final_msg}")
        print(f"Total Cost: ${total_cost:.2f}")
        print(f"Model Used: {model}")
        print(f"Output Files: {output_files}")
        print("\nNext step: Run 'pdd generate' on individual module prompts to generate code.")


if __name__ == "__main__":
    main()
