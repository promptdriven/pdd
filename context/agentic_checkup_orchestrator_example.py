import os
import sys
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

def main() -> None:
    """
    Example demonstrating how to invoke the agentic checkup orchestrator.
    
    This function coordinates an 8-step workflow to analyze, fix, and verify
    issues in a repository. In this example, we mock the internal inner loop
    so it runs quickly without making actual network calls or git modifications.
    """
    # Prepare a dummy working directory
    cwd = Path("./output/dummy_project")
    cwd.mkdir(parents=True, exist_ok=True)
    
    # Setup example inputs for an issue-driven checkup
    issue_url = "https://github.com/example/repo/issues/1"
    issue_content = "The system crashes when clicking the submit button."
    repo_owner = "example"
    repo_name = "repo"
    issue_number = 1
    issue_title = "Crash on submit"
    architecture_json = "{\"description\": \"Dummy architecture\"}"
    pddrc_content = "# Dummy config"
    
    print("--- Invoking run_agentic_checkup_orchestrator ---")
    
    # Mock the internal orchestrator loop to avoid actual LLM and Git calls
    with patch("pdd.agentic_checkup_orchestrator._run_agentic_checkup_orchestrator_inner") as mock_inner:
        # The orchestrator returns a tuple: (success: bool, final_message: str, total_cost: float, model_used: str)
        mock_inner.return_value = (True, "Checkup complete", 0.1234, "gpt-4o")
        
        success, message, cost, model = run_agentic_checkup_orchestrator(
            issue_url=issue_url,
            issue_content=issue_content,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_title=issue_title,
            architecture_json=architecture_json,
            pddrc_content=pddrc_content,
            cwd=cwd,
            verbose=True,
            quiet=False,
            no_fix=True,  # Example: Run only analysis and verification (skip fixer steps)
            test_scope="full"
        )
        
        print(f"Success: {success}")
        print(f"Message: {message}")
        print(f"Cost: ${cost:.4f}")
        print(f"Model: {model}")

if __name__ == "__main__":
    main()