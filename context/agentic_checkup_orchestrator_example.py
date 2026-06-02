import os
import sys
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator


def main() -> None:
    """
    Example showing how to invoke the agentic checkup orchestrator.
    
    The orchestrator runs an 8-step workflow to analyze, fix, and verify
    software issues. It supports both issue-driven fixes and PR-verification
    modes.
    """
    # Ensure we have an output directory for any artifacts
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # We mock the inner orchestrator to prevent actual LLM calls and git 
    # operations during this example execution.
    with patch("pdd.agentic_checkup_orchestrator._run_agentic_checkup_orchestrator_inner") as mock_inner:
        # Configure the mock to return a successful checkup result
        # Returns: (success: bool, message: str, total_cost: float, model_used: str)
        mock_inner.return_value = (
            True,
            "Checkup complete",
            0.05, # Cost in dollars
            "gpt-4o" # Model used
        )
        
        print("Running agentic checkup orchestrator in issue mode...")
        success, message, cost, model = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/example-owner/example-repo/issues/1",
            issue_content="The build fails with a syntax error in main.py.",
            repo_owner="example-owner",
            repo_name="example-repo",
            issue_number=1,
            issue_title="Syntax error in main.py",
            architecture_json="{}",
            pddrc_content="",
            cwd=output_dir,
            verbose=False,
            quiet=False,
            no_fix=False,
            timeout_adder=0.0,
            use_github_state=False,
            start_step_override=1
        )
        
        print(f"Success: {success}")
        print(f"Message: {message}")
        print(f"Total Cost: ${cost:.4f}")
        print(f"Model: {model}")


if __name__ == "__main__":
    main()