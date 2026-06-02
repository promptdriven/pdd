import os
import sys
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

def main() -> None:
    """
    Demonstrates how to invoke the multi-step agentic checkup orchestrator.
    
    The orchestrator manages an 8-step workflow (Discover, Deps, Build, Interfaces, 
    Test, Fix, Verify, Create PR) to automatically resolve issues or verify PRs.
    
    Here, we mock the internal inner orchestrator to prevent actual LLM API calls 
    and git worktree mutations during the example.
    """
    github_token = os.environ.get("GITHUB_TOKEN")
    if not github_token:
        print("GITHUB_TOKEN not set. Set it to run this example.")
        sys.exit(0)

    # Setup a dummy working directory for the repository
    cwd = Path("./output/dummy_checkup_repo")
    cwd.mkdir(parents=True, exist_ok=True)
    
    # In a real scenario, this would run the full LLM and git pipeline.
    # We patch the inner orchestrator to return a simulated success result.
    with patch("pdd.agentic_checkup_orchestrator._run_agentic_checkup_orchestrator_inner") as mock_inner:
        mock_inner.return_value = (True, "Checkup complete (mocked)", 0.15, "claude-3.5-sonnet")
        
        success, message, cost, model = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/example-owner/example-repo/issues/42",
            issue_content="The build fails with a syntax error in main.py.",
            repo_owner="example-owner",
            repo_name="example-repo",
            issue_number=42,
            issue_title="Syntax error in main.py",
            architecture_json="{}",
            pddrc_content="",
            cwd=cwd,
            verbose=True,
            quiet=False,
            no_fix=True,           # Run analysis and verification only (skip fixer steps)
            use_github_state=False # Do not interact with GitHub issues for state persistence
        )
        
        print("--- Orchestrator Result ---")
        print(f"Success: {success}")
        print(f"Message: {message}")
        print(f"Total Cost: ${cost:.4f}")
        print(f"Model Used: {model}")

if __name__ == "__main__":
    main()