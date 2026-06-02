import os
import sys
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

def main():
    """
    Example showing how to run the agentic checkup orchestrator.
    We use mock patches here to avoid executing actual Git commands or LLM calls
    during the example, but the signature and usage remain identical for real runs.
    """
    cwd = Path("./output/dummy_project").resolve()
    cwd.mkdir(parents=True, exist_ok=True)

    print("--- Running Agentic Checkup Orchestrator (Issue Mode) ---")
    
    # Mock the inner function to simulate a successful checkup run
    with patch("pdd.agentic_checkup_orchestrator._run_agentic_checkup_orchestrator_inner") as mock_inner:
        mock_inner.return_value = (True, "Checkup complete", 0.05, "gpt-4o")
        
        success, message, cost, model = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/example-owner/example-repo/issues/1",
            issue_content="Fix a bug in the calculation module.",
            repo_owner="example-owner",
            repo_name="example-repo",
            issue_number=1,
            issue_title="Bug in calculation",
            architecture_json="{}",
            pddrc_content="# pdd config",
            cwd=cwd,
            verbose=True,
            quiet=False,
            no_fix=False,
            use_github_state=False,
            test_scope="full"
        )

        print(f"Success: {success}")
        print(f"Message: {message}")
        print(f"Total Cost: ${cost:.4f}")
        print(f"Model Used: {model}")

    print("\n--- Running Agentic Checkup Orchestrator (PR Mode) ---")
    with patch("pdd.agentic_checkup_orchestrator._run_agentic_checkup_orchestrator_inner") as mock_inner:
        mock_inner.return_value = (True, "PR verified and checkup complete", 0.12, "gpt-4o")

        success, message, cost, model = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/example-owner/example-repo/issues/2",
            issue_content="Add feature X",
            repo_owner="example-owner",
            repo_name="example-repo",
            issue_number=2,
            issue_title="Feature X",
            architecture_json="{}",
            pddrc_content="# pdd config",
            cwd=cwd,
            verbose=False,
            quiet=True,
            no_fix=True,           # Just verify, don't push fixes
            use_github_state=False,
            test_scope="targeted", # Run tests related to PR diff
            pr_url="https://github.com/example-owner/example-repo/pull/3",
            pr_owner="example-owner",
            pr_repo="example-repo",
            pr_number=3
        )

        print(f"Success: {success}")
        print(f"Message: {message}")
        print(f"Total Cost: ${cost:.4f}")
        print(f"Model Used: {model}")

if __name__ == "__main__":
    main()