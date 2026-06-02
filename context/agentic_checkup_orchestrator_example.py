import os
import sys
from pathlib import Path
from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator


def main() -> None:
    """
    Example showing how to run the multi-step agentic checkup orchestrator.
    
    The orchestrator runs an 8-step process (discover, deps, build, 
    interfaces, test, fix, verify, create_pr) in an isolated git worktree.
    It supports an iterative fix-verify loop to resolve issues automatically.
    """
    # This example requires a GitHub token and an OpenAI key (or similar)
    # to run the LLM agents and interact with GitHub.
    if not os.environ.get("OPENAI_API_KEY"):
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)
        
    if not os.environ.get("GITHUB_TOKEN"):
        print("GITHUB_TOKEN not set. Set it to run this example.")
        sys.exit(0)

    print("Starting checkup orchestrator (mock run)...")
    
    # In a real scenario, these would be parsed from CLI arguments
    cwd = Path.cwd()
    
    # Run the orchestrator in PR mode (--pr) with no issue specified (--no-issue)
    # This reviews the PR on its own merits without trying to align it to a specific issue.
    # Using quiet=False to see progress.
    
    try:
        success, message, cost, model = run_agentic_checkup_orchestrator(
            issue_url="",              # Empty for PR-only mode
            issue_content="",          # Empty for PR-only mode
            repo_owner="test-owner",
            repo_name="test-repo",
            issue_number=123,          # This becomes the PR number in this mode
            issue_title="",            # Empty for PR-only mode
            architecture_json="{}",
            pddrc_content="",
            cwd=cwd,
            verbose=False,
            quiet=False,
            no_fix=True,               # Run analysis only, skip fixer loop for safety in example
            pr_url="https://github.com/test-owner/test-repo/pull/123",
            pr_owner="test-owner",
            pr_repo="test-repo",
            pr_number=123,
            use_github_state=False     # Avoid making actual GitHub API calls for state
        )
        
        print("\n--- Orchestrator Result ---")
        print(f"Success: {success}")
        print(f"Message: {message}")
        print(f"Cost: ${cost:.4f}")
        print(f"Model: {model}")
    except Exception as e:
        print(f"An error occurred while running the orchestrator: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()