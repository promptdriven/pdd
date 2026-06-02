import os
import sys
from pathlib import Path
from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

def main() -> None:
    """
    Example showing how to run the multi-step agentic checkup orchestrator.
    
    This orchestrator coordinates an 8-step process (discover, dependencies, build, 
    interfaces, test, fix, verify, create PR) to analyze and fix software issues.
    """
    # Ensure we have the necessary API key for the underlying agentic tasks
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    # Setup a dummy working directory for the example
    cwd = Path("./output/dummy_project")
    cwd.mkdir(parents=True, exist_ok=True)
    
    # Initialize a mock git repository so worktree setup doesn't fail immediately
    # Note: In a real scenario, this would be a valid git repository.
    import subprocess
    try:
        subprocess.run(["git", "init"], cwd=cwd, check=True, capture_output=True)
        # Need at least one commit to create a branch/worktree
        (cwd / "README.md").write_text("# Dummy Project")
        subprocess.run(["git", "add", "README.md"], cwd=cwd, check=True, capture_output=True)
        subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=cwd, check=True, capture_output=True)
    except Exception as e:
        print(f"Git init failed (expected in some CI environments without git): {e}")
        print("Skipping full execution as it requires a real git repository.")
        sys.exit(0)

    # Mock inputs for the orchestrator
    issue_url = "https://github.com/example-owner/example-repo/issues/1"
    issue_content = "The tests are failing due to a missing import in main.py."
    repo_owner = "example-owner"
    repo_name = "example-repo"
    issue_number = 1
    issue_title = "Missing import in main.py"
    architecture_json = "{}"  # Empty JSON for this example
    pddrc_content = ""         # Empty config

    print("Starting the agentic checkup orchestrator in --no-fix mode...")
    
    # Run the orchestrator in --no-fix mode (steps 1-5, skip 6, run 7, skip 8)
    # We use --no-fix here to avoid actual LLM-driven edits and PR creation in a dummy environment.
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
        no_fix=True,  # Prevent actual code modification and PR creation
        use_github_state=False,  # Don't try to post to GitHub in this local example
        test_scope="full"  # Run all tests
    )

    print("\n--- Orchestrator Result ---")
    print(f"Success: {success}")
    print(f"Message: {message}")
    print(f"Total Cost: ${cost:.4f}")
    print(f"Model Used: {model}")

if __name__ == "__main__":
    main()