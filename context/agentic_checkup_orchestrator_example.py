import os
import sys
from pathlib import Path
from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

def main() -> None:
    """
    Example showing how to run the agentic checkup orchestrator.
    
    The orchestrator runs an 8-step iterative loop to discover, test, fix, and 
    verify code against an issue. It can optionally operate in PR-verification mode.
    
    Inputs to the orchestrator include:
      - issue_url, issue_content, repo_owner, repo_name, issue_number, issue_title (GitHub context)
      - architecture_json, pddrc_content (Project context strings)
      - cwd: Path to the local git repository root
      - no_fix: bool indicating whether to skip fixing and just verify (--no-fix)
      - PR context (optional): pr_url, pr_owner, pr_repo, pr_number
      
    Returns:
      Tuple[bool, str, float, str]: 
        - success: Whether the checkup completed and passed the gate
        - message: Final status message
        - total_cost: Accumulated LLM cost in USD
        - model_used: The primary LLM model used
    """
    # Check for required API keys if running real LLM tasks
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    # Setup a dummy project directory
    output_dir = Path("./output/dummy_project")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Initialize a bare minimum git repo for the orchestrator to inspect
    os.system(f"cd {output_dir} && git init && touch README.md && git add README.md && git commit -m 'Initial commit'")

    # Example inputs
    issue_url = "https://github.com/example/repo/issues/123"
    issue_content = "The application crashes when processing null inputs."
    repo_owner = "example"
    repo_name = "repo"
    issue_number = 123
    issue_title = "Crash on null input"
    architecture_json = "{}"
    pddrc_content = ""

    print("Starting checkup orchestrator (--no-fix mode for safety in example)...")
    
    # Run the orchestrator
    # We use no_fix=True so it only performs discovery and testing, avoiding git commits/pushes
    success, message, cost, model = run_agentic_checkup_orchestrator(
        issue_url=issue_url,
        issue_content=issue_content,
        repo_owner=repo_owner,
        repo_name=repo_name,
        issue_number=issue_number,
        issue_title=issue_title,
        architecture_json=architecture_json,
        pddrc_content=pddrc_content,
        cwd=output_dir,
        verbose=True,
        quiet=False,
        no_fix=True,
        use_github_state=False  # Do not attempt to read/write state to GitHub comments
    )

    print("\n--- Orchestrator Result ---")
    print(f"Success: {success}")
    print(f"Message: {message}")
    print(f"Total Cost: ${cost:.4f}")
    print(f"Model Used: {model}")

if __name__ == "__main__":
    main()