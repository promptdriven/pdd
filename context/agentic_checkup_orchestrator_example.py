import os
import sys
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator


def main() -> None:
    """
    Example showing how to run the agentic checkup orchestrator.
    
    The orchestrator manages an 8-step workflow (discover, deps, build, 
    interfaces, test, fix, verify, create_pr) and supports both issue-driven 
    and PR-driven verification modes.
    """
    # We require a GitHub token to proceed (even in this mocked example, 
    # to show realistic usage).
    github_token = os.environ.get("GITHUB_TOKEN")
    if not github_token:
        print("GITHUB_TOKEN not set. Set it to run this example.")
        sys.exit(0)

    # Setup a dummy output directory representing our project root
    cwd = Path("./output/dummy_project")
    cwd.mkdir(parents=True, exist_ok=True)
    
    # In a real scenario, these would be fetched from GitHub or local config
    issue_url = "https://github.com/example-owner/example-repo/issues/1"
    issue_content = "The application crashes when processing null inputs."
    repo_owner = "example-owner"
    repo_name = "example-repo"
    issue_number = 1
    issue_title = "Crash on null input"
    architecture_json = "{ 'components': [] }"
    pddrc_content = ""
    
    print("Starting agentic checkup orchestrator (mocked execution)...")
    
    # We mock out the actual LLM step execution and git worktree creation 
    # so this example can run without hitting APIs or modifying real git repos.
    with patch("pdd.agentic_checkup_orchestrator._run_single_step") as mock_step, \
         patch("pdd.agentic_checkup_orchestrator._setup_worktree") as mock_wt, \
         patch("pdd.agentic_checkup_orchestrator._get_git_root") as mock_gr:
        
        # Mock _run_single_step to simulate success: (success, output, cost, model)
        # Note: Step 7 output must contain 'All Issues Fixed' to break the loop.
        def side_effect_step(step_num, *args, **kwargs):
            if step_num == 7:
                return (True, "{\n'success': true,\n'issue_aligned': true\n}\nAll Issues Fixed", 0.01, "mock-model")
            return (True, f"Step {step_num} completed successfully.", 0.01, "mock-model")
            
        mock_step.side_effect = side_effect_step
        
        # Mock git operations
        mock_gr.return_value = cwd
        mock_wt.return_value = (cwd / ".pdd/worktrees/checkup-issue-1", None)
        
        success, message, total_cost, model = run_agentic_checkup_orchestrator(
            issue_url=issue_url,
            issue_content=issue_content,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_title=issue_title,
            architecture_json=architecture_json,
            pddrc_content=pddrc_content,
            cwd=cwd,
            verbose=False,
            quiet=False,
            no_fix=False,
            use_github_state=False,  # Disable actual GH API calls for state
        )
        
    print("\n--- Orchestrator Result ---")
    print(f"Success: {success}")
    print(f"Message: {message}")
    print(f"Total Cost: ${total_cost:.4f}")
    print(f"Final Model: {model}")


if __name__ == "__main__":
    main()