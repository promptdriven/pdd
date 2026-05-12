import os
import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure output directory exists
output_dir = Path("./output/test_repo")
output_dir.mkdir(parents=True, exist_ok=True)

# Import the target function from the module
from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

def main():
    """
    Example showing how to use `run_agentic_bug_orchestrator`.
    
    This function orchestrates a 12-step agentic bug investigation workflow.
    It relies on a Git repository and LLM providers. In this example, we mock
    the LLM tasks and state/git helpers so it can run standalone without API keys.
    """
    print("Starting mock run of run_agentic_bug_orchestrator...")
    
    # Dummy issue details
    issue_url = "https://github.com/example/repo/issues/123"
    issue_content = "Bug: The calculator adds numbers incorrectly when using floats."
    repo_owner = "example"
    repo_name = "repo"
    issue_number = 123
    issue_author = "user1"
    issue_title = "Float addition bug"
    cwd = output_dir.resolve()

    # We mock out LLM tasks and Git/GitHub interactions to allow the orchestrator 
    # to run fully through its steps in this non-interactive example.
    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run_task, \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_setup_worktree, \
         patch("pdd.agentic_bug_orchestrator._maybe_post_step_comment") as mock_post_comment:
         
        # Mock LLM calls to always return success with some dummy output
        mock_run_task.return_value = (True, "Mocked task output", 0.05, "mock_model")
        
        # Mock state to start fresh
        mock_load_state.return_value = (None, None)
        mock_save_state.return_value = "mock_comment_id"
        mock_post_comment.return_value = "mock_comment_id"
        
        # Mock git worktree creation to just use the current directory
        mock_setup_worktree.return_value = (cwd, None)

        # Execute the orchestrator
        success, final_message, total_cost, model_used, changed_files = run_agentic_bug_orchestrator(
            issue_url=issue_url,
            issue_content=issue_content,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_author=issue_author,
            issue_title=issue_title,
            cwd=cwd,
            verbose=False,
            quiet=True,         # Set to True to reduce console spam
            use_github_state=False # Don't try to fetch remote GH state
        )

    print("\n--- Investigation Results ---")
    print(f"Success        : {success}")
    print(f"Total Cost     : ${total_cost:.4f}")
    print(f"Model Used     : {model_used}")
    print(f"Changed Files  : {changed_files}")
    print(f"Final Message  : {final_message}")

if __name__ == "__main__":
    main()