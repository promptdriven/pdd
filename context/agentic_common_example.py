# Example usage of pdd/agentic_common.py
# This script demonstrates how to use the main functions from the agentic_common module.
# Assumes the module is installed or the path is correctly set.
# Run this script from a directory where you have write permissions for logs and temp files.

import os
import sys
from pathlib import Path
from typing import Dict
from rich.console import Console

# Add the parent directory to sys.path to import the module (adjust if needed)
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.agentic_common import (
    get_agent_provider_preference,
    get_available_agents,
    run_agentic_task,
    post_step_comment,
    github_save_state,
    github_load_state,
    validate_cached_state
)

console = Console()

def example_get_preferences_and_available():
    console.print("[bold blue]--- Example: Get Provider Preferences and Available Agents ---[/bold blue]")
    
    preferences = get_agent_provider_preference()
    console.print(f"Provider Preferences: {preferences}")
    
    available = get_available_agents()
    console.print(f"Available Agents: {available}\n")

def example_run_agentic_task():
    console.print("[bold blue]--- Example: Run Agentic Task ---[/bold blue]")
    
    instruction = "List the files in the current directory."
    cwd = Path.cwd()
    
    success, output, cost, provider = run_agentic_task(
        instruction=instruction,
        cwd=cwd,
        verbose=True,
        max_retries=2,
        use_playwright=False
    )
    
    if success:
        console.print(f"[green]Success![/green] Provider: {provider}, Cost: ${cost:.4f}")
        console.print(f"Output: {output[:200]}...")  # Truncated for brevity
    else:
        console.print(f"[red]Failed:[/red] {output}\n")

def example_post_step_comment():
    console.print("[bold blue]--- Example: Post Step Comment (requires gh CLI and permissions) ---[/bold blue]")
    
    # Replace with actual values for testing
    repo_owner = "your-org"
    repo_name = "your-repo"
    issue_number = 1
    step_num = 1
    total_steps = 5
    description = "Test step"
    output = "Test output"
    cwd = Path.cwd()
    
    posted = post_step_comment(
        repo_owner=repo_owner,
        repo_name=repo_name,
        issue_number=issue_number,
        step_num=step_num,
        total_steps=total_steps,
        description=description,
        output=output,
        cwd=cwd
    )
    
    console.print(f"Comment posted: {posted}\n")

def example_github_state_management():
    console.print("[bold blue]--- Example: GitHub State Management (requires gh CLI and permissions) ---[/bold blue]")
    
    # Replace with actual values
    repo_owner = "your-org"
    repo_name = "your-repo"
    issue_number = 1
    workflow_type = "test_workflow"
    cwd = Path.cwd()
    
    state: Dict = {"key": "value", "progress": 50}
    
    comment_id = github_save_state(
        repo_owner=repo_owner,
        repo_name=repo_name,
        issue_number=issue_number,
        workflow_type=workflow_type,
        state=state,
        cwd=cwd
    )
    console.print(f"State saved with comment ID: {comment_id}")
    
    loaded_state, loaded_id = github_load_state(
        repo_owner=repo_owner,
        repo_name=repo_name,
        issue_number=issue_number,
        workflow_type=workflow_type,
        cwd=cwd
    )
    console.print(f"Loaded State: {loaded_state}, Comment ID: {loaded_id}\n")

def example_validate_cached_state():
    console.print("[bold blue]--- Example: Validate Cached State ---[/bold blue]")
    
    last_completed = 3.0
    step_outputs = {
        "1": "Success output",
        "2": "Another success",
        "3": "FAILED: Error message",
        "4": "Not reached"
    }
    step_order = [1, 2, 3, 4]
    
    corrected = validate_cached_state(
        last_completed_step=last_completed,
        step_outputs=step_outputs,
        step_order=step_order,
        quiet=False
    )
    
    console.print(f"Original last completed: {last_completed}")
    console.print(f"Corrected last completed: {corrected}\n")

if __name__ == "__main__":
    example_get_preferences_and_available()
    example_run_agentic_task()
    # Uncomment the following if you have GitHub setup and permissions:
    # example_post_step_comment()
    # example_github_state_management()
    example_validate_cached_state()