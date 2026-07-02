from __future__ import annotations

import os
import sys
from pathlib import Path
from rich.console import Console

# Dynamically configure the import path to locate 'pdd' relative to this script
script_dir = Path(__file__).resolve().parent
project_root = script_dir.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

console = Console()

def main() -> None:
    """
    Concise example of invoking the agentic checkup orchestrator in non-interactive PR mode.
    
    Parameters of `run_agentic_checkup_orchestrator`:
      - issue_url: URL to the source issue (or empty string/"null" for merit-only PR verification)
      - issue_content: Raw text content describing the target issue
      - repo_owner: Owner of the repository (e.g. "pdd-org")
      - repo_name: Name of the repository (e.g. "pdd-core")
      - issue_number: Number of the issue or PR (used for state-comment threads)
      - issue_title: Headline of the issue
      - architecture_json: Serialized structural metadata of the project modules
      - pddrc_content: Raw text content of the project configuration (.pddrc)
      
      Keyword-Only Parameters:
        - cwd: Path to the local repository checkout root (Path)
        - verbose: Enable detailed execution logs (bool)
        - quiet: Disable standard output logs (bool)
        - no_fix: Run in analysis/verification mode only (no automatic git commits/pushes) (bool)
        - timeout_adder: Extra time in seconds to add to per-step ceilings (float)
        - use_github_state: Persist workflow checkpoint markers as GitHub issue comments (bool)
        - reasoning_time: Optional reasoning model budget setting (float)
        - pr_url: URL of the associated Pull Request (str)
        - pr_owner: Repository owner of the PR branch (str)
        - pr_repo: Repository name of the PR branch (str)
        - pr_number: Number of the Pull Request (int)
        - test_scope: Testing depth limit ("full" or "targeted") (str)
        - start_step_override: Force workflow entry at a specific step (float/int)
        
    Returns:
      - Tuple[bool, str, float, str]:
        1. success (bool): True if the code successfully verified or was repaired cleanly.
        2. message (str): Explanation of the terminal status or gate outcome.
        3. total_cost (float): Total cumulative cost of downstream LLM API invocations (in USD).
        4. model_used (str): Name of the highest-order model utilized in the run.
    """
    console.print("[bold blue]--- Running Agentic Checkup Orchestrator Example ---")

    # Guard against missing essential environment variables (e.g., GitHub tokens or LLM credentials)
    github_token = os.environ.get("GITHUB_TOKEN")
    if not github_token:
        console.print("[yellow]GITHUB_TOKEN environment variable is not set. Real API calls will fail.[/yellow]")
        console.print("Set GITHUB_TOKEN to execute this orchestrator against real repository targets. Exiting gracefully.")
        sys.exit(0)

    # Setup mock input variables and mock workspace in './output'
    workspace_dir = Path("./output/example-sandbox")
    workspace_dir.mkdir(parents=True, exist_ok=True)

    # Initialize a dummy git repository in the workspace to satisfy git repository checking
    import subprocess
    try:
        subprocess.run(["git", "init"], cwd=workspace_dir, capture_output=True, check=True)
        subprocess.run(["git", "config", "user.name", "pdd-bot"], cwd=workspace_dir, capture_output=True, check=True)
        subprocess.run(["git", "config", "user.email", "bot@promptdriven.dev"], cwd=workspace_dir, capture_output=True, check=True)
        # Write a placeholder file to commit
        (workspace_dir / "README.md").write_text("# Example Sandbox Project\n", encoding="utf-8")
        subprocess.run(["git", "add", "README.md"], cwd=workspace_dir, capture_output=True, check=True)
        subprocess.run(["git", "commit", "-m", "initial commit"], cwd=workspace_dir, capture_output=True, check=True)
    except (subprocess.SubprocessError, FileNotFoundError) as e:
        console.print(f"[red]Could not initialize mock git repository: {e}[/red]")
        sys.exit(0)

    # Formulate mock architecture and configurations
    architecture_json = "{\"modules\": {\"core\": {\"path\": \"src/core.py\"}}}"
    pddrc_content = "[pdd]\ntest_command = \"python -m pytest\""

    # Trigger the checkup pipeline
    # Using --no-fix and local-only settings for safe demonstration
    success, final_message, cost, model = run_agentic_checkup_orchestrator(
        issue_url="",
        issue_content="Verify module boundaries and interface compatibility.",
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=42,
        issue_title="Verify API Interfaces",
        architecture_json=architecture_json,
        pddrc_content=pddrc_content,
        cwd=workspace_dir,
        verbose=True,
        quiet=False,
        no_fix=True,  # Run validation without writing back or creating PRs
        use_github_state=False,  # Local workflow files state tracking only
        test_scope="targeted",
        start_step_override=1,  # Begin immediately at Step 1 (Discovery)
    )

    console.print("\n[bold green]--- Orchestration Completed ---")
    console.print(f"Success Status: [bold]{success}[/bold]")
    console.print(f"Final Outcome Message: {final_message}")
    console.print(f"Downstream API Cost: ${cost:.6f} USD")
    console.print(f"Primary LLM Model Used: [blue]{model}[/bold]")

if __name__ == "__main__":
    main()