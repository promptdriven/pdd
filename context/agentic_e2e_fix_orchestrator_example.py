from __future__ import annotations

import os
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

# Add the project root to sys.path to allow importing the pdd package
# This assumes the example script is located relative to the package root
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from rich.console import Console

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

console = Console()


def main() -> None:
    """
    Demonstrates how to use the agentic_e2e_fix_orchestrator module to:
    1. Set up a temporary working directory (simulating a repo).
    2. Provide example GitHub issue details.
    3. Run the E2E fix orchestrator with default parameters.
    4. Print the results including success status, message, cost, model, and changed files.

    Note: In a real scenario, use an actual repository path for cwd, and valid GitHub details.
          This example uses dummies and a temp dir to avoid side effects.
    """

    # 1. Set up a temporary directory as cwd (agent's working directory)
    with TemporaryDirectory() as temp_dir:
        cwd = Path(temp_dir)
        console.print(f"[blue]Using temporary cwd: {cwd}[/blue]")

        # 2. Example GitHub issue details (replace with real values)
        issue_url = "https://github.com/example-owner/example-repo/issues/123"
        issue_content = "Example issue content describing an E2E test failure."
        repo_owner = "example-owner"
        repo_name = "example-repo"
        issue_number = 123
        issue_author = "example-author"
        issue_title = "Example Issue Title"

        # 3. Run the orchestrator
        # Parameters:
        # - issue_url: Full URL of the GitHub issue.
        # - issue_content: Body text of the issue.
        # - repo_owner: GitHub username or organization.
        # - repo_name: Repository name.
        # - issue_number: Issue number.
        # - issue_author: GitHub username of the issue author.
        # - issue_title: Title of the issue.
        # - cwd: Path to the working directory (repo root).
        # - timeout_adder: Additional seconds to add to step timeouts (default 0.0).
        # - max_cycles: Maximum fix cycles (default 5).
        # - resume: Resume from saved state if available (default True).
        # - verbose: Show detailed output (default False).
        # - quiet: Suppress non-error output (default False).
        # - use_github_state: Use GitHub for state persistence (default True).
        # - protect_tests: Protect existing tests from changes (default False).
        success, final_message, total_cost, model_used, changed_files = run_agentic_e2e_fix_orchestrator(
            issue_url=issue_url,
            issue_content=issue_content,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_author=issue_author,
            issue_title=issue_title,
            cwd=cwd,
            timeout_adder=0.0,
            max_cycles=1,  # Limit to 1 cycle for demo (real use: 5+)
            resume=False,  # Start fresh for demo
            verbose=True,
            quiet=False,
            use_github_state=False,  # Disable GitHub for demo (requires auth)
            protect_tests=True,
        )

        # 4. Print results
        # Returns:
        # - success: bool - True if all tests passed after fixes.
        # - final_message: str - Summary message (e.g., "All tests passed" or failure reason).
        # - total_cost: float - Estimated total cost in USD.
        # - model_used: str - LLM model used (e.g., "claude-3-sonnet").
        # - changed_files: List[str] - Paths of files modified during the workflow.
        console.print("\n[bold]Results:[/bold]")
        console.print(f"Success: {success}")
        console.print(f"Final Message: {final_message}")
        console.print(f"Total Cost: ${total_cost:.4f}")
        console.print(f"Model Used: {model_used}")
        console.print(f"Changed Files: {changed_files}")


if __name__ == "__main__":
    main()