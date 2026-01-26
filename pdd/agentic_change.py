from __future__ import annotations

import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import List, Tuple, Optional, Any

from rich.console import Console

# Internal imports
from .agentic_change_orchestrator import run_agentic_change_orchestrator

console = Console()


def _escape_format_braces(text: str) -> str:
    """
    Escape curly braces in text to prevent Python's .format() from
    interpreting them as placeholders. { becomes {{ and } becomes }}.
    """
    return text.replace("{", "{{").replace("}", "}}")


def _check_gh_cli() -> bool:
    """
    Check if the GitHub CLI (gh) is installed and available in the system PATH.
    """
    return shutil.which("gh") is not None


def _parse_issue_url(url: str) -> Optional[Tuple[str, str, int]]:
    """
    Parse a GitHub issue URL to extract the owner, repository name, and issue number.

    Supported formats:
    - https://github.com/{owner}/{repo}/issues/{number}
    - https://www.github.com/{owner}/{repo}/issues/{number}
    - github.com/{owner}/{repo}/issues/{number}

    Returns:
        Tuple of (owner, repo, issue_number) if successful, else None.
    """
    pattern = r"(?:https?://)?(?:www\.)?github\.com/([^/]+)/([^/]+)/issues/(\d+)"
    match = re.search(pattern, url)
    if match:
        return match.group(1), match.group(2), int(match.group(3))
    return None


def _run_gh_command(args: List[str]) -> Tuple[bool, str]:
    """
    Execute a gh CLI command.

    Args:
        args: List of arguments to pass to `gh`.

    Returns:
        Tuple of (success, output). Output is stdout on success, stderr on failure.
    """
    try:
        result = subprocess.run(
            ["gh"] + args,
            capture_output=True,
            text=True,
            check=False
        )
        if result.returncode != 0:
            return False, result.stderr.strip()
        return True, result.stdout.strip()
    except Exception as e:
        return False, str(e)


def _setup_repository(owner: str, repo: str, quiet: bool) -> Path:
    """
    Prepare the working directory for the agent.

    Logic:
    1. If the current directory is the target repository, use it.
    2. Otherwise, clone the repository into a temporary directory.

    Returns:
        Path to the working directory.
    """
    # Check if current directory is the repo
    try:
        if (Path.cwd() / ".git").exists():
            # Get remote origin URL
            res = subprocess.run(
                ["git", "remote", "get-url", "origin"],
                capture_output=True,
                text=True
            )
            if res.returncode == 0:
                remote_url = res.stdout.strip()
                # Check if owner/repo is in the remote URL
                # Matches formats like:
                # - https://github.com/owner/repo.git
                # - git@github.com:owner/repo.git
                if f"{owner}/{repo}" in remote_url:
                    if not quiet:
                        console.print(f"[blue]Using current directory as repository: {Path.cwd()}[/blue]")
                    return Path.cwd()
    except Exception:
        # If git check fails, proceed to clone
        pass

    # Clone to a temporary directory
    temp_dir = Path(tempfile.mkdtemp(prefix=f"pdd_{repo}_"))
    if not quiet:
        console.print(f"[blue]Cloning {owner}/{repo} to temporary directory: {temp_dir}[/blue]")

    # Use gh repo clone to handle authentication automatically
    clone_cmd = ["repo", "clone", f"{owner}/{repo}", "."]
    
    # We run this in the temp_dir
    try:
        result = subprocess.run(
            ["gh"] + clone_cmd,
            cwd=temp_dir,
            capture_output=True,
            text=True,
            check=False
        )
        if result.returncode != 0:
            raise RuntimeError(f"Failed to clone repository: {result.stderr.strip()}")
    except Exception as e:
        raise RuntimeError(f"Failed to execute clone command: {e}")

    return temp_dir


def run_agentic_change(
    issue_url: str,
    *,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True
) -> Tuple[bool, str, float, str, List[str]]:
    """
    CLI entry point for the agentic change workflow.

    Fetches issue details and comments from GitHub, sets up the repository,
    and invokes the orchestrator to perform the 12-step change process.

    Args:
        issue_url: The full URL of the GitHub issue.
        verbose: If True, enables detailed logging.
        quiet: If True, suppresses standard output.
        timeout_adder: Additional time to add to step timeouts.
        use_github_state: If True, persists state to GitHub comments.

    Returns:
        Tuple containing:
        - success (bool)
        - message (str)
        - total_cost (float)
        - model_used (str)
        - changed_files (List[str])
    """
    # 1. Check dependencies
    if not _check_gh_cli():
        return False, "gh CLI not found", 0.0, "", []

    # 2. Parse URL
    parsed = _parse_issue_url(issue_url)
    if not parsed:
        return False, "Invalid GitHub URL", 0.0, "", []
    
    owner, repo, issue_number = parsed

    if not quiet:
        console.print(f"[bold]Fetching issue #{issue_number} from {owner}/{repo}...[/bold]")

    # 3. Fetch Issue Content
    success, issue_json = _run_gh_command(["api", f"repos/{owner}/{repo}/issues/{issue_number}"])
    if not success:
        return False, f"Issue not found: {issue_json}", 0.0, "", []

    try:
        issue_data = json.loads(issue_json)
    except json.JSONDecodeError:
        return False, "Failed to parse issue JSON", 0.0, "", []

    # Extract metadata
    title = issue_data.get("title", "")
    body = issue_data.get("body", "") or ""
    author = issue_data.get("user", {}).get("login", "unknown")
    comments_url = issue_data.get("comments_url", "")

    # 4. Fetch Comments
    comments_data = []
    if comments_url:
        success, comments_json = _run_gh_command(["api", comments_url])
        if success:
            try:
                comments_data = json.loads(comments_json)
            except json.JSONDecodeError:
                if verbose:
                    console.print("[yellow]Warning: Failed to parse comments JSON[/yellow]")

    # 5. Construct Full Context
    issue_content = f"Title: {title}\n\nDescription:\n{body}\n"
    if comments_data and isinstance(comments_data, list):
        issue_content += "\nComments:\n"
        for comment in comments_data:
            if isinstance(comment, dict):
                c_user = comment.get("user", {}).get("login", "unknown")
                c_body = comment.get("body", "")
                issue_content += f"\n--- Comment by {c_user} ---\n{c_body}\n"

    # Escape curly braces to prevent .format() errors when issue contains code
    issue_content = _escape_format_braces(issue_content)

    # 6. Setup Repository (Clone or Use Current)
    try:
        work_dir = _setup_repository(owner, repo, quiet)
    except RuntimeError as e:
        return False, str(e), 0.0, "", []

    # 7. Run Orchestrator
    if not quiet:
        console.print(f"[bold green]Starting Agentic Change Orchestrator...[/bold green]")

    return run_agentic_change_orchestrator(
        issue_url=issue_url,
        issue_content=issue_content,
        repo_owner=owner,
        repo_name=repo,
        issue_number=issue_number,
        issue_author=author,
        issue_title=title,
        cwd=work_dir,
        verbose=verbose,
        quiet=quiet,
        timeout_adder=timeout_adder,
        use_github_state=use_github_state
    )