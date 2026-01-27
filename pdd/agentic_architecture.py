"""
CLI entry point for the agentic architecture workflow.
Detects GitHub issue URLs, fetches issue content and comments via `gh api`,
ensures repository context is available, then invokes the orchestrator.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
from pathlib import Path
from typing import List, Optional, Tuple

from rich.console import Console

# Internal imports
from .agentic_architecture_orchestrator import run_agentic_architecture_orchestrator

console = Console()


def _is_github_issue_url(url: str) -> bool:
    """
    Detect if the string is a valid GitHub issue URL.
    
    Args:
        url: The URL string to check.
        
    Returns:
        True if the URL matches the GitHub issue pattern, False otherwise.
    """
    return _parse_github_url(url) is not None


def _parse_github_url(url: str) -> Optional[Tuple[str, str, int]]:
    """
    Extract owner, repo, and issue number from a GitHub URL.
    
    Supports:
      - https://github.com/{owner}/{repo}/issues/{number}
      - https://www.github.com/{owner}/{repo}/issues/{number}
      - github.com/{owner}/{repo}/issues/{number}
      
    Args:
        url: The URL string to parse.
        
    Returns:
        Tuple of (owner, repo, issue_number) if successful, None otherwise.
    """
    pattern = r"(?:https?://)?(?:www\.)?github\.com/([^/]+)/([^/]+)/issues/(\d+)"
    match = re.search(pattern, url)
    if match:
        owner, repo, number = match.groups()
        return owner, repo, int(number)
    return None


def _check_gh_cli() -> bool:
    """Check if gh CLI tool is available on the PATH."""
    return shutil.which("gh") is not None


def _run_gh_command(args: List[str]) -> Tuple[bool, str]:
    """
    Run a gh command and return (success, stdout/stderr).
    
    Args:
        args: List of arguments to pass to the gh command.
        
    Returns:
        Tuple of (success boolean, output string).
    """
    try:
        result = subprocess.run(
            ["gh"] + args,
            capture_output=True,
            text=True,
            check=True
        )
        return True, result.stdout
    except subprocess.CalledProcessError as e:
        return False, e.stderr or str(e)
    except FileNotFoundError:
        return False, "gh CLI not found"


def _ensure_repo_context(owner: str, repo: str, current_cwd: Path, quiet: bool) -> Tuple[Path, Optional[str]]:
    """
    Ensure the repository is available locally.
    
    Logic:
    1. If current_cwd is inside the target repo (checked via remote), use it.
    2. If current_cwd is a git repo but mismatch, warn and use it (user might be in a fork).
    3. If current_cwd is NOT a git repo:
       a. Check if subdirectory {repo} exists and is a git repo -> use it.
       b. Clone {owner}/{repo} -> use it.
       
    Args:
        owner: Repository owner.
        repo: Repository name.
        current_cwd: Current working directory.
        quiet: Whether to suppress non-error output.
        
    Returns:
        Tuple of (path to repo root, error message if any).
    """
    
    def get_remote_url(path: Path) -> Optional[str]:
        try:
            res = subprocess.run(
                ["git", "config", "--get", "remote.origin.url"],
                cwd=path, capture_output=True, text=True
            )
            if res.returncode == 0:
                return res.stdout.strip()
        except Exception:
            pass
        return None

    # Case 1 & 2: Already in a git repo
    remote = get_remote_url(current_cwd)
    if remote:
        # Simple check if owner/repo is in the remote URL
        # Remotes can be git@github.com:owner/repo.git or https://github.com/owner/repo.git
        if f"{owner}/{repo}" in remote or f"{owner}/{repo}.git" in remote:
            return current_cwd, None
        
        # Mismatch
        if not quiet:
            console.print(f"[yellow]Warning: Current directory is a git repo but remote '{remote}' does not match '{owner}/{repo}'. Proceeding in current directory.[/yellow]")
        return current_cwd, None

    # Case 3: Not in a git repo
    target_dir = current_cwd / repo
    
    # 3a: Subdirectory exists
    if target_dir.exists() and target_dir.is_dir():
        if (target_dir / ".git").exists():
            if not quiet:
                console.print(f"[blue]Found existing repository at {target_dir}[/blue]")
            return target_dir, None
        else:
            return current_cwd, f"Directory '{repo}' exists but is not a git repository."

    # 3b: Clone
    if not quiet:
        console.print(f"[blue]Cloning {owner}/{repo} into {target_dir}...[/blue]")
    
    try:
        subprocess.run(
            ["gh", "repo", "clone", f"{owner}/{repo}"],
            cwd=current_cwd,
            check=True,
            capture_output=True,
            text=True
        )
        return target_dir, None
    except subprocess.CalledProcessError as e:
        err_msg = e.stderr if e.stderr else str(e)
        return current_cwd, f"Failed to clone repository: {err_msg}"


def run_agentic_architecture(
    issue_url: str,
    *,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    skip_prompts: bool = False
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Entry point for the agentic architecture workflow.

    1. Validates the GitHub issue URL.
    2. Fetches issue details and comments using `gh` CLI.
    3. Ensures the repository is available locally (clones if necessary).
    4. Invokes the architecture orchestrator.

    Args:
        issue_url: Full URL to the GitHub issue.
        verbose: Enable verbose logging.
        quiet: Suppress non-error output.
        timeout_adder: Additional seconds to add to step timeouts.
        use_github_state: Whether to persist state to GitHub comments.
        skip_prompts: If True, skip Step 9 (prompt generation). Default False (prompts ARE generated).

    Returns:
        Tuple containing:
        - success (bool): Whether the workflow completed successfully.
        - message (str): Final status message or error description.
        - total_cost (float): Total estimated cost of LLM calls.
        - model_used (str): The model used for the last step.
        - output_files (List[str]): List of files generated/modified.
    """
    cwd = Path.cwd()

    # 1. Check gh CLI
    if not _check_gh_cli():
        return False, "gh CLI not found. Please install GitHub CLI.", 0.0, "", []

    # 2. Parse URL
    parsed = _parse_github_url(issue_url)
    if not parsed:
        return False, f"Invalid GitHub URL: {issue_url}", 0.0, "", []
    
    owner, repo, issue_number = parsed

    if not quiet:
        console.print(f"[bold blue]Fetching issue #{issue_number} from {owner}/{repo}...[/bold blue]")

    # 3. Fetch Issue Data
    # gh api repos/{owner}/{repo}/issues/{number}
    success, output = _run_gh_command(["api", f"repos/{owner}/{repo}/issues/{issue_number}"])
    if not success:
        return False, f"Issue not found: {output}", 0.0, "", []
    
    try:
        issue_data = json.loads(output)
    except json.JSONDecodeError:
        return False, "Failed to parse GitHub API response", 0.0, "", []

    issue_title = issue_data.get("title", "")
    issue_body = issue_data.get("body", "") or ""
    issue_author = issue_data.get("user", {}).get("login", "unknown")
    comments_url = issue_data.get("comments_url", "")

    # 4. Fetch Comments
    comments_text = ""
    if comments_url:
        c_success, c_output = _run_gh_command(["api", comments_url])
        if c_success:
            try:
                comments = json.loads(c_output)
                if isinstance(comments, list) and comments:
                    formatted_comments = []
                    for c in comments:
                        user = c.get("user", {}).get("login", "unknown")
                        body = c.get("body", "")
                        formatted_comments.append(f"User: {user}\n{body}")
                    comments_text = "\n\n--- Comments ---\n" + "\n\n".join(formatted_comments)
            except json.JSONDecodeError:
                if verbose:
                    console.print("[yellow]Warning: Failed to parse comments JSON[/yellow]")

    full_issue_content = f"{issue_body}{comments_text}"

    # 5. Ensure Repo Context
    repo_path, error = _ensure_repo_context(owner, repo, cwd, quiet)
    if error:
        return False, error, 0.0, "", []

    # 6. Invoke Orchestrator
    return run_agentic_architecture_orchestrator(
        issue_url=issue_url,
        issue_content=full_issue_content,
        repo_owner=owner,
        repo_name=repo,
        issue_number=issue_number,
        issue_author=issue_author,
        issue_title=issue_title,
        cwd=repo_path,
        verbose=verbose,
        quiet=quiet,
        timeout_adder=timeout_adder,
        use_github_state=use_github_state,
        skip_prompts=skip_prompts
    )