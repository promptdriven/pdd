from __future__ import annotations

"""
Agentic bug investigation entry point.

This module serves as the CLI entry point for the agentic bug investigation workflow.
It parses a GitHub issue URL, fetches the issue content and comments using the `gh` CLI,
sets up a temporary workspace, and invokes the orchestrator to run the investigation.
"""

import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from rich.console import Console

from .agentic_bug_orchestrator import run_agentic_bug_orchestrator
from .agentic_common import get_available_agents

# Optional globals from package root; ignore if not present.
try:  # pragma: no cover - purely optional integration
    from . import DEFAULT_STRENGTH, DEFAULT_TIME  # type: ignore[unused-ignore]
except Exception:  # pragma: no cover - defensive import
    DEFAULT_STRENGTH = None  # type: ignore[assignment]
    DEFAULT_TIME = None  # type: ignore[assignment]

console = Console()

__all__ = ["run_agentic_bug"]


def _check_gh_cli() -> bool:
    """Check if the GitHub CLI (gh) is installed and available on PATH."""
    return shutil.which("gh") is not None


def _parse_github_url(url: str) -> Optional[Tuple[str, str, int]]:
    """
    Parse a GitHub issue URL to extract owner, repo, and issue number.

    Supported formats:
    - https://github.com/{owner}/{repo}/issues/{number}
    - https://www.github.com/{owner}/{repo}/issues/{number}
    - github.com/{owner}/{repo}/issues/{number}

    Args:
        url: The GitHub issue URL string.

    Returns:
        A tuple of (owner, repo, issue_number) if successful, else None.
    """
    # Normalize protocol
    if not url.startswith("http"):
        url = "https://" + url.lstrip("/")

    pattern = r"github\.com/([^/]+)/([^/]+)/issues/(\d+)"
    match = re.search(pattern, url)

    if match:
        owner, repo, number_str = match.groups()
        try:
            return owner, repo, int(number_str)
        except ValueError:
            return None
    return None


def _fetch_issue_data(owner: str, repo: str, number: int) -> Tuple[Optional[Dict[str, Any]], str]:
    """
    Fetch issue details using `gh api`.

    Args:
        owner: Repository owner.
        repo: Repository name.
        number: Issue number.

    Returns:
        (data_dict, error_message)
        - data_dict: JSON response from GitHub API if successful.
        - error_message: Error description if failed.
    """
    cmd = [
        "gh", "api",
        f"repos/{owner}/{repo}/issues/{number}",
        "--header", "Accept: application/vnd.github+json"
    ]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        return json.loads(result.stdout), ""
    except subprocess.CalledProcessError as e:
        return None, f"Failed to fetch issue: {e.stderr.strip()}"
    except json.JSONDecodeError:
        return None, "Failed to parse GitHub API response."
    except Exception as e:
        return None, str(e)


def _fetch_comments(comments_url: str) -> str:
    """
    Fetch comments for the issue to provide full context.

    Args:
        comments_url: The API URL for the issue's comments.

    Returns:
        A formatted string containing all comments, or an empty string on failure.
    """
    # The comments_url from the API is usually full absolute URL like:
    # https://api.github.com/repos/owner/repo/issues/1/comments
    # `gh api` handles full URLs gracefully.
    cmd = ["gh", "api", comments_url]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        comments_data = json.loads(result.stdout)
        
        formatted_comments = []
        for comment in comments_data:
            user = comment.get("user", {}).get("login", "unknown")
            body = comment.get("body", "")
            formatted_comments.append(f"--- Comment by {user} ---\n{body}\n")
        
        return "\n".join(formatted_comments)
    except Exception:
        # If comments fail to load, we proceed with just the issue body
        return ""


def _clone_repo(owner: str, repo: str, target_dir: Path) -> bool:
    """
    Clone the repository into the target directory.

    Args:
        owner: Repository owner.
        repo: Repository name.
        target_dir: Directory to clone into.

    Returns:
        True if successful, False otherwise.
    """
    repo_url = f"https://github.com/{owner}/{repo}.git"
    cmd = ["git", "clone", repo_url, str(target_dir)]
    try:
        subprocess.run(cmd, check=True, capture_output=True)
        return True
    except subprocess.CalledProcessError:
        return False


def run_agentic_bug(
    issue_url: str,
    *,
    verbose: bool = False,
    quiet: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Run the agentic bug investigation workflow for a given GitHub issue.

    Steps:
    1. Validates `gh` CLI availability.
    2. Parses the issue URL.
    3. Fetches issue metadata and content via GitHub API.
    4. Clones the repository to a temporary workspace.
    5. Invokes the orchestrator to run the investigation steps.

    Args:
        issue_url: The full URL to the GitHub issue.
        verbose: If True, print detailed logs.
        quiet: If True, suppress all non-essential output.

    Returns:
        A 5-tuple:
            (success, message, total_cost, model_used, changed_files)
    """
    # 1. Check prerequisites
    if not _check_gh_cli():
        msg = "gh CLI not found. Please install GitHub CLI to use this feature."
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    # 2. Parse URL
    parsed = _parse_github_url(issue_url)
    if not parsed:
        msg = f"Invalid GitHub URL: {issue_url}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    owner, repo, issue_number = parsed

    if not quiet:
        console.print(f"[blue]Fetching issue #{issue_number} from {owner}/{repo}...[/blue]")

    # 3. Fetch Issue Data
    issue_data, error_msg = _fetch_issue_data(owner, repo, issue_number)
    if not issue_data:
        msg = f"Issue not found: {error_msg}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    # Extract fields
    title = issue_data.get("title", "")
    body = issue_data.get("body", "") or ""
    author = issue_data.get("user", {}).get("login", "unknown")
    comments_url = issue_data.get("comments_url", "")
    
    # Fetch comments for context
    comments_text = _fetch_comments(comments_url) if comments_url else ""
    
    full_issue_content = (
        f"Title: {title}\n"
        f"Author: {author}\n"
        f"Description:\n{body}\n\n"
        f"Comments:\n{comments_text}"
    )

    # 4. Setup Workspace & Clone Repo
    # We use a temporary directory to avoid messing with the user's current working directory
    # unless we are already inside the target repo. For safety, we'll assume a fresh clone is best
    # for an isolated agentic run, or the orchestrator can handle existing dirs.
    # Here, we create a temp dir.
    
    with tempfile.TemporaryDirectory(prefix=f"pdd_bug_{issue_number}_") as temp_dir_str:
        temp_dir = Path(temp_dir_str)
        
        if not quiet:
            console.print(f"[blue]Cloning repository to temporary workspace: {temp_dir}[/blue]")
        
        if not _clone_repo(owner, repo, temp_dir):
            msg = "Failed to clone repository."
            if not quiet:
                console.print(f"[red]{msg}[/red]")
            return False, msg, 0.0, "", []

        # The clone creates a subdirectory with the repo name. We need to find it.
        # Usually `git clone url dir` puts it IN dir if dir is empty, or creates subdir?
        # `git clone url target_dir` puts contents INTO target_dir if it's empty? 
        # Actually `git clone url path` puts the repo IN `path`.
        # So the root of the repo is `temp_dir`.
        
        # 5. Invoke Orchestrator
        if not quiet:
            console.print(f"[green]Starting agentic investigation for: {title}[/green]")

        try:
            success, message, cost, model, changed_files = run_agentic_bug_orchestrator(
                issue_url=issue_url,
                issue_content=full_issue_content,
                repo_owner=owner,
                repo_name=repo,
                issue_number=issue_number,
                issue_author=author,
                issue_title=title,
                cwd=temp_dir,
                verbose=verbose,
                quiet=quiet
            )
            
            # Since we ran in a temp dir, the changed files are there. 
            # In a real scenario, we might want to copy them back or push a PR.
            # The orchestrator usually handles PR creation (step 9), so local files might be ephemeral.
            # We return the paths relative to the repo root.
            
            return success, message, cost, model, changed_files

        except Exception as e:
            msg = f"Orchestrator failed with exception: {e}"
            if not quiet:
                console.print(f"[red]{msg}[/red]")
                if verbose:
                    import traceback
                    console.print(traceback.format_exc())
            return False, msg, 0.0, "", []