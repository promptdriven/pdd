from __future__ import annotations

import json
import re
import shutil
import subprocess
from pathlib import Path
from typing import List, Optional, Tuple, Dict, Any

from rich.console import Console

from .agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

# Initialize rich console for printing
console = Console()


def _check_gh_cli() -> bool:
    """Check if the GitHub CLI (gh) is installed and available."""
    return shutil.which("gh") is not None


def _parse_github_url(url: str) -> Tuple[Optional[str], Optional[str], Optional[int]]:
    """
    Parse a GitHub issue URL to extract owner, repo, and issue number.

    Supported formats:
    - https://github.com/{owner}/{repo}/issues/{number}
    - https://www.github.com/{owner}/{repo}/issues/{number}
    - github.com/{owner}/{repo}/issues/{number}

    Returns:
        Tuple[owner, repo, number] or (None, None, None) if parsing fails.
    """
    # Remove protocol and www
    clean_url = url.replace("https://", "").replace("http://", "").replace("www.", "")
    
    # Regex for github.com/owner/repo/issues/number
    pattern = r"^github\.com/([^/]+)/([^/]+)/issues/(\d+)"
    match = re.match(pattern, clean_url)
    
    if match:
        return match.group(1), match.group(2), int(match.group(3))
    return None, None, None


def _fetch_issue_data(owner: str, repo: str, number: int) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    """
    Fetch issue data using `gh api`.

    Returns:
        Tuple[issue_json, error_message]
    """
    cmd = [
        "gh", "api", 
        f"repos/{owner}/{repo}/issues/{number}",
        "--header", "Accept: application/vnd.github+json"
    ]
    
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        return json.loads(result.stdout), None
    except subprocess.CalledProcessError as e:
        return None, f"Failed to fetch issue: {e.stderr.strip()}"
    except json.JSONDecodeError:
        return None, "Failed to parse GitHub API response"


def _fetch_issue_comments(comments_url: str) -> str:
    """
    Fetch all comments for an issue to build full context.
    The comments_url usually looks like: https://api.github.com/repos/{owner}/{repo}/issues/{number}/comments
    """
    # gh api accepts full URLs if they are within github.com api
    # We need to strip the base API URL to pass to `gh api` or pass the full URL
    # `gh api` handles full URLs gracefully usually, but let's be safe and use the path relative to API root if possible,
    # or just pass the full URL which `gh` supports.
    
    cmd = ["gh", "api", comments_url, "--paginate"]
    
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        comments_data = json.loads(result.stdout)
        
        full_text = []
        for comment in comments_data:
            author = comment.get("user", {}).get("login", "unknown")
            body = comment.get("body", "")
            full_text.append(f"--- Comment by {author} ---\n{body}\n")
            
        return "\n".join(full_text)
    except subprocess.CalledProcessError:
        return ""  # Return empty string on failure, don't block execution
    except json.JSONDecodeError:
        return ""


def _find_worktree_for_issue(issue_number: int) -> Optional[Path]:
    """
    Check .pdd/worktrees/ relative to git root for specific issue worktrees.
    Returns the path if found and valid, else None.
    """
    try:
        # Find git root
        git_root_cmd = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"], 
            capture_output=True, text=True, check=True
        )
        git_root = Path(git_root_cmd.stdout.strip())
    except subprocess.CalledProcessError:
        return None

    worktree_base = git_root / ".pdd" / "worktrees"
    if not worktree_base.exists():
        return None

    # Candidate directory names
    candidates = [
        f"fix-issue-{issue_number}",
        f"bug-issue-{issue_number}",
        f"change-issue-{issue_number}"
    ]

    for candidate in candidates:
        path = worktree_base / candidate
        if path.exists() and path.is_dir():
            # Verify it's a git repo/worktree
            if (path / ".git").exists():
                return path
    
    return None


def _get_current_branch(cwd: Path) -> str:
    """Get the current git branch name for a given directory."""
    try:
        cmd = ["git", "rev-parse", "--abbrev-ref", "HEAD"]
        result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=True)
        return result.stdout.strip()
    except subprocess.CalledProcessError:
        return ""


def _extract_branch_from_comments(comments_text: str) -> Optional[str]:
    """
    Attempt to parse the branch name created by `pdd bug` from issue comments.
    Looks for patterns like 'Created branch: <name>' or similar indicators if standard pdd output is present.
    """
    # Heuristic: pdd bug usually outputs "Switched to branch '...'" or "Created branch '...'"
    # Regex to find branch names in typical pdd output logs pasted in comments
    # Example: "Switched to a new branch 'fix-issue-123'"
    
    patterns = [
        r"Switched to a new branch '([^']+)'",
        r"Switched to branch '([^']+)'",
        r"Created branch '([^']+)'",
        r"Branch: ([a-zA-Z0-9_\-/]+)"
    ]
    
    for pattern in patterns:
        match = re.search(pattern, comments_text)
        if match:
            return match.group(1)
    return None


def _find_working_directory(
    issue_number: int, 
    issue_comments: str, 
    quiet: bool, 
    force: bool = False
) -> Tuple[Path, Optional[str], bool]:
    """
    Determine the correct working directory.
    
    Logic:
    1. Check for local worktree.
    2. If no worktree, check current directory branch against expected branch from comments.
    3. If mismatch and not force, abort.
    
    Returns:
        (working_directory, warning_message, should_abort)
    """
    # 1. Try finding a worktree
    worktree_path = _find_worktree_for_issue(issue_number)
    if worktree_path:
        if not quiet:
            console.print(f"[blue]Using worktree: {worktree_path}[/blue]")
        return worktree_path, None, False

    # 2. Fallback to current directory
    cwd = Path.cwd()
    
    # 3. Check branch safety
    expected_branch = _extract_branch_from_comments(issue_comments)
    
    if expected_branch:
        current_branch = _get_current_branch(cwd)
        # If we found an expected branch and it doesn't match current
        if current_branch and expected_branch != current_branch:
            warning = (
                f"Expected branch '{expected_branch}' but on '{current_branch}'.\n"
                f"Suggestion: git fetch origin && git checkout {expected_branch}"
            )
            
            if force:
                if not quiet:
                    console.print(f"[yellow]Warning: {warning} (--force specified)[/yellow]")
                return cwd, warning, False
            else:
                return cwd, warning, True
    
    if not quiet:
        console.print(f"[yellow]No worktree found for issue #{issue_number}, using current directory[/yellow]")
        
    return cwd, None, False


def run_agentic_e2e_fix(
    issue_url: str,
    *,
    timeout_adder: float = 0.0,
    max_cycles: int = 5,
    resume: bool = True,
    force: bool = False,
    verbose: bool = False,
    quiet: bool = False,
    use_github_state: bool = True,
    protect_tests: bool = False
) -> Tuple[bool, str, float, str, List[str]]:
    """
    CLI entry point for the agentic e2e fix workflow.

    Args:
        issue_url: The full GitHub issue URL.
        timeout_adder: Additional seconds to add to each step's timeout.
        max_cycles: Maximum outer loop cycles before giving up.
        resume: Whether to resume from saved state.
        force: Override branch mismatch safety checks.
        verbose: Show detailed output.
        quiet: Suppress non-error output.
        use_github_state: Enable/disable GitHub comment-based state persistence.
        protect_tests: When True, prevents modification of test files during fix.

    Returns:
        (success, message, total_cost, model_used, changed_files)
    """
    # 1. Check dependencies
    if not _check_gh_cli():
        msg = "gh CLI not found. Please install GitHub CLI to use this feature."
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    # 2. Parse URL
    owner, repo, number = _parse_github_url(issue_url)
    if not owner or not repo or not number:
        msg = f"Invalid GitHub URL: {issue_url}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    if not quiet:
        console.print(f"[bold blue]Fetching issue #{number} from {owner}/{repo}...[/bold blue]")

    # 3. Fetch Issue Data
    issue_data, error = _fetch_issue_data(owner, repo, number)
    if error or not issue_data:
        msg = f"Issue not found: {error}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    # Extract fields
    issue_title = issue_data.get("title", "")
    issue_body = issue_data.get("body", "")
    issue_author = issue_data.get("user", {}).get("login", "unknown")
    comments_url = issue_data.get("comments_url", "")

    # 4. Fetch Comments (Context)
    comments_text = ""
    if comments_url:
        comments_text = _fetch_issue_comments(comments_url)

    # Combine body and comments for full context
    full_issue_content = f"Title: {issue_title}\n\nDescription:\n{issue_body}\n\nComments:\n{comments_text}"

    # 5. Determine Working Directory
    cwd, warning_msg, should_abort = _find_working_directory(
        number, comments_text, quiet, force
    )

    if should_abort:
        if not quiet:
            console.print(f"[red]Aborting to prevent working in wrong directory.[/red]")
            if warning_msg:
                console.print(f"[red]{warning_msg}[/red]")
            console.print("[red]Use --force to override.[/red]")
        return False, "Branch mismatch - use --force to override", 0.0, "", []

    # 6. Run Orchestrator
    if not quiet:
        console.print(f"[bold green]Starting Agentic E2E Fix for Issue #{number}[/bold green]")
        console.print(f"Working Directory: {cwd}")

    return run_agentic_e2e_fix_orchestrator(
        issue_url=issue_url,
        issue_content=full_issue_content,
        repo_owner=owner,
        repo_name=repo,
        issue_number=number,
        issue_author=issue_author,
        issue_title=issue_title,
        cwd=cwd,
        timeout_adder=timeout_adder,
        max_cycles=max_cycles,
        resume=resume,
        verbose=verbose,
        quiet=quiet,
        use_github_state=use_github_state,
        protect_tests=protect_tests
    )
