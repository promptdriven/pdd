"""CLI entry point for the agentic E2E fix workflow."""

from __future__ import annotations

import json
import re
import shutil
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from rich.console import Console

from .agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator


console = Console()

_GITHUB_ISSUE_URL_RE = re.compile(
    r"^(?:https?://)?(?:www\.)?github\.com/([^/]+)/([^/]+)/issues/(\d+)(?:[/?#].*)?$"
)
_BRANCH_PATTERNS = (
    re.compile(r"Switched to (?:a new )?branch ['\"`]([^'\"`\n]+)['\"`]"),
    re.compile(r"Created branch ['\"`]([^'\"`\n]+)['\"`]"),
    re.compile(r"Branch:\s*([A-Za-z0-9._/\-]+)"),
)
_WORKTREE_PREFIXES = ("fix", "bug", "change")


def _check_gh_cli() -> bool:
    """Return True when the GitHub CLI is available on PATH."""
    return shutil.which("gh") is not None


def _parse_github_url(url: str) -> Optional[Tuple[str, str, int]]:
    """Parse a GitHub issue URL into owner, repo, and issue number."""
    match = _GITHUB_ISSUE_URL_RE.match(url.strip())
    if not match:
        return None

    owner, repo, issue_number = match.groups()
    return owner, repo, int(issue_number)


def _run_command(
    command: Sequence[str],
    *,
    cwd: Optional[Path] = None,
) -> subprocess.CompletedProcess[str]:
    """Run a subprocess command with captured text output."""
    return subprocess.run(
        list(command),
        cwd=str(cwd) if cwd is not None else None,
        capture_output=True,
        text=True,
        check=True,
    )


def _fetch_issue_data(
    owner: str,
    repo: str,
    number: int,
) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    """Fetch GitHub issue metadata via `gh api`."""
    command = [
        "gh",
        "api",
        f"repos/{owner}/{repo}/issues/{number}",
        "--header",
        "Accept: application/vnd.github+json",
    ]

    try:
        result = _run_command(command)
        payload = json.loads(result.stdout)
    except FileNotFoundError:
        return None, "gh CLI not found. Please install GitHub CLI to use this feature."
    except subprocess.CalledProcessError as exc:
        details = exc.stderr.strip() or exc.stdout.strip() or str(exc)
        return None, f"Failed to fetch issue: {details}"
    except json.JSONDecodeError:
        return None, "Failed to parse GitHub API response"

    if not isinstance(payload, dict):
        return None, "Unexpected GitHub API response for issue"

    return payload, None


def _flatten_comment_pages(payload: Any) -> List[Dict[str, Any]]:
    """Flatten `gh api --paginate --slurp` output into a list of comment objects."""
    if not isinstance(payload, list):
        return []

    comments: List[Dict[str, Any]] = []
    for item in payload:
        if isinstance(item, dict):
            comments.append(item)
            continue
        if isinstance(item, list):
            comments.extend(entry for entry in item if isinstance(entry, dict))
    return comments


def _fetch_issue_comments(comments_url: str) -> str:
    """Fetch and format all issue comments for prompt context."""
    if not comments_url:
        return ""

    command = [
        "gh",
        "api",
        comments_url,
        "--paginate",
        "--slurp",
        "--header",
        "Accept: application/vnd.github+json",
    ]

    try:
        result = _run_command(command)
        payload = json.loads(result.stdout)
    except (FileNotFoundError, subprocess.CalledProcessError, json.JSONDecodeError):
        return ""

    formatted_comments: List[str] = []
    for comment in _flatten_comment_pages(payload):
        author = str(comment.get("user", {}).get("login") or "unknown")
        body = str(comment.get("body") or "").strip()
        formatted_comments.append(f"--- Comment by {author} ---\n{body}".rstrip())

    return "\n\n".join(formatted_comments)


def _find_worktree_base(start: Path) -> Optional[Path]:
    """Locate the repo-level `.pdd/worktrees` directory from the current workspace."""
    resolved_start = start.resolve()
    for candidate in (resolved_start, *resolved_start.parents):
        worktree_base = candidate / ".pdd" / "worktrees"
        if worktree_base.is_dir():
            return worktree_base

    try:
        result = _run_command(["git", "rev-parse", "--show-toplevel"], cwd=resolved_start)
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None

    repo_root = Path(result.stdout.strip())
    for candidate in (repo_root, *repo_root.parents):
        worktree_base = candidate / ".pdd" / "worktrees"
        if worktree_base.is_dir():
            return worktree_base

    return None


def _find_worktree_for_issue(issue_number: int) -> Optional[Path]:
    """Find a local worktree matching the issue number."""
    worktree_base = _find_worktree_base(Path.cwd())
    if worktree_base is None:
        return None

    for prefix in _WORKTREE_PREFIXES:
        candidate = worktree_base / f"{prefix}-issue-{issue_number}"
        if candidate.is_dir() and (candidate / ".git").exists():
            return candidate.resolve()
    return None


def _get_current_branch(cwd: Path) -> str:
    """Return the current git branch for the provided working directory."""
    try:
        result = _run_command(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=cwd)
    except (FileNotFoundError, subprocess.CalledProcessError):
        return ""
    return result.stdout.strip()


def _extract_branch_from_comments(comments_text: str) -> Optional[str]:
    """Extract the last branch hint mentioned in issue comments."""
    branch_name: Optional[str] = None
    for pattern in _BRANCH_PATTERNS:
        for match in pattern.finditer(comments_text):
            branch_name = match.group(1)
    return branch_name


def _find_working_directory(
    issue_number: int,
    issue_comments: str,
    quiet: bool,
    force: bool = False,
) -> Tuple[Path, Optional[str], bool]:
    """Resolve the working directory and enforce branch-safety checks."""
    worktree_path = _find_worktree_for_issue(issue_number)
    if worktree_path is not None:
        if not quiet:
            console.print(f"[blue]Using worktree: {worktree_path}[/blue]")
        return worktree_path, None, False

    cwd = Path.cwd()
    expected_branch = _extract_branch_from_comments(issue_comments)
    current_branch = _get_current_branch(cwd) if expected_branch else ""

    if expected_branch and current_branch and expected_branch != current_branch:
        warning = (
            f"Expected branch '{expected_branch}' but current branch is '{current_branch}'. "
            f"Run `git checkout {expected_branch}` or pass `--force` to continue."
        )
        if force:
            if not quiet:
                console.print(f"[yellow]{warning}[/yellow]")
            return cwd, warning, False
        return cwd, warning, True

    if not quiet:
        console.print(
            "[yellow]"
            f"No issue worktree found for #{issue_number}; using current directory: {cwd}"
            "[/yellow]"
        )
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
    protect_tests: bool = False,
    ci_retries: int = 3,
    skip_ci: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """Run the agentic E2E fix workflow for a GitHub issue."""
    if not _check_gh_cli():
        message = "gh CLI not found. Please install GitHub CLI to use this feature."
        if not quiet:
            console.print(f"[red]{message}[/red]")
        return False, message, 0.0, "", []

    parsed_issue = _parse_github_url(issue_url)
    if parsed_issue is None:
        message = f"Invalid GitHub URL: {issue_url}"
        if not quiet:
            console.print(f"[red]{message}[/red]")
        return False, message, 0.0, "", []

    repo_owner, repo_name, issue_number = parsed_issue
    if not quiet:
        console.print(
            f"[bold blue]Fetching issue #{issue_number} from {repo_owner}/{repo_name}[/bold blue]"
        )

    issue_data, error = _fetch_issue_data(repo_owner, repo_name, issue_number)
    if error or issue_data is None:
        message = error or "Failed to fetch issue data"
        if not quiet:
            console.print(f"[red]{message}[/red]")
        return False, message, 0.0, "", []

    issue_title = str(issue_data.get("title") or "")
    issue_body = str(issue_data.get("body") or "")
    issue_author = str(issue_data.get("user", {}).get("login") or "unknown")
    comments_url = str(issue_data.get("comments_url") or "")
    comments_text = _fetch_issue_comments(comments_url)
    issue_content = (
        f"Title: {issue_title}\n\n"
        f"Description:\n{issue_body}\n\n"
        f"Comments:\n{comments_text}"
    )

    cwd, warning_message, should_abort = _find_working_directory(
        issue_number,
        comments_text,
        quiet,
        force,
    )
    if should_abort:
        if not quiet:
            console.print("[red]Aborting due to branch mismatch.[/red]")
            if warning_message:
                console.print(f"[red]{warning_message}[/red]")
        return (
            False,
            warning_message or "Branch mismatch - use --force to override",
            0.0,
            "",
            [],
        )

    if not quiet:
        console.print(
            f"[bold green]Starting Agentic E2E Fix for Issue #{issue_number}[/bold green]"
        )
        console.print(f"[blue]Working directory: {cwd}[/blue]")

    try:
        return run_agentic_e2e_fix_orchestrator(
            issue_url=issue_url,
            issue_content=issue_content,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_author=issue_author,
            issue_title=issue_title,
            cwd=cwd,
            timeout_adder=timeout_adder,
            max_cycles=max_cycles,
            resume=resume,
            verbose=verbose,
            quiet=quiet,
            use_github_state=use_github_state,
            protect_tests=protect_tests,
            ci_retries=ci_retries,
            skip_ci=skip_ci,
        )
    except Exception as exc:
        message = f"Orchestrator failed: {exc}"
        if not quiet:
            console.print(f"[red]{message}[/red]")
        return False, message, 0.0, "", []
