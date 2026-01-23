"""
CLI entry point for the agentic test generation workflow.
Fetches a GitHub issue, extracts content and metadata describing what needs to be tested,
then invokes the orchestrator to run the 9-step test generation process.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import List, Tuple, Optional, Dict, Any
from urllib.parse import urlparse

from rich.console import Console

from .agentic_test_orchestrator import run_agentic_test_orchestrator
from . import cmd_test_main

# Initialize console for rich output
console = Console()


def _check_gh_cli() -> bool:
    """Check if the GitHub CLI (gh) is installed and available."""
    return shutil.which("gh") is not None


def _parse_github_url(url: str) -> Optional[Tuple[str, str, int]]:
    """
    Parse GitHub issue URL to extract owner, repo, and issue number.
    Supported formats:
    - https://github.com/{owner}/{repo}/issues/{number}
    - https://www.github.com/{owner}/{repo}/issues/{number}
    - github.com/{owner}/{repo}/issues/{number}
    """
    # Ensure scheme exists for urlparse to correctly identify netloc vs path
    if not url.startswith("http://") and not url.startswith("https://"):
        url = "https://" + url

    parsed = urlparse(url)
    # Split path and filter out empty strings (e.g. from leading/trailing slashes)
    path_parts = [p for p in parsed.path.split("/") if p]

    # Expected path structure: owner/repo/issues/number
    # We look for the 'issues' segment to anchor our parsing
    try:
        if "issues" in path_parts:
            issues_index = path_parts.index("issues")
            # We need at least 2 parts before 'issues' (owner, repo) and 1 after (number)
            if issues_index >= 2 and len(path_parts) > issues_index + 1:
                owner = path_parts[issues_index - 2]
                repo = path_parts[issues_index - 1]
                number_str = path_parts[issues_index + 1]
                # Handle cases where number might be followed by fragment or query (though urlparse handles those)
                # or if there's a trailing slash that resulted in an empty part (handled by list comp)
                return owner, repo, int(number_str)
    except ValueError:
        return None
        
    return None


def _fetch_issue_data(owner: str, repo: str, number: int) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    """
    Fetch issue data and comments using the GitHub CLI.
    Returns (issue_data_dict, error_message).
    """
    try:
        # Fetch issue details
        cmd = [
            "gh", "api",
            f"repos/{owner}/{repo}/issues/{number}",
            "--header", "Accept: application/vnd.github+json"
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        issue_json = json.loads(result.stdout)

        # Extract labels and state
        labels = [l.get("name", "") for l in issue_json.get("labels", [])]
        state = issue_json.get("state", "open")

        # Fetch comments to provide full context
        comments_url = issue_json.get("comments_url")
        comments_text = ""
        if comments_url:
            # The comments_url is a full URL. gh api accepts full URLs.
            cmd_comments = ["gh", "api", comments_url]
            # We don't check=True here because comment fetching failure shouldn't block the whole process
            res_comments = subprocess.run(cmd_comments, capture_output=True, text=True, check=False)
            if res_comments.returncode == 0:
                try:
                    comments_data = json.loads(res_comments.stdout)
                    if isinstance(comments_data, list):
                        comments_text = "\n\n--- Comments ---\n"
                        for comment in comments_data:
                            user = comment.get("user", {}).get("login", "Unknown")
                            body = comment.get("body", "")
                            comments_text += f"\nUser: {user}\n{body}\n"
                except json.JSONDecodeError:
                    pass # Ignore comment parsing errors

        # Combine body, metadata, and comments
        meta_info = f"State: {state}\nLabels: {', '.join(labels)}\n"
        full_content = meta_info + "\n" + (issue_json.get("body") or "") + comments_text
        issue_json["full_content_with_comments"] = full_content
        
        return issue_json, None

    except subprocess.CalledProcessError as e:
        err_msg = e.stderr.strip() if e.stderr else str(e)
        return None, f"GitHub API call failed: {err_msg}"
    except json.JSONDecodeError:
        return None, "Failed to parse GitHub API response"
    except Exception as e:
        return None, str(e)


def _ensure_repo_context(owner: str, repo: str, cwd: Path, quiet: bool) -> Tuple[bool, str]:
    """
    Ensure we are in the correct repository.
    If the current directory is not the repo, clone it to a temp directory.
    Returns (success, path_or_error_msg).
    """
    # Check current git remote
    try:
        res = subprocess.run(
            ["git", "remote", "get-url", "origin"],
            cwd=cwd,
            capture_output=True,
            text=True
        )
        if res.returncode == 0:
            remote_url = res.stdout.strip()
            # Simple check if owner/repo is in the remote URL
            # Matches github.com/owner/repo or github.com:owner/repo
            if f"{owner}/{repo}" in remote_url or f"{owner}:{repo}" in remote_url:
                return True, str(cwd)
    except FileNotFoundError:
        pass  # git not installed or not in path, handled later

    # If we are not in the repo, clone it into a temp dir.
    try:
        temp_dir = Path(tempfile.mkdtemp(prefix=f"pdd_test_{repo}_"))
    except Exception as e:
        return False, f"Failed to create temp directory: {e}"

    if not quiet:
        console.print(f"[yellow]Current directory does not match {owner}/{repo}. Cloning to {temp_dir}...[/yellow]")
    
    try:
        clone_url = f"https://github.com/{owner}/{repo}.git"
        subprocess.run(["git", "clone", clone_url, "."], cwd=temp_dir, check=True, capture_output=quiet)
        return True, str(temp_dir)
    except subprocess.CalledProcessError as e:
        # Clean up empty temp dir if clone failed
        shutil.rmtree(temp_dir, ignore_errors=True)
        return False, f"Failed to clone repository: {e}"


def run_agentic_test(
    issue_url: str,
    *,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Main entry point for agentic test generation.
    
    Args:
        issue_url: GitHub issue URL (e.g. https://github.com/owner/repo/issues/123)
        verbose: Enable verbose logging
        quiet: Suppress non-error output
        timeout_adder: Additional seconds to add to step timeouts
        use_github_state: Whether to persist state to GitHub comments
        
    Returns:
        (success, message, total_cost, model_used, changed_files)
    """
    # 1. Check prerequisites
    if not _check_gh_cli():
        msg = "GitHub CLI (gh) not found. Please install it: https://cli.github.com/"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, "gh CLI not found", 0.0, "", []

    # 2. Parse URL
    parsed = _parse_github_url(issue_url)
    if not parsed:
        msg = f"Invalid GitHub URL format: {issue_url}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, "Invalid GitHub URL", 0.0, "", []
    
    owner, repo, issue_number = parsed

    if not quiet:
        console.print(f"[blue]Fetching issue #{issue_number} from {owner}/{repo}...[/blue]")

    # 3. Fetch Issue Data
    issue_data, error = _fetch_issue_data(owner, repo, issue_number)
    if not issue_data:
        msg = f"Issue not found or API error: {error}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, f"Issue not found: {error}", 0.0, "", []

    # Extract metadata
    issue_title = issue_data.get("title", f"Issue #{issue_number}")
    issue_author = issue_data.get("user", {}).get("login", "unknown")
    issue_content = issue_data.get("full_content_with_comments", "")
    
    # 4. Setup Repository Context
    current_cwd = Path.cwd()
    is_repo, repo_path_str = _ensure_repo_context(owner, repo, current_cwd, quiet)
    
    if not is_repo:
        # repo_path_str contains error message in this case
        if not quiet:
            console.print(f"[red]{repo_path_str}[/red]")
        return False, repo_path_str, 0.0, "", []
    
    repo_path = Path(repo_path_str)

    # 5. Run Orchestrator
    try:
        return run_agentic_test_orchestrator(
            issue_url=issue_url,
            issue_content=issue_content,
            repo_owner=owner,
            repo_name=repo,
            issue_number=issue_number,
            issue_author=issue_author,
            issue_title=issue_title,
            cwd=repo_path,
            verbose=verbose,
            quiet=quiet,
            timeout_adder=timeout_adder,
            use_github_state=use_github_state
        )
    except Exception as e:
        import traceback
        if verbose:
            traceback.print_exc()
        return False, f"Orchestrator failed: {str(e)}", 0.0, "unknown", []
    finally:
        # Cleanup if we created a temp directory
        if repo_path != current_cwd and repo_path.exists():
            if not quiet:
                console.print(f"[dim]Cleaning up temporary repository at {repo_path}...[/dim]")
            try:
                shutil.rmtree(repo_path)
            except Exception as e:
                if verbose:
                    console.print(f"[yellow]Warning: Failed to cleanup temp dir: {e}[/yellow]")


def main():
    parser = argparse.ArgumentParser(description="Agentic Test Generation CLI")
    parser.add_argument("--manual", action="store_true", help="Use manual prompt-based generation (legacy mode)")
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose output")
    parser.add_argument("--quiet", "-q", action="store_true", help="Suppress output")
    parser.add_argument("--timeout-adder", type=float, default=0.0, help="Add seconds to step timeouts")
    parser.add_argument("--no-github-state", action="store_true", help="Disable GitHub state persistence")
    
    # We use parse_known_args because manual mode might have different positional args
    args, remaining = parser.parse_known_args()

    if args.manual:
        # Delegate to cmd_test_main
        # Remove --manual from sys.argv so cmd_test_main doesn't choke on it
        sys.argv = [arg for arg in sys.argv if arg != "--manual"]
        cmd_test_main.main()
        return

    # Agentic Mode
    if not remaining:
        console.print("[red]Error: Issue URL required[/red]")
        sys.exit(1)
    
    issue_url = remaining[0]
    
    success, msg, cost, model, files = run_agentic_test(
        issue_url=issue_url,
        verbose=args.verbose,
        quiet=args.quiet,
        timeout_adder=args.timeout_adder,
        use_github_state=not args.no_github_state
    )
    
    if not success:
        sys.exit(1)


def agentic_test_main():
    """Backward-compatible alias for CLI entry point."""
    return main()


if __name__ == "__main__":
    main()
