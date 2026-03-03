"""
sync_code_main.py
~~~~~~~~~~~~~~~~~

Core logic for `pdd sync-code`: scans the repo for changed code files
and runs `pdd update` on each to reverse-sync code changes back into prompts.

Change detection strategy:
1. Primary: Compare current code SHA256 hash vs stored fingerprint hash.
2. Fallback: If no fingerprint exists, use git diff to detect changes.
"""

import os
import subprocess
from pathlib import Path
from typing import Optional, Set, Tuple, List, Dict, Any

import click
import git
from rich import print as rprint
from rich.console import Console
from rich.progress import (
    Progress,
    SpinnerColumn,
    TextColumn,
    BarColumn,
    TimeRemainingColumn,
)
from rich.table import Table
from rich.theme import Theme

from .get_language import get_language
from .sync_determine_operation import (
    calculate_sha256,
    read_fingerprint,
    _safe_basename,
)
from .update_main import find_and_resolve_all_pairs, update_file_pair

custom_theme = Theme({
    "info": "cyan",
    "warning": "yellow",
    "error": "bold red",
    "success": "green",
    "path": "dim blue",
})
console = Console(theme=custom_theme)


def get_git_changed_files(repo_root: str, base_branch: str = "main") -> Set[str]:
    """Get the set of files changed relative to a base branch.

    Combines three sources:
    - Files changed between merge-base and HEAD (committed changes)
    - Uncommitted changes (staged + unstaged vs HEAD)
    - Untracked files

    Args:
        repo_root: Absolute path to the repository root.
        base_branch: The base branch to compare against.

    Returns:
        Set of absolute file paths that have changed.
    """
    changed: Set[str] = set()

    try:
        # Find the merge base
        merge_base = subprocess.run(
            ["git", "merge-base", "HEAD", base_branch],
            capture_output=True, text=True, cwd=repo_root, check=True,
        ).stdout.strip()

        # Committed changes since merge-base (Added, Copied, Modified, Renamed)
        committed = subprocess.run(
            ["git", "diff", "--name-only", "--diff-filter=ACMR", merge_base, "HEAD"],
            capture_output=True, text=True, cwd=repo_root, check=True,
        ).stdout.strip()
        if committed:
            for f in committed.splitlines():
                changed.add(os.path.join(repo_root, f))
    except subprocess.CalledProcessError:
        # If merge-base fails (e.g., no common ancestor), skip committed changes
        pass

    try:
        # Uncommitted changes (staged + unstaged)
        uncommitted = subprocess.run(
            ["git", "diff", "--name-only", "HEAD"],
            capture_output=True, text=True, cwd=repo_root, check=True,
        ).stdout.strip()
        if uncommitted:
            for f in uncommitted.splitlines():
                changed.add(os.path.join(repo_root, f))
    except subprocess.CalledProcessError:
        pass

    try:
        # Untracked files
        untracked = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard"],
            capture_output=True, text=True, cwd=repo_root, check=True,
        ).stdout.strip()
        if untracked:
            for f in untracked.splitlines():
                changed.add(os.path.join(repo_root, f))
    except subprocess.CalledProcessError:
        pass

    return changed


def derive_basename_and_language(
    code_file_path: str, repo_root: str
) -> Tuple[Optional[str], Optional[str]]:
    """Extract basename (file stem) and language from a code file path.

    Args:
        code_file_path: Absolute path to the code file.
        repo_root: Absolute path to the repository root.

    Returns:
        (basename, language) or (None, None) for unknown extensions.
    """
    ext = os.path.splitext(code_file_path)[1]
    language = get_language(ext)
    if not language:
        return None, None

    basename = os.path.splitext(os.path.basename(code_file_path))[0]
    return basename, language.lower()


def is_code_changed(
    code_file_path: str,
    repo_root: str,
    git_changed_files: Set[str],
) -> Tuple[bool, str]:
    """Determine whether a code file has changed since last sync.

    Strategy:
    1. If a fingerprint exists, compare current SHA256 vs stored code_hash.
    2. If no fingerprint, fall back to git changed-files set.

    Args:
        code_file_path: Absolute path to the code file.
        repo_root: Absolute path to the repository root.
        git_changed_files: Set of absolute paths from get_git_changed_files().

    Returns:
        (is_changed, reason) tuple.
    """
    basename, language = derive_basename_and_language(code_file_path, repo_root)
    if basename is None or language is None:
        return False, "unknown extension"

    fingerprint = read_fingerprint(basename, language)

    if fingerprint is not None:
        stored_hash = fingerprint.code_hash
        if stored_hash is None:
            return True, "fingerprint exists but has no code_hash"

        current_hash = calculate_sha256(Path(code_file_path))
        if current_hash is None:
            return False, "could not compute current hash"

        if current_hash != stored_hash:
            return True, "code hash differs from fingerprint"
        return False, "code hash matches fingerprint"

    # No fingerprint — fall back to git
    abs_path = os.path.abspath(code_file_path)
    if abs_path in git_changed_files:
        return True, "no fingerprint, file in git changed set"
    return False, "no fingerprint, file not in git changed set"


def sync_code_main(
    ctx: click.Context,
    directory: Optional[str],
    extensions: Optional[str],
    simple: bool,
    base_branch: str,
) -> Optional[Tuple[str, float, str]]:
    """Orchestrate the sync-code process.

    Scans the repo for code/prompt pairs, filters to changed-only files,
    and runs update_file_pair on each.

    Args:
        ctx: Click context with verbose/quiet/strength/temperature in obj.
        directory: Optional directory to scan (defaults to repo root).
        extensions: Comma-separated file extensions to filter.
        simple: If True, skip agentic routing.
        base_branch: Git branch to compare against for fallback detection.

    Returns:
        Tuple of (summary_message, total_cost, models_string) or None.
    """
    quiet = ctx.obj.get("quiet", False)

    try:
        repo_obj = git.Repo(os.getcwd(), search_parent_directories=True)
        repo_root = repo_obj.working_tree_dir
    except git.InvalidGitRepositoryError:
        rprint("[bold red]Error:[/bold red] sync-code requires a Git repository.")
        return None

    scan_dir = os.path.abspath(directory) if directory else repo_root
    pairs = find_and_resolve_all_pairs(scan_dir, quiet, extensions)

    if not pairs:
        if not quiet:
            rprint("[info]No scannable code files found.[/info]")
        return None

    # Build git changed-files set for fallback detection
    git_changed_files = get_git_changed_files(repo_root, base_branch)

    # Filter to changed-only pairs
    changed_pairs: List[Tuple[str, str]] = []
    for prompt_path, code_path in pairs:
        changed, reason = is_code_changed(code_path, repo_root, git_changed_files)
        if changed:
            changed_pairs.append((prompt_path, code_path))

    if not changed_pairs:
        if not quiet:
            rprint("[info]No changed code files detected. Everything is in sync.[/info]")
        return None

    if not quiet:
        rprint(
            f"[info]Found {len(changed_pairs)} changed file(s) "
            f"out of {len(pairs)} total pairs.[/info]"
        )

    results: List[Dict[str, Any]] = []
    total_cost = 0.0

    progress = Progress(
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}", justify="right"),
        BarColumn(bar_width=None),
        TextColumn("[progress.percentage]{task.percentage:>3.1f}%"),
        TextColumn("\u2022"),
        TimeRemainingColumn(),
        TextColumn("\u2022"),
        TextColumn("Total Cost: $[bold green]{task.fields[total_cost]:.6f}[/bold green]"),
        console=console,
        transient=True,
    )

    with progress:
        task = progress.add_task(
            "Syncing code \u2192 prompts...",
            total=len(changed_pairs),
            total_cost=0.0,
        )

        for prompt_path, code_path in changed_pairs:
            relative_path = os.path.relpath(code_path, repo_root)
            progress.update(task, description=f"Processing [path]{relative_path}[/path]")

            result = update_file_pair(prompt_path, code_path, ctx, repo_obj, simple=simple)
            results.append(result)

            total_cost += result.get("cost", 0.0)
            progress.update(task, advance=1, total_cost=total_cost)

    # Summary table
    table = Table(show_header=True, header_style="bold magenta")
    table.add_column("Prompt File", style="dim", width=50)
    table.add_column("Status")
    table.add_column("Cost", justify="right")
    table.add_column("Model")
    table.add_column("Error", style="error")

    models_used: set = set()
    for res in sorted(results, key=lambda x: x["prompt_file"]):
        table.add_row(
            os.path.relpath(res["prompt_file"], repo_root),
            res["status"],
            f"${res['cost']:.6f}",
            res["model"],
            res["error"],
        )
        if res["model"]:
            models_used.add(res["model"])

    console.print("\n[bold]Sync-Code Summary[/bold]")
    console.print(table)
    console.print(f"\n[bold]Total Estimated Cost: ${total_cost:.6f}[/bold]")

    final_model_str = ", ".join(sorted(models_used)) if models_used else "N/A"
    return "Sync-code complete.", total_cost, final_model_str
