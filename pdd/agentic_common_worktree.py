"""pdd/agentic_common_worktree.py

Shared worktree setup, git-scope guards, and agentic output parsing helpers
used by multiple orchestrators (bug, split, change, etc.).
"""
from __future__ import annotations

import logging
import os
import re
import shutil
import subprocess
from pathlib import Path
from typing import List, Optional, Set, Tuple

from rich.console import Console

console = Console()
logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------


def get_git_root(cwd: Path) -> Optional[Path]:
    """Return the repository root via ``git rev-parse --show-toplevel``, or
    ``None`` on failure."""
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode == 0 and result.stdout.strip():
            return Path(result.stdout.strip())
        return None
    except (subprocess.TimeoutExpired, OSError):
        return None


def worktree_exists(cwd: Path, worktree_path: Path) -> bool:
    """Return ``True`` if *worktree_path* appears in the porcelain worktree
    listing of the repository that contains *cwd*."""
    git_root = get_git_root(cwd)
    if git_root is None:
        return False
    try:
        result = subprocess.run(
            ["git", "worktree", "list", "--porcelain"],
            cwd=str(git_root),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode != 0:
            return False
        resolved_target = worktree_path.resolve()
        for line in result.stdout.splitlines():
            if line.startswith("worktree "):
                listed_path = Path(line[len("worktree "):]).resolve()
                if listed_path == resolved_target:
                    return True
        return False
    except (subprocess.TimeoutExpired, OSError):
        return False


def branch_exists(cwd: Path, branch: str) -> bool:
    """Return ``True`` if *branch* exists as a local branch."""
    try:
        result = subprocess.run(
            ["git", "show-ref", "--verify", f"refs/heads/{branch}"],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=30,
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, OSError):
        return False


def remove_worktree(cwd: Path, worktree_path: Path) -> Tuple[bool, str]:
    """Remove a worktree via ``git worktree remove --force``.

    Returns ``(True, "")`` on success or ``(False, error_message)`` on
    failure.
    """
    try:
        result = subprocess.run(
            ["git", "worktree", "remove", "--force", str(worktree_path)],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=60,
        )
        if result.returncode == 0:
            return (True, "")
        return (False, result.stderr.strip())
    except subprocess.TimeoutExpired:
        return (False, "Timed out removing worktree")
    except OSError as exc:
        return (False, str(exc))


def delete_branch(cwd: Path, branch: str) -> Tuple[bool, str]:
    """Force-delete a local branch via ``git branch -D``.

    Returns ``(True, "")`` on success or ``(False, error_message)`` on
    failure.
    """
    try:
        result = subprocess.run(
            ["git", "branch", "-D", branch],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode == 0:
            return (True, "")
        return (False, result.stderr.strip())
    except subprocess.TimeoutExpired:
        return (False, "Timed out deleting branch")
    except OSError as exc:
        return (False, str(exc))


def resolve_main_ref(git_root: Path) -> str:
    """Return the commit hash of the first resolvable ref among
    ``origin/main``, ``origin/master``, ``main``, ``master``.

    Falls back to ``"HEAD"`` if none resolve.
    """
    for ref in ("origin/main", "origin/master", "main", "master"):
        try:
            result = subprocess.run(
                ["git", "rev-parse", "--verify", ref],
                cwd=str(git_root),
                capture_output=True,
                text=True,
                timeout=30,
            )
            if result.returncode == 0 and result.stdout.strip():
                return result.stdout.strip()
        except (subprocess.TimeoutExpired, OSError):
            continue
    return "HEAD"


# ---------------------------------------------------------------------------
# Worktree lifecycle
# ---------------------------------------------------------------------------


def setup_worktree(
    cwd: Path,
    issue_number: int,
    quiet: bool,
    *,
    resume_existing: bool = False,
    branch_prefix: str = "fix",
    worktree_prefix: str = "fix",
    base_ref: Optional[str] = None,
) -> Tuple[Optional[Path], Optional[str]]:
    """Create (or resume) an isolated git worktree for an issue.

    Worktree directory:
        ``<git_root>/.pdd/worktrees/{worktree_prefix}-issue-{issue_number}/``

    Branch name:
        ``{branch_prefix}/issue-{issue_number}``

    ``base_ref`` sets the commit the new branch is based on. Defaults to
    the first resolvable ref among origin/main, origin/master, main, master.
    Pass ``"HEAD"`` to base the branch on the caller's current commit (correct
    for stacked PRs or splits on a feature branch).

    Returns ``(worktree_path, None)`` on success or ``(None, error_msg)`` on
    failure.
    """
    git_root = get_git_root(cwd)
    if git_root is None:
        return (None, "Could not determine git root directory")

    branch_name = f"{branch_prefix}/issue-{issue_number}"
    worktree_dir = f"{worktree_prefix}-issue-{issue_number}"
    worktree_path = git_root / ".pdd" / "worktrees" / worktree_dir

    # ------------------------------------------------------------------
    # 1. Clean up any existing worktree registration
    # ------------------------------------------------------------------
    if worktree_exists(git_root, worktree_path):
        ok, err = remove_worktree(git_root, worktree_path)
        if not ok:
            logger.warning("Failed to remove existing worktree: %s", err)

    # 2. Clean up leftover directory
    if worktree_path.exists():
        try:
            shutil.rmtree(str(worktree_path))
        except OSError as exc:
            logger.warning("Failed to remove worktree directory: %s", exc)

    # ------------------------------------------------------------------
    # 3. Resolve ref to base new branches on
    # ------------------------------------------------------------------
    main_ref = base_ref if base_ref is not None else resolve_main_ref(git_root)

    # ------------------------------------------------------------------
    # 4. Handle existing branch
    # ------------------------------------------------------------------
    use_existing_branch = False
    need_reset = False

    if branch_exists(git_root, branch_name):
        if resume_existing:
            use_existing_branch = True
        else:
            ok, err = delete_branch(git_root, branch_name)
            if not ok:
                logger.warning(
                    "Could not delete branch %s: %s — will reuse and reset",
                    branch_name,
                    err,
                )
                use_existing_branch = True
                need_reset = True

    # ------------------------------------------------------------------
    # 5. Ensure parent directory exists
    # ------------------------------------------------------------------
    worktree_path.parent.mkdir(parents=True, exist_ok=True)

    # ------------------------------------------------------------------
    # 6. Create the worktree
    # ------------------------------------------------------------------
    try:
        if use_existing_branch:
            cmd = [
                "git", "worktree", "add", "--force",
                str(worktree_path), branch_name,
            ]
        else:
            cmd = [
                "git", "worktree", "add", "-b", branch_name,
                str(worktree_path), main_ref,
            ]

        result = subprocess.run(
            cmd,
            cwd=str(git_root),
            capture_output=True,
            text=True,
            timeout=120,
        )
        if result.returncode != 0:
            error_detail = result.stderr.strip() or result.stdout.strip()
            return (None, f"git worktree add failed: {error_detail}")

        # Reset to main ref when we reused an undeletable branch
        if need_reset:
            reset_result = subprocess.run(
                ["git", "reset", "--hard", main_ref],
                cwd=str(worktree_path),
                capture_output=True,
                text=True,
                timeout=60,
            )
            if reset_result.returncode != 0:
                logger.warning(
                    "Failed to reset branch to main ref: %s",
                    reset_result.stderr.strip(),
                )

    except subprocess.TimeoutExpired:
        return (None, "Timed out creating worktree")
    except OSError as exc:
        return (None, f"OS error creating worktree: {exc}")

    if not quiet:
        console.print(f"[green]Worktree created at:[/green] {worktree_path}")

    return (worktree_path, None)


# ---------------------------------------------------------------------------
# Scope guards
# ---------------------------------------------------------------------------


def get_modified_and_untracked(cwd: Path) -> List[str]:
    """Return a combined list of modified tracked files and untracked files."""
    files: List[str] = []
    try:
        # Modified tracked files relative to HEAD
        diff_result = subprocess.run(
            ["git", "diff", "--name-only", "HEAD"],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if diff_result.returncode == 0 and diff_result.stdout.strip():
            files.extend(diff_result.stdout.strip().splitlines())

        # Untracked files
        ls_result = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard"],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if ls_result.returncode == 0 and ls_result.stdout.strip():
            files.extend(ls_result.stdout.strip().splitlines())
    except (subprocess.TimeoutExpired, OSError):
        pass
    # Deduplicate: a staged new file can appear in both git diff and
    # git ls-files --others.
    return list(dict.fromkeys(files))


def check_target_file_unchanged(
    cwd: Path,
    target_file: str,
    baseline_sha: Optional[str] = None,
) -> Tuple[bool, Optional[str]]:
    """Detect concurrent edits on *target_file* on ``origin/main``.

    * If *baseline_sha* is ``None`` the call is treated as establishing a
      baseline — returns ``(True, current_sha)``.
    * If *baseline_sha* is provided, compares it against the current SHA and
      returns ``(unchanged, current_sha)``.
    * On any git failure the function **fails open** — returns
      ``(True, None)`` so workflows are not blocked.
    """
    try:
        # Best-effort fetch — don't fail if network is unavailable
        subprocess.run(
            ["git", "fetch", "origin"],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=60,
        )

        main_ref = resolve_main_ref(cwd) or "origin/main"
        result = subprocess.run(
            ["git", "rev-parse", f"{main_ref}:{target_file}"],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode != 0:
            return (True, None)

        current_sha: str = result.stdout.strip()

        if baseline_sha is None:
            return (True, current_sha)

        unchanged = current_sha == baseline_sha
        return (unchanged, current_sha)

    except (subprocess.TimeoutExpired, OSError):
        return (True, None)


def revert_out_of_scope_changes_with_dirs(
    cwd: Path,
    allowed_dirs: set[str],
    allowed_files: set[Path],
) -> List[Path]:
    """Revert/remove any changed or new files that fall outside *allowed_dirs*
    and *allowed_files*.

    * Tracked out-of-scope changes are reverted via
      ``git checkout HEAD -- <file>``.
    * Untracked out-of-scope files are removed via :func:`os.remove`.

    Returns the list of reverted / removed paths (relative to *cwd*).
    """
    reverted: List[Path] = []

    try:
        result = subprocess.run(
            ["git", "status", "--porcelain", "-u"],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode != 0:
            logger.warning(
                "git status failed (rc=%d): %s",
                result.returncode,
                result.stderr.strip(),
            )
            return reverted
    except subprocess.TimeoutExpired:
        logger.warning("git status timed out")
        return reverted
    except OSError as exc:
        logger.warning("OS error running git status: %s", exc)
        return reverted

    for line in result.stdout.splitlines():
        if len(line) < 4:
            continue

        status = line[:2]
        filepath_raw = line[3:]

        # Handle renames: "R  old_name -> new_name"
        if " -> " in filepath_raw:
            filepath_raw = filepath_raw.split(" -> ")[-1]

        filepath_str = filepath_raw.strip().strip('"')

        # ------------------------------------------------------------------
        # Scope check
        # ------------------------------------------------------------------
        in_scope = False

        for prefix in allowed_dirs:
            if filepath_str.startswith(prefix):
                in_scope = True
                break

        if not in_scope:
            abs_path = (cwd / filepath_str).resolve()
            if abs_path in allowed_files:
                in_scope = True

        if in_scope:
            continue

        # ------------------------------------------------------------------
        # Out of scope — revert or remove
        # ------------------------------------------------------------------
        is_untracked = status == "??"
        rel_path = Path(filepath_str)

        if is_untracked:
            try:
                os.remove(str(cwd / filepath_str))
                logger.info("Removed untracked out-of-scope file: %s", filepath_str)
                reverted.append(rel_path)
            except OSError as exc:
                logger.warning("Failed to remove %s: %s", filepath_str, exc)
        else:
            try:
                checkout = subprocess.run(
                    ["git", "checkout", "HEAD", "--", filepath_str],
                    cwd=str(cwd),
                    capture_output=True,
                    text=True,
                    timeout=30,
                )
                if checkout.returncode == 0:
                    logger.info(
                        "Reverted out-of-scope tracked change: %s",
                        filepath_str,
                    )
                    reverted.append(rel_path)
                else:
                    logger.warning(
                        "Failed to revert %s: %s",
                        filepath_str,
                        checkout.stderr.strip(),
                    )
            except subprocess.TimeoutExpired:
                logger.warning("Timed out reverting %s", filepath_str)
            except OSError as exc:
                logger.warning("OS error reverting %s: %s", filepath_str, exc)

    return reverted


# ---------------------------------------------------------------------------
# Output parsing
# ---------------------------------------------------------------------------


def extract_block_marker(output: str, name: str) -> str:
    """Extract content between ``BEGIN_{name}`` and ``END_{name}`` markers.

    Marker matching is **case-insensitive**. Returns the stripped content
    between the first matching pair, or an empty string if no markers are
    found.
    """
    pattern = re.compile(
        rf"BEGIN_{re.escape(name)}\s*\n?(.*?)\n?\s*END_{re.escape(name)}",
        re.DOTALL | re.IGNORECASE,
    )
    match = pattern.search(output)
    if match is not None:
        return match.group(1).strip()
    return ""