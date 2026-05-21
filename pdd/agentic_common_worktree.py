"""pdd/agentic_common_worktree.py

Shared worktree setup, git-scope guards, and agentic output parsing helpers
used by multiple orchestrators (bug, split, change, etc.).
"""
from __future__ import annotations

import hashlib
import logging
import os
import re
import shutil
import subprocess
from pathlib import Path
from typing import List, Mapping, Optional, Set, Tuple

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


def _hash_file_content(path: Path) -> Optional[str]:
    """Return the SHA-256 hex digest of *path*'s bytes, or ``None`` if the
    file cannot be read (missing, permission denied, IO error)."""
    try:
        with open(str(path), "rb") as fh:
            return hashlib.sha256(fh.read()).hexdigest()
    except (OSError, FileNotFoundError):
        return None


def revert_out_of_scope_changes_with_dirs(
    cwd: Path,
    allowed_dirs: set[str],
    allowed_files: set[Path],
    pre_snapshot: Optional[Mapping[str, Tuple[str, Optional[str]]]] = None,
    strict: bool = False,
) -> List[Path]:
    """Revert/remove any changed or new files that fall outside *allowed_dirs*
    and *allowed_files*.

    * Tracked out-of-scope changes are reverted via
      ``git checkout HEAD -- <file>``.
    * Untracked out-of-scope files are removed via :func:`os.remove`.

    When *pre_snapshot* is provided, it maps POSIX-relative path →
    ``(porcelain_status, content_sha256_hex_or_None)`` captured BEFORE the
    caller's "change of interest" began (e.g. before Step 9's LLM ran). Any
    current entry whose ``(status, content_sha256)`` matches the snapshot
    exactly is skipped — its existing state is by-construction the contract,
    so it is not part of the change set the caller wants to enforce. A status
    match with a CHANGED content hash is still treated as a new mutation
    (e.g. Step 8.5 left a tracked file ``M`` and Step 9 modified it again).
    New entries, status-changed entries, and content-changed entries are all
    subject to the allowlist.

    Deletions of pre-snapshot files (paths present in *pre_snapshot* but
    absent from the current ``git status``) are detected and treated as
    out-of-scope mutations unless the path is allowlisted. Tracked deletions
    are restored via ``git checkout HEAD -- <file>``. Untracked deletions
    (pre-status ``??``) cannot be restored — we have no stored content — so
    they are added to the returned list with a warning so the caller can
    surface the violation; Step 8.5 is idempotent and will recreate the file
    on the next invocation.

    When *strict* is ``False`` (the default), internal failures (subprocess
    timeouts, non-zero ``git`` returns, OSErrors during ``os.remove`` or
    ``git`` calls) are logged and the function returns whatever was reverted
    so far. This preserves the silent-fail behavior callers like ``e2e_fix``
    rely on.

    When *strict* is ``True``, the same failures are RAISED rather than
    swallowed so the caller can treat the guard as workflow-stopping (the
    Step 9 caller in ``agentic_change_orchestrator`` uses this). See issue
    #1123 round-3 — Codex flagged that returning ``[]`` on an enforcement
    failure lets the orchestrator advance as if everything was clean.

    Returns the list of reverted / removed paths (relative to *cwd*).
    """
    reverted: List[Path] = []

    # Use the structured ``--porcelain=v1 -z`` parser so staged renames
    # surface BOTH the new and old paths as discrete fields. The earlier
    # text-mode parser kept only the new side, which let an out-of-scope
    # old path (e.g. ``scripts/external.py`` renamed into ``pdd/``)
    # silently escape the scope guard. See issue #1080.
    from pdd.git_porcelain import parse_porcelain_z  # local import: avoid cycles

    try:
        result = subprocess.run(
            ["git", "status", "--porcelain=v1", "-z", "-u"],
            cwd=str(cwd),
            capture_output=True,
            timeout=30,
        )
        if result.returncode != 0:
            stderr_text = result.stderr.decode("utf-8", errors="replace").strip()
            logger.warning("git status failed (rc=%d): %s", result.returncode, stderr_text)
            if strict:
                raise OSError(
                    f"git status failed (rc={result.returncode}): {stderr_text}"
                )
            return reverted
    except subprocess.TimeoutExpired:
        logger.warning("git status timed out")
        if strict:
            raise
        return reverted
    except OSError as exc:
        logger.warning("OS error running git status: %s", exc)
        if strict:
            raise
        return reverted

    def _path_in_scope(rel: str) -> bool:
        for prefix in allowed_dirs:
            if rel.startswith(prefix):
                return True
        abs_path = (cwd / rel).resolve()
        return abs_path in allowed_files

    # Track which pre_snapshot keys we observe in the post-status pass so we
    # can detect deletions afterwards (entries present pre-Step-9 but absent
    # from post-status are deletions).
    seen_in_post: Set[str] = set()

    for entry in parse_porcelain_z(result.stdout):
        status = entry.status
        new_rel = entry.path
        old_rel = entry.old_path

        seen_in_post.add(new_rel)
        if old_rel is not None:
            seen_in_post.add(old_rel)

        # Pre-snapshot pass-through: if the caller supplied a baseline and
        # this entry's (path, status) matches the baseline AND the file's
        # current content hash matches what was captured at snapshot time,
        # the change predates the window the caller wants enforced — skip
        # it. A status match with a DIFFERENT content hash is a Step-9
        # mutation on top of Step-8.5's work and must still be enforced.
        #
        # We hash the file from disk BEFORE any revert action below, so the
        # value reflects the current state of the file rather than its
        # post-revert state.
        if pre_snapshot is not None:
            current_hash = _hash_file_content(cwd / new_rel)
            if pre_snapshot.get(new_rel) == (status, current_hash):
                continue

        is_rename = old_rel is not None and "R" in status
        is_copy = old_rel is not None and "C" in status

        # Renames are out-of-scope if EITHER side is out of scope: the
        # new path currently exists on disk, and the old path is removed
        # by the staged rename. Copies are different: the old path is a
        # source reference only, not a modified path, so scope and revert
        # decisions are based on the copied destination.
        if is_rename:
            new_in = _path_in_scope(new_rel)
            old_in = _path_in_scope(old_rel)
            if new_in and old_in:
                continue
        elif is_copy:
            if _path_in_scope(new_rel):
                continue
        else:
            if _path_in_scope(new_rel):
                continue

        is_untracked = status == "??"

        if is_untracked:
            try:
                os.remove(str(cwd / new_rel))
                logger.info("Removed untracked out-of-scope file: %s", new_rel)
                reverted.append(Path(new_rel))
            except OSError as exc:
                logger.warning("Failed to remove %s: %s", new_rel, exc)
                if strict:
                    raise
        elif is_rename:
            # Rename: unstage both sides, restore the old path from HEAD,
            # and delete the new path so the rename is fully undone.
            paths_to_reset = [new_rel, old_rel]
            try:
                subprocess.run(
                    ["git", "reset", "HEAD", "--"] + paths_to_reset,
                    cwd=str(cwd),
                    capture_output=True,
                    timeout=30,
                )
                checkout = subprocess.run(
                    ["git", "checkout", "HEAD", "--", old_rel],
                    cwd=str(cwd),
                    capture_output=True,
                    timeout=30,
                )
                try:
                    (cwd / new_rel).unlink()
                except FileNotFoundError:
                    pass
                except OSError as exc:
                    logger.warning("Failed to remove rename new-side %s: %s", new_rel, exc)
                    if strict:
                        raise
                if checkout.returncode == 0:
                    logger.info(
                        "Reverted out-of-scope rename: %s -> %s", old_rel, new_rel,
                    )
                    reverted.append(Path(old_rel))
                    reverted.append(Path(new_rel))
                else:
                    stderr_text = checkout.stderr.decode("utf-8", errors="replace").strip()
                    logger.warning(
                        "Failed to revert rename %s -> %s: %s",
                        old_rel, new_rel, stderr_text,
                    )
                    if strict:
                        raise OSError(
                            f"git checkout HEAD -- {old_rel} failed: {stderr_text}"
                        )
            except subprocess.TimeoutExpired:
                logger.warning("Timed out reverting rename %s -> %s", old_rel, new_rel)
                if strict:
                    raise
            except OSError as exc:
                logger.warning("OS error reverting rename %s -> %s: %s", old_rel, new_rel, exc)
                if strict:
                    raise
        elif is_copy:
            # Copy: only the destination is changed. The source path is
            # informational and must not be reset/restored/removed.
            try:
                subprocess.run(
                    ["git", "reset", "HEAD", "--", new_rel],
                    cwd=str(cwd),
                    capture_output=True,
                    timeout=30,
                )
                try:
                    (cwd / new_rel).unlink()
                except FileNotFoundError:
                    pass
                except OSError as exc:
                    logger.warning("Failed to remove copy destination %s: %s", new_rel, exc)
                    if strict:
                        raise
                logger.info("Reverted out-of-scope copy destination: %s", new_rel)
                reverted.append(Path(new_rel))
            except subprocess.TimeoutExpired:
                logger.warning("Timed out reverting copy destination %s", new_rel)
                if strict:
                    raise
            except OSError as exc:
                logger.warning("OS error reverting copy destination %s: %s", new_rel, exc)
                if strict:
                    raise
        else:
            try:
                checkout = subprocess.run(
                    ["git", "checkout", "HEAD", "--", new_rel],
                    cwd=str(cwd),
                    capture_output=True,
                    timeout=30,
                )
                if checkout.returncode == 0:
                    logger.info(
                        "Reverted out-of-scope tracked change: %s",
                        new_rel,
                    )
                    reverted.append(Path(new_rel))
                else:
                    stderr_text = checkout.stderr.decode("utf-8", errors="replace").strip()
                    logger.warning("Failed to revert %s: %s", new_rel, stderr_text)
                    if strict:
                        raise OSError(
                            f"git checkout HEAD -- {new_rel} failed: {stderr_text}"
                        )
            except subprocess.TimeoutExpired:
                logger.warning("Timed out reverting %s", new_rel)
                if strict:
                    raise
            except OSError as exc:
                logger.warning("OS error reverting %s: %s", new_rel, exc)
                if strict:
                    raise

    # ------------------------------------------------------------------
    # Deletion detection (issue #1123 round-3, blocker B)
    #
    # Paths present in pre_snapshot but absent from post-status must be
    # considered: Step 9 may have deleted a file that Step 8.5 created or
    # modified. Allowlisted deletions are skipped; tracked deletions are
    # restored from HEAD; untracked deletions cannot be auto-restored
    # (no stored content) and are surfaced as unrecoverable violations.
    # ------------------------------------------------------------------
    if pre_snapshot:
        for rel in list(pre_snapshot.keys()):
            if rel in seen_in_post:
                continue
            # If the file is on disk, this entry simply went back to clean
            # (e.g. Step 9 reverted a Step 8.5 modification) — that is a
            # mutation we already treat via the main-loop iteration on the
            # POST status. If it's gone, it was deleted.
            if (cwd / rel).exists():
                continue
            if _path_in_scope(rel):
                # Allowed deletion — skip.
                continue
            pre_entry = pre_snapshot.get(rel)
            pre_status_code = pre_entry[0] if pre_entry is not None else ""
            if pre_status_code == "??":
                # Untracked at snapshot time: no content stored, cannot
                # auto-restore. Surface it so the caller can fail the
                # workflow; Step 8.5 is idempotent so it will recreate
                # the file on the next invocation.
                logger.warning(
                    "Untracked file deleted out-of-scope: %s "
                    "(cannot auto-restore — flag as violation)",
                    rel,
                )
                reverted.append(Path(rel))
            else:
                # Tracked at snapshot time: restore from HEAD.
                try:
                    checkout = subprocess.run(
                        ["git", "checkout", "HEAD", "--", rel],
                        cwd=str(cwd),
                        capture_output=True,
                        timeout=30,
                    )
                    if checkout.returncode == 0:
                        logger.info(
                            "Restored out-of-scope deletion: %s", rel,
                        )
                        reverted.append(Path(rel))
                    else:
                        stderr_text = checkout.stderr.decode("utf-8", errors="replace").strip()
                        logger.warning(
                            "Failed to restore deletion %s: %s", rel, stderr_text,
                        )
                        if strict:
                            raise OSError(
                                f"git checkout HEAD -- {rel} failed: {stderr_text}"
                            )
                except subprocess.TimeoutExpired:
                    logger.warning("Timed out restoring deletion %s", rel)
                    if strict:
                        raise
                except OSError as exc:
                    logger.warning("OS error restoring deletion %s: %s", rel, exc)
                    if strict:
                        raise

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
