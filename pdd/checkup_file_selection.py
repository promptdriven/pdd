"""Discover source files for ``pdd checkup simplify``."""
from __future__ import annotations

import os
import subprocess
from pathlib import Path
from typing import List, Optional, Sequence, Set

from .get_language import get_language
from .update_main import (
    _SKIP_EXTENSIONS,
    _SKIP_FILENAMES,
    _has_meaningful_code,
    _has_skip_suffix,
    _is_pddignored,
    _load_pddignore,
)


# Deterministic fallback when PDD_PATH / language CSV is unavailable.
_SIMPLIFY_EXTENSIONS = frozenset({
    ".py",
    ".pyi",
    ".ts",
    ".tsx",
    ".js",
    ".jsx",
    ".go",
    ".rs",
    ".java",
    ".kt",
    ".swift",
    ".rb",
    ".cs",
    ".cpp",
    ".c",
    ".h",
    ".hpp",
})


def _is_code_extension(extension: str) -> bool:
    ext = extension.lower()
    if not ext.startswith("."):
        ext = f".{ext}"
    if ext in _SIMPLIFY_EXTENSIONS:
        return True
    try:
        return bool(get_language(ext))
    except ValueError:
        return False

_DEFAULT_MAX_FILES = 20

_HARD_EXCLUDE_PREFIXES = (
    ".pdd/evidence/",
    ".pdd/meta/",
    ".pdd/backups/",
    "dist/",
    "build/",
    "node_modules/",
)

_HARD_EXCLUDE_BASENAMES = {
    "package-lock.json",
    "pnpm-lock.yaml",
    "yarn.lock",
    "poetry.lock",
    "Pipfile.lock",
}


def resolve_simplify_repo_root(start: Path) -> Path:
    """Return the git repository root containing ``start``."""
    return _repo_root(start)


def _repo_root(start: Path) -> Path:
    current = start.resolve()
    if current.is_file():
        current = current.parent
    while True:
        if (current / ".git").is_dir():
            return current
        parent = current.parent
        if parent == current:
            return start.resolve() if start.is_dir() else start.parent.resolve()
        current = parent


def _git_name_only(args: Sequence[str], cwd: Path) -> List[str]:
    try:
        result = subprocess.run(
            ["git", *args],
            capture_output=True,
            text=True,
            cwd=cwd,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return []
    if result.returncode != 0:
        return []
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def _rel_paths_from_git(
    repo_root: Path,
    *,
    since: Optional[str] = None,
    staged: bool = False,
) -> List[str]:
    if staged:
        return _git_name_only(["diff", "--cached", "--name-only"], repo_root)
    if since:
        return _git_name_only(["diff", "--name-only", since], repo_root)
    return []


def _list_tracked_under(repo_root: Path, subpath: Optional[Path]) -> List[str]:
    args = ["ls-files", "--cached", "--others", "--exclude-standard"]
    if subpath is not None:
        rel = subpath.resolve().relative_to(repo_root.resolve()).as_posix()
        if rel == ".":
            rel = ""
        if rel:
            args.extend(["--", rel])
    try:
        result = subprocess.run(
            ["git", *args],
            capture_output=True,
            text=True,
            cwd=repo_root,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return []
    if result.returncode != 0:
        return []
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def _list_local_changes_under(repo_root: Path, subpath: Optional[Path]) -> List[str]:
    args = ["diff", "--name-only", "HEAD"]
    if subpath is not None:
        rel = subpath.resolve().relative_to(repo_root.resolve()).as_posix()
        if rel and rel != ".":
            args.extend(["--", rel])
    changed = _git_name_only(args, repo_root)
    untracked_args = ["ls-files", "--others", "--exclude-standard"]
    if subpath is not None:
        rel = subpath.resolve().relative_to(repo_root.resolve()).as_posix()
        if rel and rel != ".":
            untracked_args.extend(["--", rel])
    changed.extend(_git_name_only(untracked_args, repo_root))
    return list(dict.fromkeys(changed))


def _is_hard_excluded(rel_posix: str) -> bool:
    if rel_posix.startswith(".pdd/") and not rel_posix.startswith(".pdd/backups/"):
        if rel_posix.startswith(".pdd/evidence/") or rel_posix.startswith(".pdd/meta/"):
            return True
    for prefix in _HARD_EXCLUDE_PREFIXES:
        if rel_posix.startswith(prefix):
            return True
    base = os.path.basename(rel_posix)
    if base in _HARD_EXCLUDE_BASENAMES:
        return True
    return False


def _is_simplify_candidate(  # pylint: disable=too-many-return-statements
    abs_path: str,
    repo_root: Path,
    pddignore_patterns: List[str],
    pddignore_root: str,
) -> bool:
    if not os.path.isfile(abs_path):
        return False
    rel = os.path.relpath(abs_path, repo_root).replace("\\", "/")
    if _is_hard_excluded(rel):
        return False
    ext = os.path.splitext(abs_path)[1]
    ext_lower = ext.lower()
    if not _is_code_extension(ext):
        return False
    if abs_path.endswith(".prompt"):
        return False
    if ext_lower in _SKIP_EXTENSIONS:
        return False
    if os.path.basename(abs_path) in _SKIP_FILENAMES:
        return False
    if _has_skip_suffix(abs_path):
        return False
    if _is_pddignored(abs_path, pddignore_root, pddignore_patterns):
        return False
    return _has_meaningful_code(abs_path)


def discover_simplify_targets(
    *,
    path: Optional[Path] = None,
    since: Optional[str] = None,
    staged: bool = False,
    max_files: int = _DEFAULT_MAX_FILES,
    cwd: Optional[Path] = None,
) -> tuple[Path, List[Path]]:
    """Return ``(repo_root, selected_files)`` for a simplify run."""
    if since and staged:
        raise ValueError("--since and --staged are mutually exclusive")

    start = (path or cwd or Path.cwd()).resolve()
    repo_root = _repo_root(start)

    rel_candidates: List[str] = []
    if since or staged:
        rel_candidates = _rel_paths_from_git(repo_root, since=since, staged=staged)
    elif path is not None:
        if path.is_file():
            rel_candidates = [os.path.relpath(path.resolve(), repo_root).replace("\\", "/")]
        else:
            rel_candidates = _list_local_changes_under(repo_root, path.resolve())
            if not rel_candidates:
                rel_candidates = _list_tracked_under(repo_root, path.resolve())
    else:
        rel_candidates = _list_local_changes_under(repo_root, None)
        if not rel_candidates:
            rel_candidates = _list_tracked_under(repo_root, None)

    pddignore_patterns, pddignore_root = _load_pddignore(str(repo_root))

    selected: List[Path] = []
    seen: Set[str] = set()
    for rel in rel_candidates:
        if rel in seen:
            continue
        seen.add(rel)
        abs_path = os.path.join(repo_root, rel)
        if not _is_simplify_candidate(abs_path, repo_root, pddignore_patterns, pddignore_root):
            continue
        selected.append(Path(abs_path))
        if len(selected) >= max_files:
            break

    return repo_root, selected
