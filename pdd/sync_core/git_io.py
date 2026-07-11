"""Read-only Git object helpers for protected base/head evaluation."""

import subprocess
from pathlib import Path, PurePosixPath


def read_git_blob(root: Path, ref: str, path: PurePosixPath) -> bytes | None:
    """Read a blob from an immutable tree, returning None when it is absent."""
    result = subprocess.run(
        ["git", "show", f"{ref}:{path.as_posix()}"],
        cwd=root,
        capture_output=True,
        check=False,
    )
    return result.stdout if result.returncode == 0 else None


def read_git_mode(root: Path, ref: str, path: PurePosixPath) -> str | None:
    """Return the exact tree mode for one path without materializing it."""
    result = subprocess.run(
        ["git", "ls-tree", ref, "--", path.as_posix()],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0 or not result.stdout.strip():
        return None
    fields = result.stdout.split(None, 3)
    return fields[0] if len(fields) == 4 else None


def resolve_git_commit(root: Path, ref: str) -> str:
    """Resolve one exact commit or fail closed."""
    result = subprocess.run(
        ["git", "rev-parse", "--verify", f"{ref}^{{commit}}"],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0 or not result.stdout.strip():
        raise ValueError(f"cannot resolve Git commit: {ref}")
    return result.stdout.strip()
