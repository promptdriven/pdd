"""Read-only Git object helpers for protected base/head evaluation."""

from dataclasses import dataclass
import subprocess
from pathlib import Path, PurePosixPath


@dataclass(frozen=True)
class GitObjectEntry:
    """Mode, type, and object identity for one path in an immutable tree."""

    mode: str
    object_type: str
    object_id: str


def read_git_blob(root: Path, ref: str, path: PurePosixPath) -> bytes | None:
    """Read a blob from an immutable tree, returning None when it is absent."""
    result = subprocess.run(
        ["git", "show", f"{ref}:{path.as_posix()}"],
        cwd=root,
        capture_output=True,
        check=False,
    )
    return result.stdout if result.returncode == 0 else None


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


def read_git_tree_entry(
    root: Path,
    ref: str,
    path: PurePosixPath,
) -> GitObjectEntry | None:
    """Read one path entry from an immutable tree without recursive fallback."""
    result = subprocess.run(
        ["git", "ls-tree", "-z", ref, "--", path.as_posix()],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0 or not result.stdout:
        return None
    record = result.stdout.split(b"\0", 1)[0]
    metadata, _path_bytes = record.split(b"\t", 1)
    mode, object_type, object_id = metadata.decode("ascii").split()
    return GitObjectEntry(mode, object_type, object_id)
