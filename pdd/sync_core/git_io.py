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


def read_git_blob_bounded(
    root: Path, ref: str, path: PurePosixPath, max_bytes: int
) -> bytes | None:
    """Read an immutable blob only after verifying its object size is bounded."""
    entry = read_git_tree_entry(root, ref, path)
    if entry is None:
        return None
    if entry.object_type != "blob":
        raise ValueError(f"Git object is not a blob: {path.as_posix()}")
    size_result = subprocess.run(
        ["git", "cat-file", "-s", entry.object_id],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    try:
        size = int(size_result.stdout.strip())
    except ValueError as exc:
        raise ValueError(
            f"cannot determine Git blob size: {path.as_posix()}"
        ) from exc
    if size_result.returncode != 0 or size < 0:
        raise ValueError(f"cannot determine Git blob size: {path.as_posix()}")
    if size > max_bytes:
        raise ValueError(
            f"Git blob exceeds {max_bytes}-byte limit: {path.as_posix()}"
        )
    result = subprocess.run(
        ["git", "cat-file", "blob", entry.object_id],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0 or len(result.stdout) != size:
        raise ValueError(f"cannot read Git blob safely: {path.as_posix()}")
    return result.stdout


def read_git_regular_blob(root: Path, ref: str, path: PurePosixPath) -> bytes | None:
    """Read a regular blob and reject symlinks, gitlinks, and special modes."""
    result = subprocess.run(
        ["git", "ls-tree", ref, "--", path.as_posix()],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0 or not result.stdout.strip():
        return None
    mode = result.stdout.split(None, 1)[0]
    if mode == "040000":
        return None
    if mode not in {"100644", "100755"}:
        raise ValueError(f"Git closure member is not a regular file: {path.as_posix()}")
    return read_git_blob(root, ref, path)


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
