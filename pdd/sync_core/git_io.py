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
