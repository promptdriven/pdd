"""Sanitize, snapshot, hash, and verify closed issue-1995 evidence."""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import shutil
import sys
from pathlib import Path


SECRET_PATTERNS = (
    re.compile(rb"gh[pousr]_[A-Za-z0-9]{20,}"),
    re.compile(rb"AIza[0-9A-Za-z_-]{20,}"),
    re.compile(rb"sk-[A-Za-z0-9_-]{20,}"),
    re.compile(rb"-----BEGIN [A-Z ]*PRIVATE KEY-----"),
    re.compile(rb"PDD_ADMIN_ID_TOKEN="),
)


def _files(root: Path) -> list[Path]:
    paths = sorted(root.rglob("*"))
    unsafe = [path for path in paths if path.is_symlink() or not path.is_file()]
    if unsafe:
        raise ValueError(f"evidence contains non-regular paths: {unsafe}")
    return paths


def _digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _scan(paths: list[Path]) -> None:
    for path in paths:
        content = path.read_bytes()
        if any(pattern.search(content) for pattern in SECRET_PATTERNS):
            raise ValueError(f"evidence secret-pattern scan failed: {path.name}")


def seal(source: Path, destination: Path) -> None:
    """Copy sanitized regular files, hash them, and make the snapshot read-only."""
    if destination.exists():
        raise ValueError("sealed destination already exists")
    source_files = _files(source)
    _scan(source_files)
    temporary = destination.with_name(destination.name + ".tmp")
    if temporary.exists():
        shutil.rmtree(temporary)
    shutil.copytree(source, temporary, symlinks=False)
    copied = _files(temporary)
    manifest = temporary / "SHA256SUMS"
    lines = [
        f"{_digest(path)}  {path.relative_to(temporary).as_posix()}\n"
        for path in copied
    ]
    manifest.write_text("".join(lines), encoding="utf-8")
    for path in _files(temporary):
        path.chmod(0o444)
    for directory, _, _ in os.walk(temporary, topdown=False):
        Path(directory).chmod(0o555)
    temporary.rename(destination)


def verify(root: Path) -> None:
    """Fail unless every sealed byte and path matches its manifest."""
    manifest = root / "SHA256SUMS"
    entries = manifest.read_text(encoding="utf-8").splitlines()
    expected_paths = []
    for entry in entries:
        digest, relative = entry.split("  ", 1)
        path = root / relative
        if not path.is_file() or path.is_symlink() or _digest(path) != digest:
            raise ValueError(f"manifest mismatch: {relative}")
        expected_paths.append(relative)
    actual_paths = [
        path.relative_to(root).as_posix() for path in _files(root) if path != manifest
    ]
    if expected_paths != actual_paths:
        raise ValueError("manifest path inventory mismatch")
    _scan([root / relative for relative in actual_paths])


def main() -> int:
    """Dispatch the seal or verify operation."""
    parser = argparse.ArgumentParser()
    parser.add_argument("operation", choices=("seal", "verify"))
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path, nargs="?")
    arguments = parser.parse_args()
    try:
        if arguments.operation == "seal":
            if arguments.destination is None:
                raise ValueError("seal requires a destination")
            seal(arguments.source, arguments.destination)
            verify(arguments.destination)
        else:
            if arguments.destination is not None:
                raise ValueError("verify accepts one directory")
            verify(arguments.source)
    except (OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
