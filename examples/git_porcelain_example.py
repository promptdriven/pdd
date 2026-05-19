"""Example usage of pdd.git_porcelain.

Demonstrates parsing ``git status --porcelain=v1 -z`` output for plain
modifications, staged renames, untracked files, and paths with embedded
spaces — all of which the legacy text-mode parser handled incorrectly.
See issue #1080 for the audit that motivated this helper.
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.git_porcelain import (  # noqa: E402
    PorcelainEntry,
    iter_changed_paths,
    parse_porcelain_z,
)


def example_basic_modify_and_untracked() -> None:
    """Plain modifications and untracked records."""
    print("=== parse_porcelain_z: modify + untracked ===")
    # ``-z`` records are NUL-separated bytes with no C-quoting and no
    # trailing NUL on the last record.
    stdout = b" M pdd/module.py\x00?? scratch.txt\x00"
    entries = parse_porcelain_z(stdout)
    for entry in entries:
        print(f"  status={entry.status!r} path={entry.path!r} old_path={entry.old_path!r}")
    print()


def example_staged_rename() -> None:
    """Staged rename: git emits the new path, then the old path as a
    SECOND NUL-terminated record. The parser exposes both sides."""
    print("=== parse_porcelain_z: staged rename ===")
    stdout = b"R  pdd/new_name.py\x00pdd/old_name.py\x00"
    entries = parse_porcelain_z(stdout)
    for entry in entries:
        print(f"  status={entry.status!r} path={entry.path!r} old_path={entry.old_path!r}")
    print()


def example_path_with_spaces_and_literal_arrow() -> None:
    """Paths containing spaces or a literal ' -> ' substring round-trip
    verbatim under ``-z`` — the old text-mode parser was lossy here."""
    print("=== parse_porcelain_z: exotic path bytes ===")
    stdout = (
        b" M docs/quick start.md\x00"           # space in path
        b"?? notes/foo -> bar.txt\x00"          # literal ' -> ' in path
    )
    entries = parse_porcelain_z(stdout)
    for entry in entries:
        print(f"  status={entry.status!r} path={entry.path!r}")
    print()


def example_iter_changed_paths() -> None:
    """``iter_changed_paths`` yields both sides of a rename."""
    print("=== iter_changed_paths ===")
    entries = [
        PorcelainEntry(status=" M", path="pdd/module.py"),
        PorcelainEntry(status="R ", path="pdd/new_name.py", old_path="pdd/old_name.py"),
    ]
    for path in iter_changed_paths(entries):
        print(f"  {path}")
    print()


def main() -> None:
    example_basic_modify_and_untracked()
    example_staged_rename()
    example_path_with_spaces_and_literal_arrow()
    example_iter_changed_paths()
    print("All examples completed successfully.")


if __name__ == "__main__":
    main()
