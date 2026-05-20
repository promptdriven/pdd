"""Structured parser for ``git status --porcelain=v1 -z`` output.

The text-mode ``git status --porcelain`` output is lossy for paths
that contain shell-meaningful characters: paths with spaces, tabs,
embedded quotes, or non-ASCII bytes are C-style quoted, and a staged
rename is collapsed into a single literal ``"old -> new"`` string. Any
ad-hoc parser that does ``line[3:]`` and ``split(' -> ')`` silently
mishandles all of those cases.

This module provides a small structured parser for the ``-z`` variant,
which is the documented machine-readable format. ``-z`` emits records
joined by ``NUL`` (no C-style quoting, no trailing newline), and for
each ``R`` (rename) or ``C`` (copy) record emits the OLD path as a
SECOND ``NUL``-terminated record immediately after the new path.

The :func:`parse_porcelain_z` helper returns a sequence of
:class:`PorcelainEntry` records exposing:

* ``status`` — the two-character ``XY`` status field (e.g. ``"R "``,
  ``" M"``, ``"??"``).
* ``path``  — the new-or-only path (verbatim, no quoting artifacts).
* ``old_path`` — the previous path for renames/copies, or ``None`` for
  every other status. For copies this is the source path only; it is
  not itself a changed path.

Callers then decide per-call-site whether they need the new path only,
both old + new paths, or true rename-aware scope-guard semantics.

See issue #1080 for the audit that motivated this helper.
"""
from __future__ import annotations

import os
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, List, Optional, Sequence, Union


__all__ = [
    "PorcelainEntry",
    "parse_porcelain_z",
    "run_porcelain_z",
    "iter_changed_paths",
]


@dataclass(frozen=True)
class PorcelainEntry:
    """One parsed record from ``git status --porcelain=v1 -z``.

    Attributes:
        status: The two-character ``XY`` status field. The first
            character reflects the index/staging state, the second the
            worktree state. For renames/copies this is ``"R "``/``"RM"``
            etc. For untracked files this is ``"??"``.
        path: The new-or-only path, decoded with :func:`os.fsdecode`
            so byte paths round-trip on platforms where filenames are
            not UTF-8.
        old_path: The previous path for ``R``/``C`` records. For copy
            records this is the source path only; it is not itself
            changed. ``None`` for every other status.
    """

    status: str
    path: str
    old_path: Optional[str] = None


def _decode_path(raw: Union[bytes, str]) -> str:
    """Decode a path coming out of ``-z`` porcelain.

    ``-z`` emits raw bytes for paths (no C-quoting). We decode via
    :func:`os.fsdecode` so non-UTF-8 paths round-trip via the surrogate
    escape mechanism. Accepts ``str`` for callers that already decoded
    the stdout stream (e.g. ``subprocess.run(..., text=True)``).
    """
    if isinstance(raw, bytes):
        return os.fsdecode(raw)
    return raw


def parse_porcelain_z(
    stdout: Union[bytes, str],
) -> List[PorcelainEntry]:
    """Parse ``git status --porcelain=v1 -z`` output.

    ``-z`` terminates every record with a NUL (per ``git status`` docs:
    "Terminate entries with NUL, instead of LF"), so a trailing NUL is
    always present after the last record. Each record starts with a
    two-character status field, a single space, then the new-or-only
    path. For ``R`` or ``C`` records the OLD path follows as a separate
    NUL-terminated record.

    Args:
        stdout: Raw stdout bytes (preferred — preserves filenames that
            are not valid UTF-8) or a pre-decoded ``str``.

    Returns:
        A list of :class:`PorcelainEntry` records in the order git
        emitted them. An empty input yields an empty list.
    """
    if isinstance(stdout, bytes):
        # ``-z`` is NUL-TERMINATED (every record, including the last,
        # ends with a NUL). Splitting on NUL therefore yields an empty
        # trailing element which we drop here. Filtering empties also
        # handles defensively if git ever changed to NUL-separated.
        records: Sequence[Union[bytes, str]] = [r for r in stdout.split(b"\x00") if r]
    else:
        records = [r for r in stdout.split("\x00") if r]

    entries: List[PorcelainEntry] = []
    i = 0
    n = len(records)
    while i < n:
        record = records[i]
        # Each record is at least 4 bytes/chars: ``XY <path>``. Anything
        # shorter is malformed; skip it defensively.
        if len(record) < 4:
            i += 1
            continue
        if isinstance(record, bytes):
            status = record[:2].decode("ascii", errors="replace")
            path_bytes: Union[bytes, str] = record[3:]
        else:
            status = record[:2]
            path_bytes = record[3:]
        path = _decode_path(path_bytes)

        old_path: Optional[str] = None
        # ``R``/``C`` in either column means the NEXT record is the old
        # path (no leading status field — it is a bare path).
        if "R" in status or "C" in status:
            if i + 1 < n:
                i += 1
                old_path = _decode_path(records[i])
        entries.append(PorcelainEntry(status=status, path=path, old_path=old_path))
        i += 1
    return entries


def run_porcelain_z(
    cwd: Union[str, Path],
    *,
    include_untracked: bool = True,
    timeout: Optional[float] = 30,
) -> Optional[List[PorcelainEntry]]:
    """Run ``git status --porcelain=v1 -z`` in *cwd* and parse the result.

    Returns ``None`` if git is unavailable, the command times out, or
    returns a non-zero exit code so callers can degrade gracefully.

    Args:
        cwd: Directory in which to run git.
        include_untracked: When ``True`` (default), pass
            ``--untracked-files=all`` so untracked files are surfaced.
            When ``False``, pass ``-uno`` to suppress them — matching
            the behavior of ``_revert_out_of_scope_changes`` which
            only cares about tracked changes.
        timeout: Seconds to wait for the git invocation.
    """
    cmd: List[str] = ["git", "status", "--porcelain=v1", "-z"]
    if include_untracked:
        cmd.append("--untracked-files=all")
    else:
        cmd.append("-uno")
    try:
        result = subprocess.run(
            cmd,
            cwd=str(cwd),
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        return None
    if result.returncode != 0:
        return None
    return parse_porcelain_z(result.stdout)


def iter_changed_paths(entries: Iterable[PorcelainEntry]) -> Iterator[str]:
    """Yield changed paths from *entries*.

    For renames, yield both the new and old path because both sides are
    part of the change. For copies, yield only the copied destination:
    the source path is referenced by git but is not itself modified.
    """
    for entry in entries:
        yield entry.path
        if entry.old_path is not None and "R" in entry.status:
            yield entry.old_path
