"""Descriptor-relative durable JSON storage for protected replay ledgers."""
# pylint: disable=import-error,too-many-boolean-expressions

from __future__ import annotations

import json
import os
import secrets
import stat
from pathlib import Path
from typing import Any, Callable


class DescriptorStoreError(ValueError):
    """Raised when a durable store cannot establish a safe path boundary."""


def _lock(descriptor: int) -> None:
    if os.name == "nt":  # pragma: no cover - exercised on Windows CI
        import msvcrt  # pylint: disable=import-outside-toplevel
        msvcrt.locking(descriptor, msvcrt.LK_LOCK, 1)
        return
    import fcntl  # pylint: disable=import-outside-toplevel
    fcntl.flock(descriptor, fcntl.LOCK_EX)


def _unlock(descriptor: int) -> None:
    if os.name == "nt":  # pragma: no cover - exercised on Windows CI
        import msvcrt  # pylint: disable=import-outside-toplevel
        msvcrt.locking(descriptor, msvcrt.LK_UNLCK, 1)
        return
    import fcntl  # pylint: disable=import-outside-toplevel
    fcntl.flock(descriptor, fcntl.LOCK_UN)


def _safe_parent(path: Path) -> tuple[int, os.stat_result]:
    """Open the ledger parent once and return its stable directory identity."""
    if path.name in {"", ".", ".."} or path.is_absolute() is False:
        path = path.absolute()
    parent = path.parent
    parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(parent, flags)
    except OSError as exc:
        raise DescriptorStoreError("replay ledger parent is unsafe") from exc
    opened = os.fstat(descriptor)
    lexical = os.lstat(parent)
    if (
        not stat.S_ISDIR(opened.st_mode)
        or stat.S_ISLNK(lexical.st_mode)
        or (opened.st_dev, opened.st_ino) != (lexical.st_dev, lexical.st_ino)
        or (hasattr(os, "getuid") and opened.st_uid != os.getuid())
        or stat.S_IMODE(opened.st_mode) & 0o077
    ):
        os.close(descriptor)
        raise DescriptorStoreError("replay ledger parent is unsafe")
    return descriptor, opened


def _open_relative(parent_fd: int, name: str, flags: int, mode: int = 0o600) -> int:
    try:
        return os.open(
            name,
            flags | getattr(os, "O_NOFOLLOW", 0),
            mode,
            dir_fd=parent_fd,
        )
    except (OSError, NotImplementedError) as exc:
        raise DescriptorStoreError("replay ledger is unsafe") from exc


def _read_json(parent_fd: int, name: str, empty: Any) -> Any:
    try:
        descriptor = _open_relative(parent_fd, name, os.O_RDONLY)
    except DescriptorStoreError:
        try:
            os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
        except FileNotFoundError:
            return empty
        raise
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode) or stat.S_IMODE(metadata.st_mode) != 0o600:
            raise DescriptorStoreError("replay ledger is unsafe")
        with os.fdopen(descriptor, "r", encoding="utf-8", closefd=False) as handle:
            return json.load(handle)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise DescriptorStoreError("replay ledger is corrupt") from exc
    finally:
        os.close(descriptor)


def _write_json(parent_fd: int, name: str, payload: Any) -> None:
    temporary = f".{name}.{secrets.token_hex(16)}.tmp"
    descriptor = _open_relative(
        parent_fd, temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600
    )
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", closefd=False) as handle:
            json.dump(payload, handle, sort_keys=True, indent=2)
            handle.write("\n")
            handle.flush()
            os.fsync(descriptor)
        os.replace(temporary, name, src_dir_fd=parent_fd, dst_dir_fd=parent_fd)
        os.fsync(parent_fd)
    finally:
        os.close(descriptor)
        try:
            os.unlink(temporary, dir_fd=parent_fd)
        except FileNotFoundError:
            pass


def update_json(
    path: Path, empty: Any, update: Callable[[Any], Any]
) -> Any:
    """Lock and update one JSON ledger using only its held parent descriptor."""
    path = Path(path)
    parent_fd, identity = _safe_parent(path)
    lock_name = f"{path.name}.lock"
    lock_fd = -1
    try:
        lock_fd = _open_relative(parent_fd, lock_name, os.O_RDWR | os.O_CREAT, 0o600)
        if not stat.S_ISREG(os.fstat(lock_fd).st_mode):
            raise DescriptorStoreError("replay ledger lock is unsafe")
        os.fchmod(lock_fd, 0o600)
        _lock(lock_fd)
        payload = _read_json(parent_fd, path.name, empty)
        replacement = update(payload)
        if replacement is not None:
            _write_json(parent_fd, path.name, replacement)
        current = os.stat(path.parent, follow_symlinks=False)
        if (current.st_dev, current.st_ino) != (identity.st_dev, identity.st_ino):
            raise DescriptorStoreError("replay ledger parent changed")
        return payload if replacement is None else replacement
    finally:
        if lock_fd >= 0:
            try:
                _unlock(lock_fd)
            finally:
                os.close(lock_fd)
        os.close(parent_fd)
