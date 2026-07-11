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


def _safe_directory(metadata: os.stat_result) -> bool:
    """Return whether metadata describes a private checker-owned directory."""
    return (
        stat.S_ISDIR(metadata.st_mode)
        and (not hasattr(os, "getuid") or metadata.st_uid == os.getuid())
        and not stat.S_IMODE(metadata.st_mode) & 0o077
    )


def _legacy_safe_parent(path: Path) -> tuple[int, os.stat_result]:
    """Preserve strict filesystem-root validation for unanchored callers."""
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = -1
    try:
        descriptor = os.open(path.anchor, flags)
        for component in path.parent.parts[1:]:
            try:
                child = os.open(component, flags, dir_fd=descriptor)
            except FileNotFoundError:
                os.mkdir(component, mode=0o700, dir_fd=descriptor)
                child = os.open(component, flags, dir_fd=descriptor)
            metadata = os.fstat(child)
            if not stat.S_ISDIR(metadata.st_mode) or (
                hasattr(os, "getuid") and metadata.st_uid not in {0, os.getuid()}
            ):
                os.close(child)
                raise DescriptorStoreError("replay ledger parent is unsafe")
            os.close(descriptor)
            descriptor = child
    except (OSError, NotImplementedError, DescriptorStoreError) as exc:
        if descriptor >= 0:
            os.close(descriptor)
        if isinstance(exc, DescriptorStoreError):
            raise
        raise DescriptorStoreError("replay ledger parent is unsafe") from exc
    opened = os.fstat(descriptor)
    if not _safe_directory(opened):
        os.close(descriptor)
        raise DescriptorStoreError("replay ledger parent is unsafe")
    return descriptor, opened


def _safe_parent(
    path: Path, trust_root: Path | None
) -> tuple[int, os.stat_result]:
    """Traverse below a checker-owned trust root without following links."""
    path = path.absolute()
    if path.name in {"", ".", ".."}:
        raise DescriptorStoreError("replay ledger parent is unsafe")
    if trust_root is None:
        return _legacy_safe_parent(path)
    trust_root = trust_root.absolute()
    try:
        relative_parent = path.parent.relative_to(trust_root)
    except ValueError as exc:
        raise DescriptorStoreError("replay ledger escapes protected root") from exc
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = -1
    try:
        trust_root.mkdir(mode=0o700, parents=True, exist_ok=True)
        descriptor = os.open(trust_root, flags)
        root_metadata = os.fstat(descriptor)
        if not _safe_directory(root_metadata):
            raise DescriptorStoreError("replay ledger root is unsafe")
        for component in relative_parent.parts:
            if component in {"", ".", ".."}:
                raise DescriptorStoreError("replay ledger parent is unsafe")
            try:
                child = os.open(component, flags, dir_fd=descriptor)
            except FileNotFoundError:
                os.mkdir(component, mode=0o700, dir_fd=descriptor)
                child = os.open(component, flags, dir_fd=descriptor)
            metadata = os.fstat(child)
            if not _safe_directory(metadata):
                os.close(child)
                raise DescriptorStoreError("replay ledger parent is unsafe")
            os.close(descriptor)
            descriptor = child
    except (OSError, NotImplementedError, DescriptorStoreError) as exc:
        if descriptor >= 0:
            os.close(descriptor)
        if isinstance(exc, DescriptorStoreError):
            raise
        raise DescriptorStoreError("replay ledger parent is unsafe") from exc
    opened = os.fstat(descriptor)
    if not _safe_directory(opened):
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
        descriptor = _open_relative(parent_fd, name, os.O_RDONLY)
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
    path: Path,
    empty: Any,
    update: Callable[[Any], Any],
    *,
    trust_root: Path | None = None,
) -> Any:
    """Update JSON below an explicit checker-owned descriptor trust anchor."""
    path = Path(path).absolute()
    parent_fd, identity = _safe_parent(
        path, Path(trust_root) if trust_root is not None else None
    )
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
        current = os.fstat(parent_fd)
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
