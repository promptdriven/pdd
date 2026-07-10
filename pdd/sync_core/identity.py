"""Stable repository identity used by canonical sync records."""

from __future__ import annotations

import os
import subprocess
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from .durability import fsync_directory


REPOSITORY_ID_RELPATH = Path(".pdd/repository-id")


class RepositoryIdentityError(ValueError):
    """Raised when protected repository identity is absent or malformed."""


@dataclass(frozen=True)
class RepositoryIdentity:
    """A repository UUID and whether it is safe for persistent state."""

    value: str
    persistent: bool


def canonical_repository_id(value: str) -> str:
    """Validate and normalize one protected repository UUID."""
    try:
        parsed = uuid.UUID(value.strip())
    except (AttributeError, ValueError) as exc:
        raise RepositoryIdentityError("repository ID must be a valid UUID") from exc
    if str(parsed) != value.strip().lower():
        raise RepositoryIdentityError("repository ID must use canonical lowercase UUID form")
    return str(parsed)


def _ephemeral_seed(root: Path) -> str:
    result = subprocess.run(
        ["git", "config", "--get", "remote.origin.url"],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    return result.stdout.strip() or str(root.resolve())


def read_repository_identity(root: Path, *, require_persistent: bool = False) -> RepositoryIdentity:
    """Read protected identity or return a report-only ephemeral UUID."""
    repository_root = Path(root).resolve()
    identity_path = repository_root / REPOSITORY_ID_RELPATH
    if identity_path.exists():
        if identity_path.is_symlink() or not identity_path.is_file():
            raise RepositoryIdentityError("repository ID must be a regular file")
        return RepositoryIdentity(
            canonical_repository_id(identity_path.read_text(encoding="ascii")),
            True,
        )
    if require_persistent:
        raise RepositoryIdentityError(
            "canonical state requires initialization of .pdd/repository-id"
        )
    ephemeral = uuid.uuid5(uuid.NAMESPACE_URL, f"pdd-legacy:{_ephemeral_seed(repository_root)}")
    return RepositoryIdentity(str(ephemeral), False)


def initialize_repository_identity(
    root: Path,
    repository_id: Optional[str] = None,
) -> RepositoryIdentity:
    """Create the protected repository UUID exactly once using an atomic write."""
    repository_root = Path(root).resolve()
    identity_path = repository_root / REPOSITORY_ID_RELPATH
    if identity_path.exists():
        return read_repository_identity(repository_root, require_persistent=True)
    value = canonical_repository_id(repository_id or str(uuid.uuid4()))
    state_dir = identity_path.parent
    if state_dir.exists() and (state_dir.is_symlink() or not state_dir.is_dir()):
        raise RepositoryIdentityError(".pdd must be a real directory")
    state_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
    temporary = state_dir / f".{identity_path.name}.{os.getpid()}.tmp"
    descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "w", encoding="ascii") as handle:
            handle.write(value + "\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, identity_path)
        fsync_directory(state_dir)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise
    return RepositoryIdentity(value, True)
