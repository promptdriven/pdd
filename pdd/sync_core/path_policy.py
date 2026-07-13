"""Protected repository path validation and artifact snapshots."""

from __future__ import annotations

import hashlib
import os
import stat
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Mapping

from .types import ArtifactSnapshot


class PathPolicyError(ValueError):
    """Raised when a managed path violates protected repository policy."""


@dataclass(frozen=True)
class ResolvedPath:
    """Logical identity and prevalidated canonical target for a managed path."""

    logical_relpath: PurePosixPath
    canonical_path: Path
    alias_relpath: PurePosixPath | None = None


class PathPolicy:
    """Validate managed paths against one canonical checkout boundary."""

    def __init__(
        self,
        checkout_root: Path,
        approved_aliases: Mapping[PurePosixPath, PurePosixPath] | None = None,
    ) -> None:
        root = Path(checkout_root)
        if root.is_symlink() or not root.is_dir():
            raise PathPolicyError("checkout root must be a real directory")
        self.checkout_root = root.resolve()
        self.approved_aliases = dict(approved_aliases or {})

    @staticmethod
    def _validate_relpath(relpath: PurePosixPath) -> None:
        if relpath.is_absolute() or not relpath.parts or ".." in relpath.parts:
            raise PathPolicyError(f"managed path must be repository-relative: {relpath}")

    def _within_root(self, path: Path) -> bool:
        try:
            path.relative_to(self.checkout_root)
            return True
        except ValueError:
            return False

    def resolve(self, relpath: PurePosixPath, *, allow_missing: bool = False) -> ResolvedPath:
        """Resolve a logical path without permitting unapproved link traversal."""
        self._validate_relpath(relpath)
        candidate = self.checkout_root.joinpath(*relpath.parts)
        alias_relpath = None
        parts = relpath.parts
        for index in range(1, len(parts) + 1):
            logical_component = PurePosixPath(*parts[:index])
            component = self.checkout_root.joinpath(*parts[:index])
            if not component.exists() and not component.is_symlink():
                break
            mode = component.lstat().st_mode
            if stat.S_ISLNK(mode):
                approved_target = self.approved_aliases.get(logical_component)
                if approved_target is None:
                    raise PathPolicyError(f"unapproved managed symlink: {logical_component}")
                self._validate_relpath(approved_target)
                target = component.resolve(strict=True)
                expected = self.checkout_root.joinpath(*approved_target.parts).resolve(strict=True)
                if target != expected or not self._within_root(target):
                    raise PathPolicyError(
                        f"approved alias target changed: {logical_component}"
                    )
                alias_relpath = logical_component
        canonical = candidate.resolve(strict=not allow_missing)
        if not self._within_root(canonical):
            raise PathPolicyError(f"managed path escapes checkout: {relpath}")
        if canonical.exists():
            mode = canonical.stat().st_mode
            if not stat.S_ISREG(mode):
                raise PathPolicyError(
                    f"managed artifact is not a regular file: {relpath}"
                )
        elif not allow_missing:
            raise PathPolicyError(f"managed artifact does not exist: {relpath}")
        return ResolvedPath(relpath, canonical, alias_relpath)

    def snapshot(
        self,
        role: str,
        relpath: PurePosixPath,
        *,
        required: bool = True,
    ) -> ArtifactSnapshot:
        """Hash content and normalized Git mode after validating path policy."""
        try:
            resolved = self.resolve(relpath)
        except FileNotFoundError:
            return ArtifactSnapshot(role, relpath, None, None, required)
        digest = hashlib.sha256(resolved.canonical_path.read_bytes()).hexdigest()
        file_mode = resolved.canonical_path.stat().st_mode
        executable_bits = stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH
        git_mode = "100755" if file_mode & executable_bits else "100644"
        return ArtifactSnapshot(role, relpath, digest, git_mode, required)

    def revalidate(self, resolved: ResolvedPath) -> None:
        """Reject target replacement or alias retarget before a later commit."""
        current = self.resolve(resolved.logical_relpath, allow_missing=True)
        if current != resolved:
            raise PathPolicyError(
                f"managed path changed after planning: {resolved.logical_relpath}"
            )
        parent_mode = os.lstat(current.canonical_path.parent).st_mode
        if not stat.S_ISDIR(parent_mode):
            raise PathPolicyError("managed destination parent is not a directory")
