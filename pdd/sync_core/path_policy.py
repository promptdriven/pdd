"""Protected repository path validation and artifact snapshots."""

from __future__ import annotations

import hashlib
import os
import posixpath
import stat
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Mapping

from .git_io import read_git_blob, read_git_tree_entry
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
        *,
        base_ref: str | None = None,
        head_ref: str | None = None,
    ) -> None:
        root = Path(checkout_root)
        if root.is_symlink() or not root.is_dir():
            raise PathPolicyError("checkout root must be a real directory")
        self.checkout_root = root.resolve()
        self.approved_aliases = dict(approved_aliases or {})
        self.base_ref = base_ref
        self.head_ref = head_ref

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

    @staticmethod
    def _canonical_alias_target(
        alias_relpath: PurePosixPath, raw_target: bytes
    ) -> PurePosixPath:
        try:
            target_text = raw_target.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise PathPolicyError(
                f"approved alias target is not UTF-8: {alias_relpath}"
            ) from exc
        target = PurePosixPath(target_text)
        if target.is_absolute():
            raise PathPolicyError(f"approved alias target escapes checkout: {alias_relpath}")
        normalized = PurePosixPath(
            posixpath.normpath((alias_relpath.parent / target).as_posix())
        )
        if normalized == PurePosixPath(".") or ".." in normalized.parts:
            raise PathPolicyError(f"approved alias target escapes checkout: {alias_relpath}")
        return normalized

    def _immutable_alias_target(
        self,
        alias_relpath: PurePosixPath,
        *,
        required: bool,
    ) -> PurePosixPath | None:
        if self.base_ref is None or self.head_ref is None:
            return None
        base_entry = read_git_tree_entry(self.checkout_root, self.base_ref, alias_relpath)
        head_entry = read_git_tree_entry(self.checkout_root, self.head_ref, alias_relpath)
        if base_entry is None and head_entry is None:
            if required:
                raise PathPolicyError(
                    f"approved alias is absent from protected trees: {alias_relpath}"
                )
            return None
        if base_entry != head_entry or base_entry is None or head_entry is None:
            raise PathPolicyError(f"approved alias changed in protected trees: {alias_relpath}")
        if base_entry.mode != "120000" or base_entry.object_type != "blob":
            if not required:
                return None
            raise PathPolicyError(
                f"approved alias is not an unchanged symlink: {alias_relpath}"
            )
        target = read_git_blob(self.checkout_root, self.base_ref, alias_relpath)
        if target is None:
            raise PathPolicyError(f"approved alias target is unreadable: {alias_relpath}")
        return self._canonical_alias_target(alias_relpath, target)

    def _approved_alias_target(
        self, alias_relpath: PurePosixPath,
        *,
        required: bool = False,
    ) -> PurePosixPath | None:
        configured = self.approved_aliases.get(alias_relpath)
        if configured is None:
            return None
        immutable = self._immutable_alias_target(
            alias_relpath,
            required=required or configured is not None,
        )
        self._validate_relpath(configured)
        if immutable is not None and configured != immutable:
            raise PathPolicyError(f"approved alias target changed: {alias_relpath}")
        return configured

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
            approved_target = self._approved_alias_target(
                logical_component,
                required=stat.S_ISLNK(mode),
            )
            if approved_target is not None and not stat.S_ISLNK(mode):
                raise PathPolicyError(
                    f"approved alias is not a symlink: {logical_component}"
                )
            if stat.S_ISLNK(mode):
                if approved_target is None:
                    raise PathPolicyError(f"unapproved managed symlink: {logical_component}")
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
