"""Protected approved-alias policy loading for canonical synchronization."""
# pylint: disable=duplicate-code

from __future__ import annotations

import json
from pathlib import Path, PurePosixPath
from types import MappingProxyType
from typing import Mapping

from .git_io import read_git_blob
from .manifest import UnitManifest


ALIAS_POLICY_PATH = PurePosixPath(".pdd/sync-aliases.json")


def _relpath(value: object, field: str) -> PurePosixPath:
    if not isinstance(value, str) or not value:
        raise ValueError(f"protected alias {field} must be a non-empty path")
    path = PurePosixPath(value)
    if path.is_absolute() or not path.parts or ".." in path.parts:
        raise ValueError(f"protected alias {field} must be repository-relative")
    return path


def _parse(raw: bytes) -> Mapping[PurePosixPath, PurePosixPath]:
    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise ValueError("protected alias policy is malformed") from exc
    if (
        not isinstance(payload, dict)
        or set(payload) != {"schema_version", "aliases"}
        or payload["schema_version"] != 1
        or not isinstance(payload["aliases"], list)
    ):
        raise ValueError("protected alias policy schema is invalid")
    aliases: dict[PurePosixPath, PurePosixPath] = {}
    for row in payload["aliases"]:
        if not isinstance(row, dict) or set(row) != {"alias_path", "canonical_path"}:
            raise ValueError("protected alias entry is malformed")
        alias = _relpath(row["alias_path"], "path")
        canonical = _relpath(row["canonical_path"], "canonical path")
        if alias == canonical or alias in aliases:
            raise ValueError("protected alias entry is ambiguous")
        aliases[alias] = canonical
    ordered = dict(sorted(aliases.items()))
    return MappingProxyType(ordered)


def load_protected_aliases(
    root: Path, manifest: UnitManifest
) -> Mapping[PurePosixPath, PurePosixPath]:
    """Load immutable base aliases and reject candidate policy changes."""
    base = read_git_blob(root, manifest.base_ref, ALIAS_POLICY_PATH)
    head = read_git_blob(root, manifest.head_ref, ALIAS_POLICY_PATH)
    if base is None:
        if head is not None:
            raise ValueError("candidate added protected alias policy")
        return MappingProxyType({})
    if head is None:
        raise ValueError("candidate removed protected alias policy")
    if head != base:
        raise ValueError("candidate changed protected alias policy")
    return _parse(base)


def load_committed_aliases(
    root: Path, ref: str = "HEAD"
) -> Mapping[PurePosixPath, PurePosixPath]:
    """Load approved aliases from a committed protected policy blob."""
    raw = read_git_blob(root, ref, ALIAS_POLICY_PATH)
    if raw is None:
        return MappingProxyType({})
    return _parse(raw)
