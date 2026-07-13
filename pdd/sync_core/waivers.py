"""Protected waiver loading for canonical synchronization reports."""

from __future__ import annotations

import json
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path, PurePosixPath
from typing import Any

from .git_io import read_git_blob
from .manifest import UnitManifest


WAIVER_PATH = PurePosixPath(".pdd/sync-waivers.json")


@dataclass(frozen=True, order=True)
class SyncWaiver:
    """Reviewed, expiring exception bound to one exact managed snapshot."""

    waiver_id: str
    prompt_path: PurePosixPath
    snapshot_digest: str
    approved_by: str
    reason: str
    expires_at: datetime


@dataclass(frozen=True)
class WaiverSet:
    """Effective managed waivers and fail-closed policy violations."""

    waivers: tuple[SyncWaiver, ...]
    invalid_reasons: tuple[str, ...]

    @property
    def managed_count(self) -> int:
        """Return the gross number of effective managed exceptions."""
        return len(self.waivers)


def _waiver(row: Any) -> SyncWaiver:
    if not isinstance(row, dict):
        raise ValueError("waiver entry is not an object")
    try:
        expires_at = datetime.fromisoformat(str(row["expires_at"]))
        waiver = SyncWaiver(
            str(row["waiver_id"]).strip(),
            PurePosixPath(str(row["prompt_path"])),
            str(row["snapshot_digest"]).strip(),
            str(row["approved_by"]).strip(),
            str(row["reason"]).strip(),
            expires_at,
        )
    except (KeyError, ValueError) as exc:
        raise ValueError("waiver entry is malformed") from exc
    invalid_fields = (
        not waiver.waiver_id,
        waiver.prompt_path.is_absolute(),
        ".." in waiver.prompt_path.parts,
        len(waiver.snapshot_digest) != 64,
        any(character not in "0123456789abcdef" for character in waiver.snapshot_digest),
        not waiver.approved_by,
        not waiver.reason,
        waiver.expires_at.tzinfo is None,
    )
    if any(invalid_fields):
        raise ValueError("waiver entry has invalid protected fields")
    return waiver


def _load(root: Path, ref: str) -> tuple[dict[str, SyncWaiver], list[str]]:
    raw = read_git_blob(root, ref, WAIVER_PATH)
    if raw is None:
        return {}, []
    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        return {}, [f"{ref}: sync waiver file is malformed: {exc}"]
    rows = payload.get("waivers") if isinstance(payload, dict) else None
    if not isinstance(rows, list):
        return {}, [f"{ref}: sync waivers must be a list"]
    waivers: dict[str, SyncWaiver] = {}
    invalid: list[str] = []
    for row in rows:
        try:
            waiver = _waiver(row)
        except ValueError as exc:
            invalid.append(f"{ref}: {exc}")
            continue
        if waiver.waiver_id in waivers:
            invalid.append(f"{ref}: duplicate waiver id {waiver.waiver_id}")
            continue
        waivers[waiver.waiver_id] = waiver
    return waivers, invalid


def load_sync_waivers(
    root: Path,
    manifest: UnitManifest,
    *,
    now: datetime,
) -> WaiverSet:
    """Load an immutable base/head waiver union without permitting weakening."""
    base, invalid = _load(root, manifest.base_ref)
    head, head_invalid = _load(root, manifest.head_ref)
    invalid.extend(head_invalid)
    effective = dict(base)
    for waiver_id, waiver in head.items():
        protected = base.get(waiver_id)
        if protected is not None and protected != waiver:
            invalid.append(f"candidate changed protected waiver {waiver_id}")
            continue
        effective[waiver_id] = waiver
    invalid.extend(
        f"candidate removed protected waiver {waiver_id}"
        for waiver_id in sorted(set(base) - set(head))
    )
    expected = {unit.prompt_relpath for unit in manifest.expected_managed}
    valid: list[SyncWaiver] = []
    for waiver in effective.values():
        if waiver.prompt_path not in expected:
            invalid.append(
                f"waiver {waiver.waiver_id} references non-managed subject "
                f"{waiver.prompt_path}"
            )
            continue
        if waiver.expires_at <= now:
            invalid.append(f"waiver {waiver.waiver_id} is expired")
            continue
        valid.append(waiver)
    return WaiverSet(tuple(sorted(valid)), tuple(sorted(set(invalid))))
