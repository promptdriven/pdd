"""Protected expected-unit and decommission authorization parsing."""

from __future__ import annotations

import json
from dataclasses import dataclass, replace
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING

from .git_io import read_git_blob
from .types import UnitId

if TYPE_CHECKING:
    from .manifest import OwnershipRule, UnitManifest


_EXPECTED_MANAGED_PATH = PurePosixPath(".pdd/expected-managed.json")
_OWNERSHIP_PATH = PurePosixPath(".pdd/sync-ownership.json")


@dataclass(frozen=True)
class DecommissionTombstone:
    """Protected proof that a synchronized unit was deliberately removed."""

    prompt_path: PurePosixPath
    artifact_paths: tuple[PurePosixPath, ...]
    rationale: str
    owner: str
    baseline_status: str


def load_tombstones(
    root: Path, ref: str
) -> dict[PurePosixPath, DecommissionTombstone]:
    """Load strict decommission authorizations from one immutable Git tree."""
    raw = read_git_blob(root, ref, PurePosixPath(".pdd/sync-tombstones.json"))
    if raw is None:
        return {}
    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise ValueError("protected sync tombstones are malformed") from exc
    if not isinstance(payload, list):
        raise ValueError("protected sync tombstones must be a list")
    tombstones: dict[PurePosixPath, DecommissionTombstone] = {}
    for item in payload:
        if not isinstance(item, dict):
            raise ValueError("each sync tombstone must be an object")
        try:
            prompt_path = PurePosixPath(item["prompt_path"])
            artifacts = tuple(
                sorted(PurePosixPath(value) for value in item["artifact_paths"])
            )
            tombstone = DecommissionTombstone(
                prompt_path,
                artifacts,
                item["rationale"],
                item["owner"],
                item["baseline_status"],
            )
        except (KeyError, TypeError) as exc:
            raise ValueError("sync tombstone is missing required fields") from exc
        if (
            prompt_path.is_absolute()
            or ".." in prompt_path.parts
            or any(path.is_absolute() or ".." in path.parts for path in artifacts)
            or not tombstone.rationale
            or not tombstone.owner
        ):
            raise ValueError("sync tombstone contains invalid protected fields")
        if prompt_path in tombstones:
            raise ValueError("duplicate sync tombstone prompt identity")
        tombstones[prompt_path] = tombstone
    return tombstones


def load_expected_registry(
    root: Path, ref: str, repository_id: str
) -> set[UnitId] | None:
    """Load the protected active-unit denominator when one has been established."""
    raw = read_git_blob(root, ref, PurePosixPath(".pdd/expected-managed.json"))
    if raw is None:
        return None
    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise ValueError("protected expected-managed registry is malformed") from exc
    rows = payload.get("units") if isinstance(payload, dict) else None
    if (
        not isinstance(payload, dict)
        or payload.get("schema_version") != 1
        or not isinstance(rows, list)
    ):
        raise ValueError("protected expected-managed registry schema is invalid")
    units: set[UnitId] = set()
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"prompt_path", "language_id"}:
            raise ValueError("expected-managed unit entry is malformed")
        try:
            unit = UnitId(
                repository_id,
                PurePosixPath(row["prompt_path"]),
                row["language_id"],
            )
        except (TypeError, ValueError) as exc:
            raise ValueError("expected-managed unit identity is invalid") from exc
        if unit in units:
            raise ValueError("expected-managed registry contains a duplicate unit")
        units.add(unit)
    return units


def control_transition_invalid(
    root: Path,
    base_ref: str,
    head_ref: str,
    base_ownership: tuple[OwnershipRule, ...],
    head_ownership: tuple[OwnershipRule, ...],
) -> list[str]:
    """Reject removal or weakening of protected denominator controls."""
    invalid: list[str] = []
    base_ownership_blob = read_git_blob(root, base_ref, _OWNERSHIP_PATH)
    head_ownership_blob = read_git_blob(root, head_ref, _OWNERSHIP_PATH)
    if base_ownership_blob is not None and head_ownership_blob is None:
        invalid.append(f"{head_ref}: protected sync ownership policy is missing")
    elif base_ownership_blob is not None:
        removed = set(base_ownership) - set(head_ownership)
        for rule in sorted(removed, key=lambda item: item.pattern):
            promoted = replace(rule, preauthorize_absent=True)
            if (
                not rule.preauthorize_absent
                and promoted in head_ownership
                and read_git_blob(root, base_ref, PurePosixPath(rule.pattern)) is None
                and read_git_blob(root, head_ref, PurePosixPath(rule.pattern)) is None
            ):
                # An exact dormant rule may be promoted only in a prerequisite
                # transition that does not also introduce the authorized path.
                continue
            invalid.append(
                f"{head_ref}: protected sync ownership rule was removed or weakened: "
                f"{rule.pattern}"
            )

    base_expected = read_git_blob(root, base_ref, _EXPECTED_MANAGED_PATH)
    head_expected = read_git_blob(root, head_ref, _EXPECTED_MANAGED_PATH)
    if base_expected is not None and head_expected is None:
        invalid.append(f"{head_ref}: protected expected-managed registry is missing")
    return invalid


def enforce_head_fixed_point(
    transition: UnitManifest,
    stable_head: UnitManifest,
    control_invalid: list[str],
) -> UnitManifest:
    """Require the candidate head to be a valid next protected base."""
    invalid = list(transition.invalid_reasons)
    invalid.extend(control_invalid)
    invalid.extend(
        f"{stable_head.head_ref}: fixed-point: {reason}"
        for reason in stable_head.invalid_reasons
    )
    stable_managed = {unit.unit_id for unit in stable_head.managed_units}
    if stable_managed != set(stable_head.expected_managed):
        invalid.append(
            f"{stable_head.head_ref}: fixed-point managed units do not match "
            "the protected expected-managed registry"
        )
    return replace(
        transition,
        invalid_reasons=tuple(invalid),
        unaccounted_tracked_paths=tuple(
            sorted(
                set(transition.unaccounted_tracked_paths)
                | set(stable_head.unaccounted_tracked_paths)
            )
        ),
    )
