"""Canonical unit snapshots built from manifests, includes, and profiles."""

from __future__ import annotations

from pathlib import Path, PurePosixPath

from .alias_policy import load_protected_aliases
from .includes import IncludeGraphError, build_include_closure
from .manifest import ManifestUnit, UnitManifest
from .path_policy import PathPolicy, PathPolicyError
from .types import ArtifactSnapshot, UnitSnapshot, VerificationProfile


class SnapshotError(ValueError):
    """Raised when a complete policy-valid unit snapshot cannot be built."""


def _obligation_role(kind: str) -> str:
    normalized = kind.casefold()
    if normalized in {"test", "story", "policy", "requirement"}:
        return "test"
    if normalized == "example":
        return "example"
    return "validation"


def build_unit_snapshot(
    root: Path,
    manifest: UnitManifest,
    unit: ManifestUnit,
    profile: VerificationProfile,
) -> UnitSnapshot:
    """Build the complete current snapshot for one present managed unit."""
    if not unit.present_in_head:
        raise SnapshotError("cannot snapshot a unit absent from the checked head")
    if profile.unit_id != unit.unit_id:
        raise SnapshotError("verification profile identity does not match unit")
    policy = PathPolicy(root, load_protected_aliases(root, manifest))
    artifacts: dict[tuple[str, PurePosixPath], ArtifactSnapshot] = {}

    def add(role: str, relpath: PurePosixPath, required: bool = True) -> None:
        snapshot = policy.snapshot(role, relpath, required=required)
        artifacts[(role, relpath)] = snapshot

    try:
        add("prompt", unit.unit_id.prompt_relpath)
        closure = build_include_closure(
            unit.unit_id.prompt_relpath,
            policy,
            root_aliases=unit.artifact_paths,
        )
        for included in closure.artifacts:
            add("include", included.relpath)
        for path in unit.artifact_paths:
            add("code", path)
        for obligation in profile.obligations:
            for path in obligation.code_under_test_paths:
                add("code", path)
            role = _obligation_role(obligation.kind)
            for path in obligation.artifact_paths:
                add(role, path, required=obligation.required)
    except (FileNotFoundError, PathPolicyError, IncludeGraphError) as exc:
        raise SnapshotError(f"cannot build unit snapshot: {exc}") from exc
    return UnitSnapshot(
        unit.unit_id,
        tuple(sorted(artifacts.values())),
        manifest.unit_digest(unit),
        closure.digest(),
        profile.profile_digest,
        closure.has_nondeterministic_query,
    )
