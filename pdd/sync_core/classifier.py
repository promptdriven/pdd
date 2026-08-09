"""Pure synchronization classifier."""

from __future__ import annotations

from typing import Optional

from .types import (
    BaselineStatus,
    EvidenceOutcome,
    FingerprintRecord,
    InventoryStatus,
    SemanticStatus,
    SyncVerdict,
    UnitSnapshot,
    VerdictDetails,
    VerificationProfile,
)
from .trust import ValidationEvidence


PROMPT_SIDE_ROLES = frozenset({"prompt", "include", "config", "architecture"})


def _evidence_is_complete(
    current: UnitSnapshot,
    profile: Optional[VerificationProfile],
    evidence: Optional[ValidationEvidence],
) -> bool:
    if profile is None or evidence is None:
        return False
    outcomes = evidence.result_map()
    required = (item for item in profile.obligations if item.required)
    obligations_pass = all(
        outcomes.get(item.obligation_id) is EvidenceOutcome.PASS for item in required
    )
    return (
        profile.complete
        and profile.unit_id == current.unit_id
        and evidence.subject == current.unit_id
        and profile.profile_digest == current.verification_profile_digest
        and evidence.profile_digest == profile.profile_digest
        and evidence.snapshot_digest == current.digest()
        and not current.nondeterministic_inputs
        and obligations_pass
    )


def _preflight_verdict(
    current: UnitSnapshot,
    baseline: Optional[FingerprintRecord],
    inventory: InventoryStatus,
    missing: tuple[str, ...],
) -> Optional[SyncVerdict]:
    """Return a fail-closed verdict for invalid identity or absent baseline."""
    if inventory is InventoryStatus.INVALID:
        statuses = (BaselineStatus.CORRUPT, SemanticStatus.FAILED)
        reason = "unit inventory or path policy is invalid"
    elif baseline is None:
        statuses = (BaselineStatus.UNBASELINED, SemanticStatus.UNKNOWN)
        reason = "no trustworthy baseline exists"
    elif not baseline.valid:
        statuses = (BaselineStatus.CORRUPT, SemanticStatus.FAILED)
        reason = "baseline schema or provenance is invalid"
    elif baseline.snapshot.unit_id != current.unit_id:
        statuses = (BaselineStatus.CORRUPT, SemanticStatus.FAILED)
        reason = "baseline identity does not match the current unit"
    else:
        return None
    return SyncVerdict(
        current.unit_id,
        inventory,
        *statuses,
        VerdictDetails((), reason, missing),
    )


def _changed_roles(current: UnitSnapshot, baseline: UnitSnapshot) -> tuple[str, ...]:
    """Compare artifact and closure state without consulting Git provenance."""
    baseline_artifacts = baseline.artifact_map()
    current_artifacts = current.artifact_map()
    roles = set(baseline_artifacts) | set(current_artifacts)
    changed = [
        role
        for role in roles
        if baseline_artifacts.get(role) != current_artifacts.get(role)
    ]
    closure_changed = (
        baseline.manifest_digest != current.manifest_digest
        or baseline.verification_profile_digest != current.verification_profile_digest
    )
    if closure_changed:
        closure_roles = ("manifest",)
    else:
        closure_roles = ()
    artifact_roles = tuple(role for role, _path in changed)
    return tuple(sorted(artifact_roles + closure_roles))


def _drift_verdict(
    current: UnitSnapshot,
    inventory: InventoryStatus,
    changed: tuple[str, ...],
) -> SyncVerdict:
    """Classify one-sided drift versus a simultaneous source/derived edit."""
    prompt_changed = bool(set(changed) & PROMPT_SIDE_ROLES)
    derived_changed = bool(set(changed) - PROMPT_SIDE_ROLES - {"manifest"})
    conflict = prompt_changed and derived_changed
    semantic = SemanticStatus.CONFLICT if conflict else SemanticStatus.UNKNOWN
    reason = (
        "prompt-side and derived artifacts changed from the same baseline"
        if conflict
        else "current state differs from the trusted baseline"
    )
    return SyncVerdict(
        current.unit_id,
        inventory,
        BaselineStatus.DRIFTED,
        semantic,
        VerdictDetails(changed, reason),
    )


def classify(
    current: UnitSnapshot,
    baseline: Optional[FingerprintRecord],
    profile: Optional[VerificationProfile],
    evidence: Optional[ValidationEvidence],
    *,
    inventory: InventoryStatus = InventoryStatus.MANAGED,
) -> SyncVerdict:
    """Classify a unit without I/O, mutation, subprocesses, or policy inference."""
    missing = tuple(
        sorted(
            artifact.role
            for artifact in current.artifacts
            if artifact.required and not artifact.exists
        )
    )
    preflight = _preflight_verdict(current, baseline, inventory, missing)
    if preflight is not None:
        return preflight
    assert baseline is not None
    changed = _changed_roles(current, baseline.snapshot)

    if missing:
        return SyncVerdict(
            current.unit_id,
            inventory,
            BaselineStatus.DRIFTED,
            SemanticStatus.FAILED,
            VerdictDetails(
                changed,
                "one or more required artifacts are missing",
                missing,
            ),
        )

    evidence_complete = _evidence_is_complete(current, profile, evidence)
    if not changed:
        return SyncVerdict(
            current.unit_id,
            inventory,
            BaselineStatus.CURRENT,
            SemanticStatus.VERIFIED if evidence_complete else SemanticStatus.UNKNOWN,
            VerdictDetails(
                (),
                "baseline is current and trusted evidence is complete"
                if evidence_complete
                else "baseline is current but complete trusted evidence is absent",
                evidence_complete=evidence_complete,
            ),
        )
    return _drift_verdict(current, inventory, changed)
