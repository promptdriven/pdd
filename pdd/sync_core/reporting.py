"""Strict read-only canonical synchronization reporting."""

from __future__ import annotations

import os
import subprocess
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any, Iterable

from .classifier import classify
from .evidence_store import (
    EvidenceStoreError,
    load_attestation,
    load_trust_policy,
)
from .fingerprint_store import CorruptFingerprintError, FingerprintStore
from .git_io import resolve_git_commit
from .manifest import ManifestUnit, UnitManifest, build_unit_manifest
from .snapshot import SnapshotError, build_unit_snapshot
from .runner import RunnerConfig, TRUSTED_RUNNER_VERSION, runner_identity_digest
from .transaction import TransactionError, TransactionManager
from .trust import AttestationError, ValidationEvidence
from .types import (
    BaselineStatus,
    EvidenceOutcome,
    InventoryStatus,
    SemanticStatus,
    SyncVerdict,
    VerdictDetails,
)
from .verification import ProfileSet, load_verification_profiles
from .waivers import WaiverSet, load_sync_waivers


@dataclass(frozen=True)
class InventoryCounts:
    """Complete candidate and managed-denominator counts."""

    unaccounted_tracked_paths: int
    managed_units: int
    protected_expected_managed_units: int
    managed_waivers: int
    invalid: int


@dataclass(frozen=True)
class EvidenceCounts:
    """Profile and trusted-evidence coverage counts."""

    trusted_in_sync: int
    verification_profile_complete: int
    trusted_current_evidence: int


@dataclass(frozen=True)
class StatusCounts:
    """Independent baseline and semantic failure counts."""

    drifted: int
    unbaselined: int
    corrupt: int
    unknown: int
    conflict: int
    failed: int


@dataclass(frozen=True)
class CanonicalCounts:
    """Machine predicate counts aggregated from canonical unit verdicts."""

    inventory: InventoryCounts
    evidence: EvidenceCounts
    statuses: StatusCounts

    def as_flat_dict(self) -> dict[str, int]:
        """Return field names used by the external certificate predicate."""
        return {
            **self.inventory.__dict__,
            **self.evidence.__dict__,
            **self.statuses.__dict__,
        }


@dataclass(frozen=True)
class ReportContext:
    """Resolved read-only dependencies shared while classifying units."""

    root: Path
    manifest: UnitManifest
    profiles: ProfileSet
    store: FingerprintStore
    trust_policy: Any
    waivers: WaiverSet
    now: datetime


@dataclass(frozen=True)
class EvidenceExpectation:
    """Current closure fields an attestation must match."""

    unit: ManifestUnit
    snapshot_digest: str
    profile_digest: str
    attestation_ref: str | None


@dataclass(frozen=True)
class CanonicalReportOptions:
    """Exact refs, scope, trust state, and clock for one report."""

    base_ref: str = "HEAD"
    head_ref: str = "HEAD"
    modules: tuple[str, ...] = ()
    replay_ledger_path: Path | None = None
    now: datetime | None = None


def _error_verdict(unit: ManifestUnit, baseline: BaselineStatus, reason: str) -> SyncVerdict:
    return SyncVerdict(
        unit.unit_id,
        InventoryStatus.MANAGED,
        baseline,
        SemanticStatus.FAILED,
        VerdictDetails((), reason),
    )


def _invalid_profile_verdict(unit: ManifestUnit) -> SyncVerdict:
    """Return a non-current unknown verdict without consulting stale evidence."""
    return SyncVerdict(
        unit.unit_id,
        InventoryStatus.MANAGED,
        BaselineStatus.CORRUPT,
        SemanticStatus.UNKNOWN,
        VerdictDetails((), "verification profile reconciliation is invalid"),
    )


def _evidence(
    context: ReportContext,
    expectation: EvidenceExpectation,
) -> ValidationEvidence | None:
    if not expectation.attestation_ref or context.trust_policy is None:
        return None
    envelope = load_attestation(context.root, expectation.attestation_ref)
    evidence = context.trust_policy.verify(
        envelope, envelope.binding, now=context.now
    )
    ancestry = subprocess.run(
        [
            "git",
            "merge-base",
            "--is-ancestor",
            envelope.binding.checked_sha,
            context.manifest.head_ref,
        ],
        cwd=context.root,
        capture_output=True,
        check=False,
    )
    if ancestry.returncode != 0:
        raise AttestationError(
            "attestation checked commit is not an ancestor of certified head"
        )
    binding = envelope.binding
    if (
        binding.subject != expectation.unit.unit_id
        or binding.snapshot_digest != expectation.snapshot_digest
        or binding.profile_digest != expectation.profile_digest
        or binding.base_sha != context.manifest.base_ref
    ):
        return None
    profile = context.profiles.for_unit(expectation.unit.unit_id)
    outcomes = {item.obligation_id: item.outcome for item in envelope.results}
    vitest_pass_is_unbound = profile is not None and any(
        obligation.validator_id == "vitest"
        and outcomes.get(obligation.obligation_id) is EvidenceOutcome.PASS
        for obligation in profile.obligations
    ) and binding.native_runner_digest is None
    if (
        profile is None
        or vitest_pass_is_unbound
        or binding.runner_digest
        != runner_identity_digest(
            profile, root=context.root, ref=context.manifest.head_ref,
            config=RunnerConfig(
                adapter_identities=binding.adapter_identities,
            ),
        )
        or binding.tool_version != TRUSTED_RUNNER_VERSION
    ):
        raise AttestationError("attestation runner identity is not protected")
    return evidence


def _unit_verdict(context: ReportContext, unit: ManifestUnit) -> SyncVerdict:
    if context.manifest.invalid_reasons:
        return _error_verdict(unit, BaselineStatus.CORRUPT, "manifest is invalid")
    if context.profiles.invalid_reasons:
        return _invalid_profile_verdict(unit)
    profile = context.profiles.for_unit(unit.unit_id)
    if profile is None:
        return _error_verdict(unit, BaselineStatus.CORRUPT, "profile is missing")
    try:
        snapshot = build_unit_snapshot(context.root, context.manifest, unit, profile)
        baseline = context.store.load(unit.unit_id)
        attestation_ref = baseline.attestation_ref if baseline else None
        evidence = _evidence(
            context,
            EvidenceExpectation(
                unit,
                snapshot.digest(),
                profile.profile_digest,
                attestation_ref,
            ),
        )
        return classify(snapshot, baseline, profile, evidence)
    except CorruptFingerprintError as exc:
        return _error_verdict(unit, BaselineStatus.CORRUPT, str(exc))
    except (SnapshotError, EvidenceStoreError, AttestationError) as exc:
        return _error_verdict(unit, BaselineStatus.DRIFTED, str(exc))


def _counts(
    manifest: UnitManifest,
    profiles: ProfileSet,
    waivers: WaiverSet,
    verdicts: tuple[SyncVerdict, ...],
    errors: Iterable[str],
) -> CanonicalCounts:
    errors_present = bool(tuple(errors))
    inventory = InventoryCounts(
        len(manifest.unaccounted_tracked_paths),
        len(manifest.managed_units),
        len(manifest.expected_managed),
        waivers.managed_count,
        sum(item.inventory is InventoryStatus.INVALID for item in manifest.candidates)
        + int(errors_present),
    )
    evidence = EvidenceCounts(
        sum(verdict.in_sync for verdict in verdicts),
        sum(profile.complete for profile in profiles.profiles),
        sum(verdict.evidence_complete for verdict in verdicts),
    )
    statuses = StatusCounts(
        sum(verdict.baseline is BaselineStatus.DRIFTED for verdict in verdicts),
        sum(verdict.baseline is BaselineStatus.UNBASELINED for verdict in verdicts),
        sum(verdict.baseline is BaselineStatus.CORRUPT for verdict in verdicts),
        sum(verdict.semantic is SemanticStatus.UNKNOWN for verdict in verdicts),
        sum(verdict.semantic is SemanticStatus.CONFLICT for verdict in verdicts),
        sum(verdict.semantic is SemanticStatus.FAILED for verdict in verdicts),
    )
    return CanonicalCounts(inventory, evidence, statuses)


def _predicate(counts: CanonicalCounts) -> bool:
    inventory = counts.inventory
    evidence = counts.evidence
    statuses = counts.statuses
    return (
        inventory.unaccounted_tracked_paths == 0
        and inventory.managed_units > 0
        and inventory.managed_units == inventory.protected_expected_managed_units
        and inventory.managed_waivers == 0
        and evidence.trusted_in_sync == inventory.managed_units
        and evidence.verification_profile_complete == inventory.managed_units
        and evidence.trusted_current_evidence == inventory.managed_units
        and statuses.drifted == 0
        and statuses.unbaselined == 0
        and statuses.corrupt == 0
        and statuses.unknown == 0
        and statuses.conflict == 0
        and statuses.failed == 0
        and inventory.invalid == 0
    )


def _report_context(
    root: Path,
    options: CanonicalReportOptions,
) -> tuple[ReportContext, list[str], tuple[str, ...]]:
    """Resolve protected inputs, trust policy, store, and recovery state."""
    base_sha = resolve_git_commit(root, options.base_ref)
    head_sha = resolve_git_commit(root, options.head_ref)
    manifest = build_unit_manifest(root, base_ref=base_sha, head_ref=head_sha)
    profiles = load_verification_profiles(root, manifest)
    now = options.now or datetime.now(timezone.utc)
    waivers = load_sync_waivers(root, manifest, now=now)
    errors = list(
        manifest.invalid_reasons
        + profiles.invalid_reasons
        + waivers.invalid_reasons
    )
    ledger = options.replay_ledger_path
    if ledger is None:
        configured = os.environ.get("PDD_ATTESTATION_REPLAY_LEDGER")
        ledger = Path(configured) if configured else None
    trust_policy = None
    if ledger is None:
        errors.append("external attestation replay ledger is not configured")
    else:
        try:
            trust_policy = load_trust_policy(
                root, base_sha, replay_ledger_path=ledger
            ).verifier
        except EvidenceStoreError as exc:
            errors.append(str(exc))
    try:
        recovery = TransactionManager(root).incomplete()
    except TransactionError as exc:
        recovery = ()
        errors.append(str(exc))
    if recovery:
        errors.append("RECOVERY_REQUIRED: " + ", ".join(recovery))
    context = ReportContext(
        root,
        manifest,
        profiles,
        FingerprintStore(root),
        trust_policy,
        waivers,
        now,
    )
    return context, errors, recovery


def build_canonical_report(
    root: Path,
    options: CanonicalReportOptions = CanonicalReportOptions(),
) -> dict[str, Any]:
    """Build a strict trusted report; never mutate repository-managed state."""
    repository_root = Path(root).resolve()
    context, errors, recovery = _report_context(repository_root, options)
    manifest = context.manifest
    profiles = context.profiles
    wanted = set(options.modules)
    selected = tuple(
        unit
        for unit in manifest.managed_units
        if not wanted
        or module_identity(unit.unit_id.prompt_relpath) in wanted
        or unit.unit_id.prompt_relpath.stem.rsplit("_", 1)[0] in wanted
        or unit.unit_id.prompt_relpath.as_posix() in wanted
    )
    verdicts = tuple(_unit_verdict(context, unit) for unit in selected)
    counts = _counts(manifest, profiles, context.waivers, verdicts, errors)
    return {
        "schema_version": 1,
        "ok": _predicate(counts) and len(selected) == len(manifest.managed_units),
        "project_root": str(repository_root),
        "repository_id": manifest.repository_id,
        "base_sha": manifest.base_ref,
        "head_sha": manifest.head_ref,
        "manifest_digest": manifest.digest(),
        "counts": counts.as_flat_dict(),
        "errors": sorted(set(errors)),
        "recovery_required": list(recovery),
        "units": [
            {
                "subject": verdict.subject.prompt_relpath.as_posix(),
                "inventory": verdict.inventory.value,
                "baseline": verdict.baseline.value,
                "semantic": verdict.semantic.value,
                "in_sync": verdict.in_sync,
                "evidence_complete": verdict.evidence_complete,
                "changed_roles": list(verdict.changed_roles),
                "reason": verdict.reason,
            }
            for verdict in verdicts
        ],
    }


def module_identity(prompt_path: PurePosixPath) -> str:
    """Return a language-stripped identity below an approved prompt root.

    Prompt roots are matched as complete path components so package-local
    ``pdd/prompts`` paths cannot be confused with unrelated similarly named
    directories or traversal-shaped inputs.
    """
    parts = prompt_path.parts
    if prompt_path.is_absolute() or ".." in parts:
        raise ValueError(f"prompt path is outside supported prompt roots: {prompt_path}")
    if parts[:1] == ("prompts",):
        relative = PurePosixPath(*parts[1:])
    elif parts[:2] == ("pdd", "prompts"):
        relative = PurePosixPath(*parts[2:])
    else:
        raise ValueError(f"prompt path is outside supported prompt roots: {prompt_path}")
    return relative.with_suffix("").as_posix().rsplit("_", 1)[0]
