"""Immutable value types shared by every synchronization consumer."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from enum import Enum
from pathlib import PurePosixPath
from typing import Optional, Union


class InventoryStatus(str, Enum):
    """Intrinsic ownership classification for a discovered subject."""

    MANAGED = "MANAGED"
    HUMAN_OWNED = "HUMAN_OWNED"
    REMOVED = "REMOVED"
    INVALID = "INVALID"


class BaselineStatus(str, Enum):
    """Relationship between current bytes and the trusted baseline."""

    CURRENT = "CURRENT"
    DRIFTED = "DRIFTED"
    UNBASELINED = "UNBASELINED"
    CORRUPT = "CORRUPT"


class SemanticStatus(str, Enum):
    """Current semantic agreement backed by validation evidence."""

    VERIFIED = "VERIFIED"
    UNKNOWN = "UNKNOWN"
    CONFLICT = "CONFLICT"
    FAILED = "FAILED"


class EvidenceOutcome(str, Enum):
    """Normalized terminal result for a verification obligation."""

    PASS = "PASS"
    FAIL = "FAIL"
    ERROR = "ERROR"
    COLLECTION_ERROR = "COLLECTION_ERROR"
    SKIP = "SKIP"
    XFAIL = "XFAIL"
    XPASS = "XPASS"
    DESELECTED = "DESELECTED"
    TIMEOUT = "TIMEOUT"
    NOT_COLLECTED = "NOT_COLLECTED"
    QUARANTINED = "QUARANTINED"
    FLAKY = "FLAKY"


class AssuranceLevel(str, Enum):
    """Strength of the execution boundary required by a verification profile."""

    STANDARD_FRAMEWORK = "standard_framework"
    ISOLATED_BLACK_BOX = "isolated_black_box"

    @property
    def strength(self) -> int:
        """Return the monotonic protection rank used during profile merging."""
        return {
            AssuranceLevel.STANDARD_FRAMEWORK: 0,
            AssuranceLevel.ISOLATED_BLACK_BOX: 1,
        }[self]

    def protects_at_least(self, other: AssuranceLevel) -> bool:
        """Return whether this level is no weaker than ``other``."""
        return self.strength >= other.strength


def _validate_repository_id(repository_id: str) -> None:
    if not repository_id or repository_id.strip() != repository_id:
        raise ValueError("repository_id must be a non-empty canonical identifier")


def _validate_relpath(path: PurePosixPath) -> None:
    if path.is_absolute() or not path.parts or ".." in path.parts:
        raise ValueError(f"path must be repository-relative: {path}")


@dataclass(frozen=True, order=True)
class CandidateId:
    """Stable identity for an artifact not yet adopted into a unit."""

    repository_id: str
    artifact_relpath: PurePosixPath
    role: str

    def __post_init__(self) -> None:
        _validate_repository_id(self.repository_id)
        _validate_relpath(self.artifact_relpath)
        if not self.role:
            raise ValueError("candidate role must not be empty")


@dataclass(frozen=True, order=True)
class UnitId:
    """Stable prompt-backed identity independent of checkout location."""

    repository_id: str
    prompt_relpath: PurePosixPath
    language_id: str

    def __post_init__(self) -> None:
        _validate_repository_id(self.repository_id)
        _validate_relpath(self.prompt_relpath)
        if not self.language_id:
            raise ValueError("language_id must not be empty")


SubjectId = Union[CandidateId, UnitId]


@dataclass(frozen=True, order=True)
class ArtifactSnapshot:
    """Policy-relevant state of one artifact at an instant."""

    role: str
    relpath: PurePosixPath
    digest: Optional[str]
    git_mode: Optional[str]
    required: bool = True

    def __post_init__(self) -> None:
        if not self.role:
            raise ValueError("artifact role must not be empty")
        _validate_relpath(self.relpath)
        if self.digest is not None and not self.digest:
            raise ValueError("artifact digest must be non-empty or None")
        if self.git_mode not in {None, "100644", "100755", "120000"}:
            raise ValueError(f"unsupported normalized Git mode: {self.git_mode}")

    @property
    def exists(self) -> bool:
        """Return whether both content and artifact mode are present."""
        return self.digest is not None and self.git_mode is not None


@dataclass(frozen=True)
class UnitSnapshot:
    """Complete hashable state consumed by the pure classifier."""

    unit_id: UnitId
    artifacts: tuple[ArtifactSnapshot, ...]
    manifest_digest: str
    dependency_snapshot_digest: str
    verification_profile_digest: str
    nondeterministic_inputs: bool = False

    def __post_init__(self) -> None:
        identities = [(artifact.role, artifact.relpath) for artifact in self.artifacts]
        if len(identities) != len(set(identities)):
            raise ValueError("artifact role/path identities must be unique")
        for value in (
            self.manifest_digest,
            self.dependency_snapshot_digest,
            self.verification_profile_digest,
        ):
            if not value:
                raise ValueError("snapshot closure digests must not be empty")

    def artifact_map(self) -> dict[tuple[str, PurePosixPath], ArtifactSnapshot]:
        """Index artifacts by role and repository-relative path."""
        return {(artifact.role, artifact.relpath): artifact for artifact in self.artifacts}

    def digest(self) -> str:
        """Return a deterministic digest of the complete snapshot closure."""
        payload = {
            "unit_id": {
                "repository_id": self.unit_id.repository_id,
                "prompt_relpath": self.unit_id.prompt_relpath.as_posix(),
                "language_id": self.unit_id.language_id,
            },
            "artifacts": [
                {
                    "role": item.role,
                    "path": item.relpath.as_posix(),
                    "digest": item.digest,
                    "git_mode": item.git_mode,
                    "required": item.required,
                }
                for item in sorted(self.artifacts)
            ],
            "manifest_digest": self.manifest_digest,
            "dependency_snapshot_digest": self.dependency_snapshot_digest,
            "verification_profile_digest": self.verification_profile_digest,
            "nondeterministic_inputs": self.nondeterministic_inputs,
        }
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(encoded).hexdigest()


@dataclass(frozen=True, order=True)
class VerificationObligation:
    """One protected requirement that must receive trusted evidence."""
    # pylint: disable=too-many-instance-attributes

    obligation_id: str
    kind: str
    validator_id: str
    validator_config_digest: str
    requirement_ids: tuple[str, ...]
    artifact_paths: tuple[PurePosixPath, ...]
    required: bool = True
    code_under_test_paths: tuple[PurePosixPath, ...] = ()

    def __post_init__(self) -> None:
        if not self.obligation_id or not self.kind or not self.validator_id:
            raise ValueError("verification obligation identity must be complete")
        if not self.validator_config_digest:
            raise ValueError("validator config digest must not be empty")
        for path in self.artifact_paths:
            _validate_relpath(path)
        for path in self.code_under_test_paths:
            _validate_relpath(path)


@dataclass(frozen=True)
class VerificationProfile:
    """Protected set of obligations for a unit."""

    unit_id: UnitId
    obligations: tuple[VerificationObligation, ...]
    required_requirement_ids: tuple[str, ...]
    profile_digest: str
    assurance: AssuranceLevel = AssuranceLevel.STANDARD_FRAMEWORK

    def __post_init__(self) -> None:
        obligation_ids = [item.obligation_id for item in self.obligations]
        if len(obligation_ids) != len(set(obligation_ids)):
            raise ValueError("verification profile contains duplicate obligation IDs")
        if len(self.required_requirement_ids) != len(set(self.required_requirement_ids)):
            raise ValueError("verification profile contains duplicate requirement IDs")
        if not self.profile_digest:
            raise ValueError("verification profile digest must not be empty")
        if not isinstance(self.assurance, AssuranceLevel):
            try:
                object.__setattr__(self, "assurance", AssuranceLevel(self.assurance))
            except ValueError as exc:
                raise ValueError("unsupported verification assurance level") from exc

    @property
    def complete(self) -> bool:
        """Return whether required obligations cover every declared requirement."""
        required_obligations = tuple(item for item in self.obligations if item.required)
        if not required_obligations or not self.required_requirement_ids:
            return False
        covered = {
            requirement_id
            for item in required_obligations
            for requirement_id in item.requirement_ids
        }
        required = set(self.required_requirement_ids)
        if covered != required:
            return False
        opaque = {item for item in required if item.startswith("CONTRACT-SHA256:")}
        human_covered = {
            requirement_id
            for item in required_obligations
            if item.kind == "human-attestation"
            and item.validator_id == "threshold-ed25519"
            for requirement_id in item.requirement_ids
        }
        return opaque.issubset(human_covered)


@dataclass(frozen=True, order=True)
class ObligationEvidence:
    """Trusted-checker result for one obligation."""

    obligation_id: str
    outcome: EvidenceOutcome


@dataclass(frozen=True)
# pylint: disable=too-many-instance-attributes
class FingerprintProvenance:
    """Auditable origin of one canonical fingerprint transition."""

    kind: str
    command: str
    transaction_id: str
    git_commit: str
    timestamp: str
    pdd_version: str
    reviewed_by: Optional[str] = None
    reason: Optional[str] = None


@dataclass(frozen=True)
class FingerprintRecord:
    """Versioned baseline snapshot with transaction provenance."""

    snapshot: UnitSnapshot
    schema_version: int
    hash_algorithm_version: int
    provenance: FingerprintProvenance
    claimed_semantic_status: SemanticStatus
    attestation_ref: Optional[str]

    @property
    def valid(self) -> bool:
        """Return whether the record uses the authoritative v2 schema."""
        return (
            self.schema_version == 2
            and self.hash_algorithm_version == 2
            and bool(self.provenance.kind)
            and bool(self.provenance.command)
            and bool(self.provenance.transaction_id)
            and bool(self.provenance.git_commit)
            and bool(self.provenance.timestamp)
            and bool(self.provenance.pdd_version)
        )


@dataclass(frozen=True)
class VerdictDetails:
    """Diagnostic details kept separate from the core status dimensions."""

    changed_roles: tuple[str, ...]
    reason: str
    required_artifacts_missing: tuple[str, ...] = ()
    evidence_complete: bool = False


@dataclass(frozen=True)
class SyncVerdict:
    """Independent inventory, baseline, and semantic classifications."""

    subject: SubjectId
    inventory: InventoryStatus
    baseline: BaselineStatus
    semantic: SemanticStatus
    details: VerdictDetails

    @property
    def changed_roles(self) -> tuple[str, ...]:
        """Return roles that differ from the baseline."""
        return self.details.changed_roles

    @property
    def reason(self) -> str:
        """Return the stable human-readable verdict explanation."""
        return self.details.reason

    @property
    def required_artifacts_missing(self) -> tuple[str, ...]:
        """Return required artifact roles absent from the current snapshot."""
        return self.details.required_artifacts_missing

    @property
    def evidence_complete(self) -> bool:
        """Return whether trusted evidence covers every required obligation."""
        return self.details.evidence_complete

    @property
    def in_sync(self) -> bool:
        """Return true only for the complete trusted managed predicate."""
        return (
            self.inventory is InventoryStatus.MANAGED
            and self.baseline is BaselineStatus.CURRENT
            and self.semantic is SemanticStatus.VERIFIED
            and not self.required_artifacts_missing
            and self.evidence_complete
        )
