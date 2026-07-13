"""Contract tests for the side-effect-free canonical sync classifier."""

from datetime import datetime, timezone
from pathlib import PurePosixPath

import pytest

from pdd.sync_core import (
    ArtifactSnapshot,
    AttestationBinding,
    AttestationRequest,
    AttestationSigner,
    AttestationTrustPolicy,
    BaselineStatus,
    EvidenceOutcome,
    FingerprintRecord,
    FingerprintProvenance,
    InventoryStatus,
    SemanticStatus,
    UnitId,
    UnitSnapshot,
    ValidationEvidence,
    VerificationObligation,
    VerificationProfile,
    classify,
)
from pdd.sync_core.types import ObligationEvidence


UNIT_ID = UnitId("repository-1", PurePosixPath("prompts/widget_python.prompt"), "python")
NOW = datetime(2026, 7, 10, 12, 0, tzinfo=timezone.utc)
PRIVATE_KEY = b"c" * 32
SIGNER = AttestationSigner("trusted-ci", PRIVATE_KEY)
PUBLIC_KEY = SIGNER.public_key_bytes()


def _snapshot(**digests: str | None) -> UnitSnapshot:
    values = {
        "prompt": "prompt-v1",
        "include": "include-v1",
        "code": "code-v1",
        "example": "example-v1",
        "test": "test-v1",
    }
    values.update(digests)
    return UnitSnapshot(
        UNIT_ID,
        tuple(
            ArtifactSnapshot(
                role,
                PurePosixPath(
                    {
                        "prompt": "prompts/widget_python.prompt",
                        "include": "docs/widget.md",
                        "code": "src/widget.py",
                        "example": "examples/widget_example.py",
                        "test": "tests/test_widget.py",
                    }[role]
                ),
                digest,
                "100644" if digest is not None else None,
            )
            for role, digest in values.items()
        ),
        manifest_digest="manifest-v1",
        dependency_snapshot_digest="graph-v1",
        verification_profile_digest="profile-v1",
    )


def _profile() -> VerificationProfile:
    return VerificationProfile(
        UNIT_ID,
        (
            VerificationObligation(
                "tests",
                "test",
                "pytest",
                "pytest-config-v1",
                ("REQ-1",),
                (PurePosixPath("tests/test_widget.py"),),
            ),
        ),
        ("REQ-1",),
        "profile-v1",
    )


def _evidence(snapshot: UnitSnapshot, outcome: EvidenceOutcome = EvidenceOutcome.PASS) -> ValidationEvidence:
    binding = AttestationBinding(
        UNIT_ID,
        snapshot.digest(),
        "profile-v1",
        "pytest-v1",
        "pdd-test",
        "base-1",
        "head-1",
    )
    envelope = SIGNER.issue(
        AttestationRequest(
            "attestation-1",
            binding,
            (ObligationEvidence("tests", outcome),),
            "nonce-1",
            NOW,
        )
    )
    return AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}).verify(
        envelope, binding, now=NOW
    )


def _baseline(snapshot: UnitSnapshot) -> FingerprintRecord:
    provenance = FingerprintProvenance(
        "generated",
        "pdd sync widget",
        "transaction-1",
        "head-1",
        "2026-07-10T12:00:00+00:00",
        "pdd-test",
    )
    return FingerprintRecord(
        snapshot, 2, 2, provenance, SemanticStatus.VERIFIED, "attestation-1"
    )


def test_current_hashes_without_evidence_are_not_in_sync() -> None:
    snapshot = _snapshot()
    verdict = classify(snapshot, _baseline(snapshot), _profile(), None)
    assert verdict.baseline is BaselineStatus.CURRENT
    assert verdict.semantic is SemanticStatus.UNKNOWN
    assert verdict.in_sync is False


def test_complete_trusted_current_evidence_is_in_sync() -> None:
    snapshot = _snapshot()
    verdict = classify(snapshot, _baseline(snapshot), _profile(), _evidence(snapshot))
    assert verdict.semantic is SemanticStatus.VERIFIED
    assert verdict.in_sync is True


@pytest.mark.parametrize("outcome", [EvidenceOutcome.SKIP, EvidenceOutcome.XFAIL, EvidenceOutcome.FLAKY])
def test_non_passing_evidence_cannot_verify(outcome) -> None:
    snapshot = _snapshot()
    verdict = classify(snapshot, _baseline(snapshot), _profile(), _evidence(snapshot, outcome))
    assert verdict.semantic is SemanticStatus.UNKNOWN
    assert verdict.in_sync is False


def test_prompt_and_code_coedit_is_conflict() -> None:
    baseline = _snapshot()
    current = _snapshot(prompt="prompt-v2", code="code-v2")
    verdict = classify(current, _baseline(baseline), _profile(), _evidence(current))
    assert verdict.baseline is BaselineStatus.DRIFTED
    assert verdict.semantic is SemanticStatus.CONFLICT
    assert verdict.changed_roles == ("code", "prompt")
    assert verdict.in_sync is False


@pytest.mark.parametrize("role", ["prompt", "include", "code", "example", "test"])
def test_one_sided_drift_never_accepts_current_hashes(role: str) -> None:
    baseline = _snapshot()
    current = _snapshot(**{role: f"{role}-v2"})
    verdict = classify(current, _baseline(baseline), _profile(), _evidence(current))
    assert verdict.baseline is BaselineStatus.DRIFTED
    assert verdict.semantic is SemanticStatus.UNKNOWN
    assert verdict.in_sync is False


def test_missing_required_artifact_fails() -> None:
    baseline = _snapshot()
    current = _snapshot(code=None)
    verdict = classify(current, _baseline(baseline), _profile(), None)
    assert verdict.baseline is BaselineStatus.DRIFTED
    assert verdict.semantic is SemanticStatus.FAILED
    assert verdict.required_artifacts_missing == ("code",)


def test_mode_only_change_is_drift() -> None:
    baseline = _snapshot()
    artifacts = tuple(
        ArtifactSnapshot(
            item.role,
            item.relpath,
            item.digest,
            "100755" if item.role == "code" else item.git_mode,
        )
        for item in baseline.artifacts
    )
    current = UnitSnapshot(
        UNIT_ID,
        artifacts,
        baseline.manifest_digest,
        baseline.dependency_snapshot_digest,
        baseline.verification_profile_digest,
    )
    verdict = classify(current, _baseline(baseline), _profile(), None)
    assert verdict.baseline is BaselineStatus.DRIFTED
    assert verdict.changed_roles == ("code",)


def test_missing_baseline_is_unknown_not_current() -> None:
    verdict = classify(_snapshot(), None, _profile(), None)
    assert verdict.baseline is BaselineStatus.UNBASELINED
    assert verdict.semantic is SemanticStatus.UNKNOWN
    assert verdict.in_sync is False


def test_invalid_inventory_fails_closed() -> None:
    snapshot = _snapshot()
    verdict = classify(
        snapshot,
        _baseline(snapshot),
        _profile(),
        _evidence(snapshot),
        inventory=InventoryStatus.INVALID,
    )
    assert verdict.baseline is BaselineStatus.CORRUPT
    assert verdict.semantic is SemanticStatus.FAILED
    assert verdict.in_sync is False


def test_empty_profile_and_evidence_cannot_verify() -> None:
    snapshot = _snapshot()
    profile = VerificationProfile(UNIT_ID, (), (), "profile-v1")
    binding = AttestationBinding(
        UNIT_ID,
        snapshot.digest(),
        "profile-v1",
        "pytest-v1",
        "pdd-test",
        "base-1",
        "head-1",
    )
    envelope = SIGNER.issue(
        AttestationRequest(
            "attestation-empty",
            binding,
            (),
            "nonce-empty",
            NOW,
        )
    )
    evidence = AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}).verify(
        envelope, binding, now=NOW
    )
    verdict = classify(snapshot, _baseline(snapshot), profile, evidence)
    assert profile.complete is False
    assert verdict.semantic is SemanticStatus.UNKNOWN
    assert verdict.in_sync is False


def test_duplicate_obligation_ids_are_rejected() -> None:
    obligation = VerificationObligation(
        "duplicate",
        "test",
        "pytest",
        "pytest-v1",
        ("REQ-1",),
        (PurePosixPath("tests/test_widget.py"),),
    )
    with pytest.raises(ValueError, match="duplicate obligation"):
        VerificationProfile(
            UNIT_ID,
            (obligation, obligation),
            ("REQ-1",),
            "profile-duplicate",
        )


def test_multiple_artifacts_with_same_role_are_preserved() -> None:
    snapshot = _snapshot()
    second_test = ArtifactSnapshot(
        "test",
        PurePosixPath("tests/test_widget_integration.py"),
        "integration-test-v1",
        "100644",
    )
    baseline = UnitSnapshot(
        snapshot.unit_id,
        snapshot.artifacts + (second_test,),
        snapshot.manifest_digest,
        snapshot.dependency_snapshot_digest,
        snapshot.verification_profile_digest,
    )
    changed_test = ArtifactSnapshot(
        "test",
        second_test.relpath,
        "integration-test-v2",
        "100644",
    )
    current = UnitSnapshot(
        snapshot.unit_id,
        snapshot.artifacts + (changed_test,),
        snapshot.manifest_digest,
        snapshot.dependency_snapshot_digest,
        snapshot.verification_profile_digest,
    )
    verdict = classify(current, _baseline(baseline), _profile(), None)
    assert verdict.changed_roles == ("test",)
    assert len(current.artifact_map()) == 6


def test_nondeterministic_input_cannot_be_verified_by_execution_evidence() -> None:
    snapshot = _snapshot()
    nondeterministic = UnitSnapshot(
        snapshot.unit_id,
        snapshot.artifacts,
        snapshot.manifest_digest,
        snapshot.dependency_snapshot_digest,
        snapshot.verification_profile_digest,
        nondeterministic_inputs=True,
    )
    verdict = classify(
        nondeterministic,
        _baseline(nondeterministic),
        _profile(),
        _evidence(nondeterministic),
    )
    assert verdict.semantic is SemanticStatus.UNKNOWN
    assert verdict.in_sync is False
