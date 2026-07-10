"""Tests for canonical v2 fingerprint persistence and migration safety."""

import json
from pathlib import PurePosixPath

import pytest

from pdd.sync_core import (
    ArtifactSnapshot,
    CorruptFingerprintError,
    FingerprintProvenance,
    FingerprintRecord,
    FingerprintStore,
    FingerprintStoreError,
    SemanticStatus,
    UnitId,
    UnitSnapshot,
)
from pdd.sync_core.identity import initialize_repository_identity


REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
UNIT_ID = UnitId(
    REPOSITORY_ID, PurePosixPath("prompts/widget_python.prompt"), "python"
)


def _store(tmp_path):
    initialize_repository_identity(tmp_path, REPOSITORY_ID)
    return FingerprintStore(tmp_path)


def _record(*, kind="generated", semantic=SemanticStatus.VERIFIED, attestation="att-1"):
    snapshot = UnitSnapshot(
        UNIT_ID,
        (
            ArtifactSnapshot(
                "prompt",
                PurePosixPath("prompts/widget_python.prompt"),
                "prompt-hash",
                "100644",
            ),
            ArtifactSnapshot(
                "test",
                PurePosixPath("tests/test_widget.py"),
                "test-hash",
                "100644",
            ),
            ArtifactSnapshot(
                "test",
                PurePosixPath("tests/test_widget_e2e.py"),
                "e2e-hash",
                "100755",
            ),
        ),
        "manifest-hash",
        "graph-hash",
        "profile-hash",
    )
    provenance = FingerprintProvenance(
        kind,
        "pdd sync widget",
        "transaction-1",
        "head-1",
        "2026-07-10T12:00:00+00:00",
        "pdd-test",
        "reviewer@example.com" if kind == "baseline-reset" else None,
        "reviewed migration" if kind == "baseline-reset" else None,
    )
    return FingerprintRecord(snapshot, 2, 2, provenance, semantic, attestation)


def test_v2_round_trip_preserves_all_artifact_paths_and_modes(tmp_path) -> None:
    store = _store(tmp_path)
    record = _record()
    path = store.write(record)
    assert path.stat().st_mode & 0o777 == 0o644
    assert store.load(UNIT_ID) == record
    assert len(store.load(UNIT_ID).snapshot.artifacts) == 3


def test_corrupt_existing_record_fails_without_rewriting(tmp_path) -> None:
    store = _store(tmp_path)
    path = store.write(_record())
    path.write_text("{not-json", encoding="utf-8")
    before = path.read_bytes()
    with pytest.raises(CorruptFingerprintError):
        store.load(UNIT_ID)
    assert path.read_bytes() == before


def test_required_null_hash_is_rejected(tmp_path) -> None:
    store = _store(tmp_path)
    record = _record()
    missing = ArtifactSnapshot(
        "code", PurePosixPath("src/widget.py"), None, None, required=True
    )
    snapshot = UnitSnapshot(
        record.snapshot.unit_id,
        record.snapshot.artifacts + (missing,),
        record.snapshot.manifest_digest,
        record.snapshot.dependency_snapshot_digest,
        record.snapshot.verification_profile_digest,
    )
    invalid = FingerprintRecord(
        snapshot,
        2,
        2,
        record.provenance,
        record.claimed_semantic_status,
        record.attestation_ref,
    )
    with pytest.raises(FingerprintStoreError, match="null hash or mode"):
        store.write(invalid)


def test_verified_record_requires_attestation(tmp_path) -> None:
    with pytest.raises(FingerprintStoreError, match="requires an attestation"):
        _store(tmp_path).write(_record(attestation=None))


def test_baseline_reset_is_current_but_semantically_unknown(tmp_path) -> None:
    store = _store(tmp_path)
    record = _record(
        kind="baseline-reset", semantic=SemanticStatus.UNKNOWN, attestation=None
    )
    store.write(record)
    assert store.load(UNIT_ID).claimed_semantic_status is SemanticStatus.UNKNOWN
    with pytest.raises(FingerprintStoreError, match="must remain semantic UNKNOWN"):
        store.write(_record(kind="baseline-reset"))


def test_baseline_reset_requires_review_audit_fields(tmp_path) -> None:
    record = _record(
        kind="baseline-reset", semantic=SemanticStatus.UNKNOWN, attestation=None
    )
    provenance = FingerprintProvenance(
        record.provenance.kind,
        record.provenance.command,
        record.provenance.transaction_id,
        record.provenance.git_commit,
        record.provenance.timestamp,
        record.provenance.pdd_version,
    )
    with pytest.raises(FingerprintStoreError, match="reviewer and rationale"):
        _store(tmp_path).write(
            FingerprintRecord(record.snapshot, 2, 2, provenance, SemanticStatus.UNKNOWN, None)
        )


def test_legacy_record_is_readable_but_not_promoted(tmp_path) -> None:
    store = _store(tmp_path)
    legacy_path = tmp_path / ".pdd/meta/widget_python.json"
    legacy_path.parent.mkdir(parents=True, exist_ok=True)
    legacy_path.write_text(json.dumps({"prompt_hash": "legacy"}), encoding="utf-8")
    legacy = store.read_legacy(legacy_path)
    assert legacy.payload["prompt_hash"] == "legacy"
    assert store.load(UNIT_ID) is None


def test_embedded_identity_mismatch_is_corrupt(tmp_path) -> None:
    store = _store(tmp_path)
    path = store.write(_record())
    payload = json.loads(path.read_text(encoding="utf-8"))
    payload["unit_id"]["prompt_relpath"] = "prompts/other_python.prompt"
    path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(CorruptFingerprintError, match="embedded identity"):
        store.load(UNIT_ID)
