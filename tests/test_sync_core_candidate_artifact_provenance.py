"""Strict tests for protected candidate-wheel build provenance."""
# pylint: disable=missing-function-docstring,line-too-long

import hashlib
import json
import threading
from datetime import datetime, timedelta, timezone

import pytest

from pdd.sync_core import AttestationSigner
from pdd.sync_core.artifact_provenance import (
    CandidateArtifactPolicy,
    CandidateArtifactProvenanceError,
    load_candidate_artifact_provenance,
)


SOURCE_SHA = "a" * 40
LOCK_SHA256 = "b" * 64
WORKFLOW = "promptdriven/pdd/.github/workflows/candidate-wheel.yml@refs/heads/main"
TARGET = {
    "implementation": "CPython",
    "version": "3.12.3",
    "abi": "cp312",
    "platform": "manylinux_2_17_x86_64",
}


def _policy(authority: AttestationSigner) -> CandidateArtifactPolicy:
    return CandidateArtifactPolicy(
        authority.issuer,
        authority.public_key_bytes(),
        WORKFLOW,
        LOCK_SHA256,
        TARGET["implementation"],
        TARGET["version"],
        TARGET["abi"],
        TARGET["platform"],
    )


def _policy_with_replay_ledger(authority: AttestationSigner, replay_ledger) -> CandidateArtifactPolicy:
    policy = _policy(authority)
    policy.replay_ledger_path = replay_ledger
    return policy


def _attestation(
    wheel,
    authority: AttestationSigner,
    **overrides,
) -> dict:
    now = datetime.now(timezone.utc)
    payload = {
        "schema_version": 1,
        "issuer": authority.issuer,
        "attestation_id": "candidate-build-123",
        "nonce": "candidate-build-nonce-123",
        "issued_at": now.isoformat(),
        "expires_at": (now + timedelta(minutes=10)).isoformat(),
        "wheel_sha256": hashlib.sha256(wheel.read_bytes()).hexdigest(),
        "source_sha": SOURCE_SHA,
        "dependency_lock_sha256": LOCK_SHA256,
        "python": TARGET,
        "builder_workflow_identity": WORKFLOW,
    }
    payload.update(overrides)
    payload["signature"] = {
        "algorithm": "Ed25519",
        "value": authority.sign_bytes(
            json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        ),
    }
    return payload


def _load(tmp_path, wheel, authority, **overrides):
    path = tmp_path / "candidate-build-attestation.json"
    path.write_text(json.dumps(_attestation(wheel, authority, **overrides)))
    return load_candidate_artifact_provenance(path, wheel, _policy(authority))


def test_unrelated_wheel_cannot_use_another_wheels_attestation(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    certified = tmp_path / "certified.whl"
    unrelated = tmp_path / "unrelated.whl"
    certified.write_bytes(b"certified candidate wheel")
    unrelated.write_bytes(b"unrelated candidate wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match="digest"):
        _load(tmp_path, unrelated, authority, wheel_sha256=hashlib.sha256(certified.read_bytes()).hexdigest())


def test_correct_wheel_with_wrong_certified_source_sha_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match="source SHA"):
        _load(tmp_path, wheel, authority, source_sha="c" * 40).verify(
            _policy(authority), expected_source_sha=SOURCE_SHA
        )


def test_forged_build_attestation_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    path = tmp_path / "candidate-build-attestation.json"
    forged = _attestation(wheel, authority)
    forged["source_sha"] = "c" * 40
    path.write_text(json.dumps(forged))
    with pytest.raises(CandidateArtifactProvenanceError, match="signature"):
        load_candidate_artifact_provenance(path, wheel, _policy(authority))


def test_stale_or_replayed_build_attestation_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match="expired"):
        _load(
            tmp_path,
            wheel,
            authority,
            issued_at=(datetime.now(timezone.utc) - timedelta(hours=2)).isoformat(),
            expires_at=(datetime.now(timezone.utc) - timedelta(hours=1)).isoformat(),
        )
    policy = _policy(authority)
    provenance = _load(tmp_path, wheel, authority)
    provenance.verify(policy, expected_source_sha=SOURCE_SHA)
    with pytest.raises(CandidateArtifactProvenanceError, match="replayed"):
        provenance.verify(policy, expected_source_sha=SOURCE_SHA)


def test_replayed_build_attestation_is_rejected_across_policy_instances(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    replay_ledger = tmp_path / "external-candidate-replay.json"
    provenance = _load(tmp_path, wheel, authority)
    provenance.verify(
        _policy_with_replay_ledger(authority, replay_ledger),
        expected_source_sha=SOURCE_SHA,
    )
    with pytest.raises(CandidateArtifactProvenanceError, match="replayed"):
        provenance.verify(
            _policy_with_replay_ledger(authority, replay_ledger),
            expected_source_sha=SOURCE_SHA,
        )


def test_concurrent_durable_replay_consumers_are_atomic(tmp_path, monkeypatch) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    replay_ledger = tmp_path / "external-candidate-replay.json"
    provenance = _load(tmp_path, wheel, authority)
    write_barrier = threading.Barrier(2)
    original_write_text = type(replay_ledger).write_text

    def synchronized_ledger_write(path, *args, **kwargs):
        if path == replay_ledger:
            write_barrier.wait(timeout=5)
        return original_write_text(path, *args, **kwargs)

    monkeypatch.setattr(type(replay_ledger), "write_text", synchronized_ledger_write)
    results: list[str] = []
    lock = threading.Lock()

    def consume() -> None:
        try:
            provenance.verify(
                _policy_with_replay_ledger(authority, replay_ledger),
                expected_source_sha=SOURCE_SHA,
            )
            outcome = "accepted"
        except CandidateArtifactProvenanceError as exc:
            outcome = str(exc)
        with lock:
            results.append(outcome)

    threads = [threading.Thread(target=consume) for _ in range(2)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(timeout=10)

    assert sorted(results) == ["accepted", "candidate attestation is replayed"]


@pytest.mark.parametrize(
    ("field", "value", "error"),
    [
        ("builder_workflow_identity", "attacker/workflow@main", "builder workflow"),
        ("dependency_lock_sha256", "c" * 64, "dependency lock"),
        ("python", {**TARGET, "abi": "cp313"}, "interpreter"),
    ],
)
def test_wrong_protected_build_environment_is_rejected(tmp_path, field, value, error) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match=error):
        _load(tmp_path, wheel, authority, **{field: value}).verify(
            _policy(authority), expected_source_sha=SOURCE_SHA
        )


def test_source_checkout_is_not_a_candidate_artifact(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    checkout = tmp_path / "pdd"
    checkout.mkdir()
    path = tmp_path / "candidate-build-attestation.json"
    path.write_text(json.dumps(_attestation(wheel, authority)))
    with pytest.raises(CandidateArtifactProvenanceError, match="wheel path"):
        load_candidate_artifact_provenance(path, checkout, _policy(authority))


def test_valid_exact_sha_artifact_is_accepted(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    provenance = _load(tmp_path, wheel, authority)
    provenance.verify(_policy(authority), expected_source_sha=SOURCE_SHA)
    assert provenance.source_sha == SOURCE_SHA
    assert provenance.wheel_sha256 == hashlib.sha256(wheel.read_bytes()).hexdigest()
