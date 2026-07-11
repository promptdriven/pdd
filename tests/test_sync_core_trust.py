"""Adversarial tests for trusted semantic evidence issuance."""

import base64
import json
import subprocess
from dataclasses import replace
from datetime import datetime, timedelta, timezone
from pathlib import PurePosixPath

import pytest

from pdd.sync_core import (
    AttestationError,
    AttestationBinding,
    AttestationRequest,
    AttestationSigner,
    AttestationTrustPolicy,
    EvidenceOutcome,
    FileReplayStore,
    RemoteAttestationSigner,
    UnitId,
)
from pdd.sync_core.trust import ValidationEvidence
from pdd.sync_core.finalize import attestation_signer_from_environment
from pdd.sync_core.types import ObligationEvidence


PRIVATE_KEY = b"t" * 32
SIGNER = AttestationSigner("trusted-ci", PRIVATE_KEY)
PUBLIC_KEY = SIGNER.public_key_bytes()
NOW = datetime(2026, 7, 10, 12, 0, tzinfo=timezone.utc)
UNIT = UnitId("repository-1", PurePosixPath("prompts/widget_python.prompt"), "python")


def _envelope(*, nonce="nonce-1", issued_at=NOW, lifetime=timedelta(hours=1)):
    return SIGNER.issue(
        AttestationRequest(
            "attestation-1",
            _binding(),
            (ObligationEvidence("test", EvidenceOutcome.PASS),),
            nonce,
            issued_at,
            lifetime,
        )
    )


def _binding(**overrides):
    values = {
        "subject": UNIT,
        "snapshot_digest": "snapshot-1",
        "profile_digest": "profile-1",
        "runner_digest": "runner-1",
        "tool_version": "pdd-test",
        "base_sha": "base-1",
        "checked_sha": "head-1",
    }
    values.update(overrides)
    return AttestationBinding(**values)


def _verify(policy, envelope, **overrides):
    now = overrides.pop("now", NOW)
    return policy.verify(envelope, _binding(**overrides), now=now)


def test_valid_attestation_produces_sealed_evidence() -> None:
    evidence = _verify(AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}), _envelope())
    assert isinstance(evidence, ValidationEvidence)
    assert evidence.attestation_id == "attestation-1"


def test_remote_attestation_authority_signature_is_verified(monkeypatch) -> None:
    request = AttestationRequest(
        "remote-attestation",
        _binding(),
        (ObligationEvidence("test", EvidenceOutcome.PASS),),
        "remote-nonce",
        NOW,
    )

    def remote_sign(command, *, input, capture_output, check):
        assert command == ("protected-attestation-sign",)
        assert capture_output is True and check is False
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=SIGNER.sign_bytes(input).encode("ascii"),
            stderr=b"",
        )

    monkeypatch.setattr("pdd.sync_core.trust.subprocess.run", remote_sign)
    signer = RemoteAttestationSigner(
        SIGNER.issuer, SIGNER.public_key_bytes(), ("protected-attestation-sign",)
    )
    envelope = signer.issue(request)
    evidence = AttestationTrustPolicy(
        {SIGNER.issuer: SIGNER.public_key_bytes()}
    ).verify(envelope, request.binding, now=NOW)
    assert evidence.attestation_id == request.attestation_id


def test_attestation_environment_forbids_local_private_key(monkeypatch) -> None:
    monkeypatch.setenv("PDD_ATTESTATION_SIGNING_KEY", "candidate-secret")
    with pytest.raises(ValueError, match="local attestation signing keys are forbidden"):
        attestation_signer_from_environment()


def test_attestation_environment_builds_remote_authority(monkeypatch) -> None:
    monkeypatch.setenv("PDD_ATTESTATION_ISSUER", SIGNER.issuer)
    monkeypatch.setenv(
        "PDD_ATTESTATION_PUBLIC_KEY",
        base64.b64encode(SIGNER.public_key_bytes()).decode("ascii"),
    )
    monkeypatch.setenv(
        "PDD_ATTESTATION_SIGNER_COMMAND",
        json.dumps(["protected-attestation-sign"]),
    )
    assert isinstance(attestation_signer_from_environment(), RemoteAttestationSigner)


def test_evidence_cannot_be_caller_asserted() -> None:
    with pytest.raises(TypeError, match="AttestationTrustPolicy"):
        ValidationEvidence(
            object(),
            _seal=object(),
        )


def test_forged_signature_is_rejected() -> None:
    envelope = replace(_envelope(), binding=_binding(checked_sha="candidate-head"))
    with pytest.raises(AttestationError, match="signature"):
        _verify(AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}), envelope)


def test_unknown_issuer_is_rejected() -> None:
    with pytest.raises(AttestationError, match="not trusted"):
        _verify(AttestationTrustPolicy({}), _envelope())


def test_expired_attestation_is_rejected() -> None:
    envelope = _envelope(issued_at=NOW - timedelta(hours=2), lifetime=timedelta(minutes=1))
    with pytest.raises(AttestationError, match="expired"):
        _verify(AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}), envelope)


def test_overlong_attestation_lifetime_is_rejected() -> None:
    envelope = _envelope(nonce="nonce-long", lifetime=timedelta(days=9))
    with pytest.raises(AttestationError, match="exceeds policy"):
        _verify(AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}), envelope)


@pytest.mark.parametrize(
    ("policy", "message"),
    [
        (AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}, revoked_issuers=frozenset({"trusted-ci"})), "issuer is revoked"),
        (AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}, revoked_attestations=frozenset({"attestation-1"})), "attestation is revoked"),
    ],
)
def test_revocation_is_enforced(policy, message) -> None:
    with pytest.raises(AttestationError, match=message):
        _verify(policy, _envelope())


def test_nonce_reuse_by_different_attestation_is_rejected() -> None:
    policy = AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY})
    first = _envelope()
    _verify(policy, first)
    second = SIGNER.issue(
        AttestationRequest(
            "attestation-2",
            _binding(),
            first.results,
            "nonce-1",
            NOW,
        )
    )
    with pytest.raises(AttestationError, match="replayed"):
        _verify(policy, second)


def test_exact_signed_statement_recheck_is_idempotent() -> None:
    policy = AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY})
    envelope = _envelope()
    first = _verify(policy, envelope)
    second = _verify(policy, envelope)
    assert first.attestation_id == second.attestation_id == "attestation-1"


def test_durable_nonce_collision_is_rejected_across_policy_instances(tmp_path) -> None:
    path = tmp_path / "external/replay.json"
    envelope = _envelope()
    first = AttestationTrustPolicy(
        {"trusted-ci": PUBLIC_KEY}, replay_store=FileReplayStore(path)
    )
    second = AttestationTrustPolicy(
        {"trusted-ci": PUBLIC_KEY}, replay_store=FileReplayStore(path)
    )
    _verify(first, envelope)
    conflicting = SIGNER.issue(
        AttestationRequest(
            "attestation-conflict",
            _binding(),
            envelope.results,
            "nonce-1",
            NOW,
        )
    )
    with pytest.raises(AttestationError, match="replayed"):
        _verify(second, conflicting)
    assert path.stat().st_mode & 0o777 == 0o600


def test_durable_exact_statement_recheck_is_idempotent(tmp_path) -> None:
    path = tmp_path / "external/replay.json"
    envelope = _envelope()
    first = AttestationTrustPolicy(
        {"trusted-ci": PUBLIC_KEY}, replay_store=FileReplayStore(path)
    )
    second = AttestationTrustPolicy(
        {"trusted-ci": PUBLIC_KEY}, replay_store=FileReplayStore(path)
    )
    _verify(first, envelope)
    assert _verify(second, envelope).attestation_id == envelope.attestation_id


@pytest.mark.parametrize(
    "override",
    [
        {"snapshot_digest": "snapshot-2"},
        {"profile_digest": "profile-2"},
        {"base_sha": "base-2"},
        {"checked_sha": "head-2"},
    ],
)
def test_wrong_closure_binding_is_rejected(override) -> None:
    with pytest.raises(AttestationError, match="checked closure"):
        _verify(
            AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}),
            _envelope(),
            **override,
        )


def test_file_replay_store_rejects_symlink_lock(tmp_path) -> None:
    path = tmp_path / "replay.json"
    outside = tmp_path / "outside.lock"
    outside.write_text("do not touch")
    path.with_name("replay.json.lock").symlink_to(outside)
    store = FileReplayStore(path)
    with pytest.raises(AttestationError, match="unsafe"):
        store.consume("trusted-ci", "nonce", "attestation")
