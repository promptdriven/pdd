"""Adversarial tests for trusted semantic evidence issuance."""

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
    UnitId,
)
from pdd.sync_core.trust import ValidationEvidence
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
    envelope = _envelope(nonce="nonce-long", lifetime=timedelta(hours=2))
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


def test_exact_signed_statement_replay_is_rejected() -> None:
    policy = AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY})
    envelope = _envelope()
    _verify(policy, envelope)
    with pytest.raises(AttestationError, match="replayed"):
        _verify(policy, envelope)


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
