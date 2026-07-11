"""Tests for untrusted evidence storage and protected-base trust roots."""

import base64
import json
import subprocess
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

import pytest

from pdd.sync_core import (
    AttestationBinding,
    AttestationRequest,
    AttestationSigner,
    AttestationTrustPolicy,
    EvidenceStoreError,
    EvidenceOutcome,
    decode_attestation,
    encode_attestation,
    load_trust_policy,
)
from pdd.sync_core.types import ObligationEvidence, UnitId


PRIVATE_KEY = b"e" * 32
SIGNER = AttestationSigner("trusted-ci", PRIVATE_KEY)
UNIT = UnitId("repository-1", PurePosixPath("prompts/widget_python.prompt"), "python")


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _envelope():
    binding = AttestationBinding(
        UNIT, "snapshot", "profile", "runner", "pdd-test", "base", "head"
    )
    return SIGNER.issue(
        AttestationRequest(
            "attestation-1",
            binding,
            (ObligationEvidence("test", EvidenceOutcome.PASS),),
            "nonce-1",
            datetime(2026, 7, 10, 12, 0, tzinfo=timezone.utc),
        )
    )


def test_attestation_json_round_trip_preserves_signed_payload() -> None:
    envelope = _envelope()
    decoded = decode_attestation(json.loads(encode_attestation(envelope)))
    assert decoded == envelope
    assert decoded.payload() == envelope.payload()


def test_attestation_json_round_trip_preserves_playwright_command() -> None:
    envelope = _envelope()
    envelope = replace(
        envelope,
        binding=replace(
            envelope.binding,
            playwright_command=("/opt/node", "/opt/playwright/cli.js"),
        ),
    )
    decoded = decode_attestation(json.loads(encode_attestation(envelope)))
    assert decoded == envelope
    assert decoded.payload() == envelope.payload()


def test_pre_closure_signed_envelope_uses_explicit_legacy_payload_shape() -> None:
    envelope = _envelope()
    payload = json.loads(encode_attestation(envelope))
    payload.pop("payload_version", None)
    payload["binding"].pop("artifact_closure_digest")
    payload.pop("signature")
    legacy_bytes = json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    ).encode()
    payload["signature"] = SIGNER.sign_bytes(legacy_bytes)

    decoded = decode_attestation(payload)

    assert decoded.payload_version == 1
    assert decoded.payload() == legacy_bytes
    AttestationTrustPolicy({SIGNER.issuer: SIGNER.public_key_bytes()}).verify(
        decoded,
        decoded.binding,
        now=datetime(2026, 7, 10, 12, 1, tzinfo=timezone.utc),
    )


def test_unknown_attestation_payload_version_is_rejected() -> None:
    payload = json.loads(encode_attestation(_envelope()))
    payload["payload_version"] = 99

    with pytest.raises(EvidenceStoreError, match="payload version"):
        decode_attestation(payload)


def test_candidate_cannot_replace_protected_base_public_key(tmp_path) -> None:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "trust@example.com")
    _git(root, "config", "user.name", "Trust Test")
    policy_path = root / ".pdd/attestation-trust.json"
    policy_path.parent.mkdir()
    protected_key = base64.b64encode(SIGNER.public_key_bytes()).decode("ascii")
    policy_path.write_text(
        json.dumps(
            {
                "issuers": [
                    {"issuer_id": "trusted-ci", "public_key": protected_key}
                ],
                "revoked_issuers": [],
                "revoked_attestations": [],
            }
        )
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected trust")
    base = _git(root, "rev-parse", "HEAD")
    candidate = AttestationSigner("trusted-ci", b"x" * 32)
    policy_path.write_text(
        json.dumps(
            {
                "issuers": [
                    {
                        "issuer_id": "trusted-ci",
                        "public_key": base64.b64encode(
                            candidate.public_key_bytes()
                        ).decode("ascii"),
                    }
                ]
            }
        )
    )
    loaded = load_trust_policy(
        root,
        base,
        replay_ledger_path=tmp_path / "external-trust/replay.json",
    )
    assert loaded.issuer_ids == ("trusted-ci",)
    assert loaded.digest
    assert loaded.verifier.verify(
        _envelope(), _envelope().binding, now=datetime(2026, 7, 10, 12, 1, tzinfo=timezone.utc)
    )
