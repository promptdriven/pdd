"""Tests for untrusted evidence storage and protected-base trust roots."""

import base64
import json
import subprocess
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

from pdd.sync_core import (
    AttestationBinding,
    AttestationRequest,
    AttestationSigner,
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


def test_attestation_json_round_trip_preserves_playwright_toolchain_identity() -> None:
    envelope = _envelope()
    envelope = replace(
        envelope,
        binding=replace(
            envelope.binding,
            playwright_toolchain_identity="3e5f" * 16,
        ),
    )
    decoded = decode_attestation(json.loads(encode_attestation(envelope)))
    assert decoded == envelope
    assert decoded.payload() == envelope.payload()


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
