"""Contract tests for protected threshold-Ed25519 human approvals."""

import base64
import json
import subprocess
from datetime import datetime, timedelta, timezone
from pathlib import Path, PurePosixPath

import pytest
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from pdd.sync_core import (
    EvidenceOutcome,
    HumanAttestationError,
    HumanAttestationRequest,
    HumanAttestationVerifier,
    RunBinding,
    UnitId,
    VerificationObligation,
    VerificationProfile,
    load_human_attestation_policy,
)


NOW = datetime(2026, 7, 10, 12, 0, tzinfo=timezone.utc)
UNIT = UnitId("repository-1", PurePosixPath("prompts/widget.prompt"), "python")


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _key(seed: bytes) -> Ed25519PrivateKey:
    return Ed25519PrivateKey.from_private_bytes(seed * 32)


def _public(key: Ed25519PrivateKey) -> str:
    return base64.b64encode(key.public_key().public_bytes_raw()).decode("ascii")


def _request() -> HumanAttestationRequest:
    obligation = VerificationObligation(
        "human", "human-attestation", "threshold-ed25519", "policy-digest",
        ("CONTRACT-SHA256:abc",), (),
    )
    profile = VerificationProfile(
        UNIT, (obligation,), ("CONTRACT-SHA256:abc",), "profile-digest"
    )
    return HumanAttestationRequest(
        profile,
        obligation,
        RunBinding("snapshot-digest", "base-sha", "head-sha", "artifact-digest"),
    )


def _approval(
    key: Ed25519PrivateKey,
    identity: str,
    request: HumanAttestationRequest,
    *,
    nonce: str,
    decision: str = "PASS",
) -> dict[str, object]:
    payload: dict[str, object] = {
        "approval_id": f"approval-{identity}",
        "identity": identity,
        "key_id": identity,
        "decision": decision,
        "repository_id": request.profile.unit_id.repository_id,
        "prompt_relpath": request.profile.unit_id.prompt_relpath.as_posix(),
        "language_id": request.profile.unit_id.language_id,
        "requirement_ids": list(request.obligation.requirement_ids),
        "obligation_id": request.obligation.obligation_id,
        "snapshot_digest": request.binding.snapshot_digest,
        "profile_digest": request.profile.profile_digest,
        "protected_base_sha": request.binding.base_sha,
        "checked_head_sha": request.binding.head_sha,
        "artifact_closure_digest": request.binding.artifact_closure_digest,
        "policy_version": "v1",
        "policy_digest": "POLICY_DIGEST",
        "nonce": nonce,
        "issued_at": NOW.isoformat(),
        "expires_at": (NOW + timedelta(hours=1)).isoformat(),
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["signature"] = base64.b64encode(key.sign(encoded)).decode("ascii")
    return payload


def _repository(tmp_path: Path) -> tuple[Path, str, Path, tuple[Ed25519PrivateKey, ...]]:
    root = tmp_path / "repo"
    store = tmp_path / "external-store"
    root.mkdir()
    store.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "attestation@example.com")
    _git(root, "config", "user.name", "Attestation Test")
    keys = (_key(b"a"), _key(b"b"), _key(b"c"))
    policy = {
        "version": "v1",
        "threshold": 2,
        "required_role": "approver",
        "signers": [
            {"identity": identity, "key_id": identity, "public_key": _public(key), "roles": ["approver"]}
            for identity, key in zip(("alice", "bob", "carol"), keys)
        ],
        "revoked_identities": [],
        "revoked_key_ids": [],
    }
    policy_path = root / ".pdd/human-attestation-policy.json"
    policy_path.parent.mkdir()
    policy_path.write_text(json.dumps(policy), encoding="utf-8")
    (root / "prompts").mkdir()
    (root / "prompts/widget.prompt").write_text("opaque contract", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected human attestation policy")
    return root, _git(root, "rev-parse", "HEAD"), store, keys


def _write_approvals(store: Path, approvals: list[dict[str, object]]) -> None:
    (store / "approvals.json").write_text(json.dumps({"approvals": approvals}), encoding="utf-8")


def test_external_threshold_approvals_pass_every_opaque_requirement(tmp_path: Path) -> None:
    root, base, store, keys = _repository(tmp_path)
    request = _request()
    policy = load_human_attestation_policy(root, base, store)
    approvals = [
        _approval(keys[0], "alice", request, nonce="alice-1"),
        _approval(keys[1], "bob", request, nonce="bob-1"),
    ]
    for approval in approvals:
        approval["policy_digest"] = policy.digest
        approval["signature"] = ""
        encoded = json.dumps({key: value for key, value in approval.items() if key != "signature"}, sort_keys=True, separators=(",", ":")).encode()
        key = keys[("alice", "bob").index(approval["identity"])]
        approval["signature"] = base64.b64encode(key.sign(encoded)).decode("ascii")
    _write_approvals(store, approvals)
    verifier = HumanAttestationVerifier(policy, store / "replay.json")
    assert verifier.verify(request, now=NOW) is EvidenceOutcome.PASS


@pytest.mark.parametrize("mutator", ["candidate_policy", "single", "mixed", "rebind"])
def test_human_attestation_fails_closed_for_untrusted_or_incomplete_approvals(
    tmp_path: Path, mutator: str
) -> None:
    root, base, store, keys = _repository(tmp_path)
    request = _request()
    policy = load_human_attestation_policy(root, base, store)
    approvals = [
        _approval(keys[0], "alice", request, nonce="same"),
        _approval(keys[1], "bob", request, nonce="bob-1"),
    ]
    if mutator == "candidate_policy":
        (root / ".pdd/human-attestation-policy.json").write_text(
            json.dumps({"threshold": 1, "signers": []}), encoding="utf-8"
        )
    if mutator == "single":
        approvals.pop()
    if mutator == "mixed":
        approvals[1]["decision"] = "FAIL"
    if mutator == "rebind":
        approvals[1]["nonce"] = "same"
    _write_approvals(store, approvals)
    verifier = HumanAttestationVerifier(policy, store / "replay.json")
    with pytest.raises(HumanAttestationError):
        verifier.verify(request, now=NOW)
