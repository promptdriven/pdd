"""Contract tests for protected threshold-Ed25519 human approvals."""

import base64
import json
import subprocess
from datetime import datetime, timedelta, timezone
from pathlib import Path, PurePosixPath

import pytest
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from pdd.sync_core import (
    AttestationIssue,
    AttestationSigner,
    EvidenceOutcome,
    HumanAttestationError,
    HumanAttestationRequest,
    HumanAttestationVerifier,
    RunnerConfig,
    RunBinding,
    UnitId,
    VerificationObligation,
    VerificationProfile,
    load_human_attestation_policy,
    run_profile,
)


NOW = datetime.now(timezone.utc).replace(microsecond=0)
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
        "maximum_lifetime_seconds": 3600,
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


def _sign(key: Ed25519PrivateKey, approval: dict[str, object]) -> None:
    approval["signature"] = base64.b64encode(
        key.sign(
            json.dumps(
                {name: value for name, value in approval.items() if name != "signature"},
                sort_keys=True,
                separators=(",", ":"),
            ).encode()
        )
    ).decode("ascii")


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
        key = keys[("alice", "bob").index(approval["identity"])]
        _sign(key, approval)
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
        approvals.pop()
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


@pytest.mark.parametrize("mutator", ["duplicate", "expired", "future", "revoked", "wrong_requirement"])
def test_human_attestation_rejects_each_invalid_signer_or_binding(
    tmp_path: Path, mutator: str
) -> None:
    root, base, store, keys = _repository(tmp_path)
    request = _request()
    policy = load_human_attestation_policy(root, base, store)
    approvals = [
        _approval(keys[0], "alice", request, nonce="alice-1"),
        _approval(keys[1], "bob", request, nonce="bob-1"),
    ]
    for index, approval in enumerate(approvals):
        approval["policy_digest"] = policy.digest
        _sign(keys[index], approval)
    if mutator == "duplicate":
        approvals[1] = dict(approvals[0])
        approvals[1]["approval_id"] = "another-alice"
        _sign(keys[0], approvals[1])
    elif mutator == "expired":
        approvals[1]["expires_at"] = (NOW - timedelta(minutes=1)).isoformat()
        _sign(keys[1], approvals[1])
    elif mutator == "future":
        approvals[1]["issued_at"] = (NOW + timedelta(minutes=1)).isoformat()
        _sign(keys[1], approvals[1])
    elif mutator == "revoked":
        policy = policy.__class__(
            policy.version, policy.digest, policy.threshold,
            policy.maximum_lifetime_seconds, policy.required_role, policy.signers,
            frozenset({"bob"}), policy.revoked_key_ids, policy.candidate_root,
            policy.external_store,
        )
    else:
        approvals[1]["requirement_ids"] = ["CONTRACT-SHA256:other"]
        _sign(keys[1], approvals[1])
    _write_approvals(store, approvals)
    with pytest.raises(HumanAttestationError):
        HumanAttestationVerifier(policy, store / "replay.json").verify(request, now=NOW)


def test_runner_normalizes_external_threshold_quorum_to_pass(tmp_path: Path) -> None:
    root, base, store, keys = _repository(tmp_path)
    binding = RunBinding("snapshot-digest", base, base, "artifact-digest")
    request = _request()
    policy = load_human_attestation_policy(root, base, store)
    obligation = VerificationObligation(
        "human", "human-attestation", "threshold-ed25519", policy.digest,
        request.obligation.requirement_ids, (),
    )
    profile = VerificationProfile(UNIT, (obligation,), request.profile.required_requirement_ids, "profile-digest")
    request = HumanAttestationRequest(profile, obligation, binding)
    approvals = [
        _approval(keys[0], "alice", request, nonce="alice-run"),
        _approval(keys[1], "bob", request, nonce="bob-run"),
    ]
    for index, approval in enumerate(approvals):
        approval["policy_digest"] = policy.digest
        _sign(keys[index], approval)
    _write_approvals(store, approvals)
    _envelope, executions = run_profile(
        root, profile, request.binding,
        AttestationIssue(AttestationSigner("runner", b"r" * 32), "run", "run-nonce", NOW),
        config=RunnerConfig(
            human_attestation_store=store,
            human_attestation_replay_ledger=store / "replay.json",
        ),
    )
    assert executions[0].outcome is EvidenceOutcome.PASS
