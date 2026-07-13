"""Serialization and protected-base policy loading for signed evidence."""

from __future__ import annotations

import base64
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Mapping

from .trust import (
    AttestationBinding,
    AttestationEnvelope,
    AttestationError,
    AttestationTrustPolicy,
    AttestationValidity,
    FileReplayStore,
)
from .git_io import read_git_blob
from .types import EvidenceOutcome, ObligationEvidence, UnitId


TRUST_POLICY_PATH = PurePosixPath(".pdd/attestation-trust.json")
EVIDENCE_ROOT = PurePosixPath(".pdd/evidence/v2")


class EvidenceStoreError(ValueError):
    """Raised when evidence or protected trust configuration is malformed."""


@dataclass(frozen=True)
class LoadedTrustPolicy:
    """Runtime verifier and deterministic protected policy digest."""

    verifier: AttestationTrustPolicy
    digest: str
    issuer_ids: tuple[str, ...]


def evidence_relpath(attestation_id: str) -> PurePosixPath:
    """Return the safe repository-relative location for one attestation."""
    safe = "-_.0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    if not attestation_id or any(character not in safe for character in attestation_id):
        raise EvidenceStoreError("attestation ID contains unsafe characters")
    return EVIDENCE_ROOT / f"{attestation_id}.json"


def attestation_payload(envelope: AttestationEnvelope) -> dict[str, Any]:
    """Convert a signed envelope to stable JSON data without altering its payload."""
    binding = envelope.binding
    payload = {
        "attestation_id": envelope.attestation_id,
        "issuer": envelope.issuer,
        "binding": {
            "subject": {
                "repository_id": binding.subject.repository_id,
                "prompt_relpath": binding.subject.prompt_relpath.as_posix(),
                "language_id": binding.subject.language_id,
            },
            "snapshot_digest": binding.snapshot_digest,
            "profile_digest": binding.profile_digest,
            "runner_digest": binding.runner_digest,
            "tool_version": binding.tool_version,
            "base_sha": binding.base_sha,
            "checked_sha": binding.checked_sha,
        },
        "results": [
            {
                "obligation_id": result.obligation_id,
                "outcome": result.outcome.value,
            }
            for result in envelope.results
        ],
        "validity": {
            "issued_at": envelope.validity.issued_at,
            "expires_at": envelope.validity.expires_at,
            "nonce": envelope.validity.nonce,
        },
        "signature": envelope.signature,
    }
    if binding.adapter_identities:
        payload["binding"]["adapter_identities"] = [
            list(item) for item in binding.adapter_identities
        ]
    if binding.playwright_toolchain_identity is not None:
        payload["binding"]["playwright_toolchain_identity"] = (
            binding.playwright_toolchain_identity
        )
    return payload


def encode_attestation(envelope: AttestationEnvelope) -> bytes:
    """Encode a signed envelope for transactional repository persistence."""
    return json.dumps(
        attestation_payload(envelope), sort_keys=True, indent=2
    ).encode("utf-8") + b"\n"


def _string(payload: Mapping[str, Any], key: str) -> str:
    value = payload.get(key)
    if not isinstance(value, str) or not value:
        raise EvidenceStoreError(f"evidence field {key!r} must be a non-empty string")
    return value


def decode_attestation(payload: Mapping[str, Any]) -> AttestationEnvelope:
    """Decode untrusted JSON into a typed envelope without granting trust."""
    try:
        binding_data = payload["binding"]
        subject_data = binding_data["subject"]
        validity_data = payload["validity"]
        results_data = payload["results"]
        if not all(isinstance(item, dict) for item in results_data):
            raise TypeError("result must be an object")
        subject = UnitId(
            _string(subject_data, "repository_id"),
            PurePosixPath(_string(subject_data, "prompt_relpath")),
            _string(subject_data, "language_id"),
        )
        identities_data = binding_data.get("adapter_identities", [])
        if not isinstance(identities_data, list) or not all(
            isinstance(item, list) and len(item) == 2
            and all(isinstance(value, str) and value for value in item)
            for item in identities_data
        ):
            raise TypeError("adapter_identities must be non-empty string pairs")
        adapter_identities = tuple((item[0], item[1]) for item in identities_data)
        if (
            tuple(sorted(adapter_identities)) != adapter_identities
            or len(set(adapter_identities)) != len(adapter_identities)
        ):
            raise TypeError("adapter_identities must be sorted and unique")
        toolchain_identity = binding_data.get("playwright_toolchain_identity")
        if toolchain_identity is not None and (
            not isinstance(toolchain_identity, str) or not toolchain_identity
        ):
            raise TypeError("playwright_toolchain_identity must be a non-empty string")
        binding = AttestationBinding(
            subject,
            _string(binding_data, "snapshot_digest"),
            _string(binding_data, "profile_digest"),
            _string(binding_data, "runner_digest"),
            _string(binding_data, "tool_version"),
            _string(binding_data, "base_sha"),
            _string(binding_data, "checked_sha"),
            adapter_identities=adapter_identities,
            playwright_toolchain_identity=toolchain_identity,
        )
        results = tuple(
            ObligationEvidence(
                _string(item, "obligation_id"),
                EvidenceOutcome(_string(item, "outcome")),
            )
            for item in results_data
        )
        validity = AttestationValidity(
            _string(validity_data, "issued_at"),
            _string(validity_data, "expires_at"),
            _string(validity_data, "nonce"),
        )
        return AttestationEnvelope(
            _string(payload, "attestation_id"),
            _string(payload, "issuer"),
            binding,
            results,
            validity,
            _string(payload, "signature"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        raise EvidenceStoreError(f"attestation envelope is malformed: {exc}") from exc


def load_attestation(root: Path, attestation_id: str) -> AttestationEnvelope:
    """Load an untrusted candidate envelope from its canonical path."""
    path = Path(root).resolve().joinpath(*evidence_relpath(attestation_id).parts)
    if path.is_symlink() or not path.is_file():
        raise EvidenceStoreError(f"attestation file is missing or unsafe: {path}")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise EvidenceStoreError(f"attestation JSON is malformed: {path}") from exc
    if not isinstance(payload, dict):
        raise EvidenceStoreError("attestation root must be an object")
    envelope = decode_attestation(payload)
    if envelope.attestation_id != attestation_id:
        raise EvidenceStoreError("attestation path and embedded identity differ")
    return envelope


def load_trust_policy(
    root: Path,
    protected_base_ref: str,
    *,
    replay_ledger_path: Path,
) -> LoadedTrustPolicy:
    """Load issuer and revocation authority only from the protected base tree."""
    raw = read_git_blob(Path(root), protected_base_ref, TRUST_POLICY_PATH)
    if raw is None:
        raise EvidenceStoreError("protected base has no attestation trust policy")
    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise EvidenceStoreError("protected attestation trust policy is malformed") from exc
    if not isinstance(payload, dict) or not isinstance(payload.get("issuers"), list):
        raise EvidenceStoreError("protected trust policy issuers must be a list")
    issuers: dict[str, bytes] = {}
    for item in payload["issuers"]:
        if not isinstance(item, dict):
            raise EvidenceStoreError("protected issuer entry must be an object")
        issuer_id = _string(item, "issuer_id")
        try:
            public_key = base64.b64decode(_string(item, "public_key"), validate=True)
        except ValueError as exc:
            raise EvidenceStoreError("protected issuer public key is malformed") from exc
        if len(public_key) != 32 or issuer_id in issuers:
            raise EvidenceStoreError("protected issuer is duplicate or not Ed25519")
        issuers[issuer_id] = public_key
    revoked_issuers = frozenset(payload.get("revoked_issuers", []))
    revoked_attestations = frozenset(payload.get("revoked_attestations", []))
    if not all(isinstance(item, str) for item in revoked_issuers | revoked_attestations):
        raise EvidenceStoreError("protected revocation entries must be strings")
    digest = hashlib.sha256(raw).hexdigest()
    try:
        verifier = AttestationTrustPolicy(
            issuers,
            revoked_issuers=revoked_issuers,
            revoked_attestations=revoked_attestations,
            replay_store=FileReplayStore(replay_ledger_path),
        )
    except AttestationError as exc:
        raise EvidenceStoreError("protected trust policy cannot be initialized") from exc
    return LoadedTrustPolicy(verifier, digest, tuple(sorted(issuers)))
