"""Protected threshold-Ed25519 verification for external human approvals."""

# pylint: disable=too-many-instance-attributes,too-many-locals,too-many-branches,too-many-statements

from __future__ import annotations

import base64
import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path, PurePosixPath
from typing import Any, Mapping

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from .git_io import read_git_blob
from .trust import AttestationError, FileReplayStore
from .types import EvidenceOutcome, VerificationObligation, VerificationProfile


HUMAN_ATTESTATION_POLICY_PATH = PurePosixPath(".pdd/human-attestation-policy.json")
_APPROVALS_FILENAME = "approvals.json"


class HumanAttestationError(AttestationError):
    """Raised when threshold human approval cannot be trusted."""


@dataclass(frozen=True)
class HumanAttestationSigner:
    """One protected signer identity and its permitted roles."""

    identity: str
    key_id: str
    public_key: bytes
    roles: frozenset[str]
    not_before: datetime | None
    not_after: datetime | None


@dataclass(frozen=True)
class HumanAttestationPolicy:
    """Protected immutable quorum policy for human approval verification."""

    version: str
    digest: str
    threshold: int
    maximum_lifetime_seconds: int
    required_role: str
    signers: Mapping[str, HumanAttestationSigner]
    revoked_identities: frozenset[str]
    revoked_key_ids: frozenset[str]
    candidate_root: Path
    external_store: Path


@dataclass(frozen=True)
class HumanAttestationRequest:
    """Exact immutable closure a human approval must cover."""

    profile: VerificationProfile
    obligation: VerificationObligation
    binding: Any

    def __post_init__(self) -> None:
        if (
            self.obligation.kind != "human-attestation"
            or self.obligation.validator_id != "threshold-ed25519"
        ):
            raise ValueError("human attestation request requires threshold-ed25519")
        if self.obligation not in self.profile.obligations:
            raise ValueError("human attestation obligation is outside the profile")
        if not self.binding.artifact_closure_digest:
            raise ValueError("human attestation requires an artifact closure digest")


def _required_string(payload: Mapping[str, Any], name: str) -> str:
    value = payload.get(name)
    if not isinstance(value, str) or not value:
        raise HumanAttestationError(f"human attestation field {name!r} is invalid")
    return value


def _timestamp(value: object, name: str) -> datetime:
    if not isinstance(value, str):
        raise HumanAttestationError(f"human attestation field {name!r} is invalid")
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError as exc:
        raise HumanAttestationError(f"human attestation field {name!r} is malformed") from exc
    if parsed.tzinfo is None:
        raise HumanAttestationError(f"human attestation field {name!r} lacks a timezone")
    return parsed.astimezone(timezone.utc)


def _optional_timestamp(value: object, name: str) -> datetime | None:
    return None if value is None else _timestamp(value, name)


def load_human_attestation_policy(
    root: Path, protected_base_ref: str, external_store: Path
) -> HumanAttestationPolicy:
    """Load quorum authority only from the protected base Git tree."""
    root = Path(root).resolve()
    external = Path(external_store).resolve()
    try:
        external.relative_to(root)
    except ValueError:
        pass
    else:
        raise HumanAttestationError(
            "human approval store must be outside the candidate checkout"
        )
    raw = read_git_blob(root, protected_base_ref, HUMAN_ATTESTATION_POLICY_PATH)
    if raw is None:
        raise HumanAttestationError("protected base has no human attestation policy")
    try:
        payload = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise HumanAttestationError("protected human attestation policy is malformed") from exc
    if not isinstance(payload, dict):
        raise HumanAttestationError("protected human attestation policy must be an object")
    version = _required_string(payload, "version")
    threshold = payload.get("threshold")
    maximum_lifetime_seconds = payload.get("maximum_lifetime_seconds")
    required_role = _required_string(payload, "required_role")
    rows = payload.get("signers")
    if (
        not isinstance(threshold, int)
        or threshold < 1
        or not isinstance(maximum_lifetime_seconds, int)
        or maximum_lifetime_seconds < 1
        or not isinstance(rows, list)
    ):
        raise HumanAttestationError("protected human attestation threshold is invalid")
    signers: dict[str, HumanAttestationSigner] = {}
    key_ids: set[str] = set()
    for row in rows:
        if not isinstance(row, dict):
            raise HumanAttestationError("protected human signer is malformed")
        identity = _required_string(row, "identity")
        key_id = _required_string(row, "key_id")
        roles = row.get("roles")
        if (
            not isinstance(roles, list)
            or not roles
            or not all(isinstance(role, str) and role for role in roles)
        ):
            raise HumanAttestationError("protected human signer roles are invalid")
        try:
            public_key = base64.b64decode(_required_string(row, "public_key"), validate=True)
        except ValueError as exc:
            raise HumanAttestationError("protected human signer key is malformed") from exc
        if len(public_key) != 32 or identity in signers or key_id in key_ids:
            raise HumanAttestationError("protected human signer identity or key is duplicate")
        signer = HumanAttestationSigner(
            identity, key_id, public_key, frozenset(roles),
            _optional_timestamp(row.get("not_before"), "not_before"),
            _optional_timestamp(row.get("not_after"), "not_after"),
        )
        if signer.not_before and signer.not_after and signer.not_after <= signer.not_before:
            raise HumanAttestationError("protected human signer validity is invalid")
        signers[identity] = signer
        key_ids.add(key_id)
    revoked_identities = frozenset(payload.get("revoked_identities", []))
    revoked_key_ids = frozenset(payload.get("revoked_key_ids", []))
    if not all(isinstance(value, str) for value in revoked_identities | revoked_key_ids):
        raise HumanAttestationError("protected human revocation list is invalid")
    if threshold > len(signers) or not any(
        required_role in signer.roles for signer in signers.values()
    ):
        raise HumanAttestationError("protected human attestation policy is unsatisfiable")
    return HumanAttestationPolicy(
        version, hashlib.sha256(raw).hexdigest(), threshold,
        maximum_lifetime_seconds, required_role, signers, revoked_identities,
        revoked_key_ids, root, external,
    )


def _canonical_payload(approval: Mapping[str, Any]) -> bytes:
    unsigned = {key: value for key, value in approval.items() if key != "signature"}
    return json.dumps(unsigned, sort_keys=True, separators=(",", ":")).encode()


class HumanAttestationVerifier:  # pylint: disable=too-few-public-methods
    """Verify external, thresholded human decisions without any signing surface."""

    def __init__(self, policy: HumanAttestationPolicy, replay_ledger_path: Path) -> None:
        self.policy = policy
        replay = Path(replay_ledger_path).resolve()
        try:
            replay.relative_to(policy.candidate_root)
        except ValueError:
            pass
        else:
            raise HumanAttestationError(
                "human attestation replay ledger must be outside the candidate checkout"
            )
        self._replay = FileReplayStore(replay)

    def _load_approvals(self, store: Path) -> list[Mapping[str, Any]]:
        path = Path(store).resolve() / _APPROVALS_FILENAME
        if path.is_symlink() or not path.is_file():
            raise HumanAttestationError("external human approval store is missing or unsafe")
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise HumanAttestationError("external human approval store is malformed") from exc
        approvals = payload.get("approvals") if isinstance(payload, dict) else None
        if not isinstance(approvals, list) or not all(isinstance(item, dict) for item in approvals):
            raise HumanAttestationError("external human approvals must be an object list")
        return approvals

    def _verify_approval(
        self, approval: Mapping[str, Any], request: HumanAttestationRequest, now: datetime
    ) -> str:
        identity = _required_string(approval, "identity")
        signer = self.policy.signers.get(identity)
        if signer is None or identity in self.policy.revoked_identities:
            raise HumanAttestationError("human approval identity is not authorized")
        if (
            _required_string(approval, "key_id") != signer.key_id
            or signer.key_id in self.policy.revoked_key_ids
        ):
            raise HumanAttestationError("human approval key is revoked or rotated")
        if self.policy.required_role not in signer.roles:
            raise HumanAttestationError("human approval signer lacks the required role")
        issued = _timestamp(approval.get("issued_at"), "issued_at")
        expires = _timestamp(approval.get("expires_at"), "expires_at")
        if (
            expires <= issued
            or expires - issued > timedelta(seconds=self.policy.maximum_lifetime_seconds)
            or issued > now
            or expires <= now
        ):
            raise HumanAttestationError("human approval is stale or not yet valid")
        if (
            signer.not_before and issued < signer.not_before
        ) or (
            signer.not_after and issued >= signer.not_after
        ):
            raise HumanAttestationError("human approval signer is outside its validity window")
        expected = {
            "decision": "PASS", "repository_id": request.profile.unit_id.repository_id,
            "prompt_relpath": request.profile.unit_id.prompt_relpath.as_posix(),
            "language_id": request.profile.unit_id.language_id,
            "requirement_ids": list(request.obligation.requirement_ids),
            "obligation_id": request.obligation.obligation_id,
            "snapshot_digest": request.binding.snapshot_digest,
            "profile_digest": request.profile.profile_digest,
            "protected_base_sha": request.binding.base_sha,
            "checked_head_sha": request.binding.head_sha,
            "artifact_closure_digest": request.binding.artifact_closure_digest,
            "policy_version": self.policy.version, "policy_digest": self.policy.digest,
        }
        if any(approval.get(key) != value for key, value in expected.items()):
            raise HumanAttestationError("human approval does not bind the checked closure")
        try:
            signature = base64.b64decode(
                _required_string(approval, "signature"), validate=True
            )
            Ed25519PublicKey.from_public_bytes(signer.public_key).verify(
                signature, _canonical_payload(approval)
            )
        except (ValueError, InvalidSignature) as exc:
            raise HumanAttestationError("human approval signature is invalid") from exc
        approval_id = _required_string(approval, "approval_id")
        nonce = _required_string(approval, "nonce")
        digest = hashlib.sha256(_canonical_payload(approval)).hexdigest()
        self._replay.consume(identity, nonce, f"{approval_id}:{digest}")
        return identity

    def verify(
        self, request: HumanAttestationRequest, *, now: datetime | None = None
    ) -> EvidenceOutcome:
        """Return PASS only when distinct authorized humans reach threshold."""
        instant = now or datetime.now(timezone.utc)
        approvals = self._load_approvals(self.policy.external_store)
        try:
            identities = {
                self._verify_approval(approval, request, instant) for approval in approvals
            }
        except AttestationError as exc:
            raise HumanAttestationError(str(exc)) from exc
        if len(identities) < self.policy.threshold:
            raise HumanAttestationError("human approval threshold is not met")
        return EvidenceOutcome.PASS
