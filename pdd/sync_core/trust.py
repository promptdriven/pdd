"""Attestation issuance and protected trust-policy verification."""

from __future__ import annotations

import base64
import json
import os
import subprocess
import tempfile
from dataclasses import dataclass, replace
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Mapping, Optional, Protocol

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)
from .descriptor_store import DescriptorStoreError, update_json
from .durability import fsync_directory
from .types import EvidenceOutcome, ObligationEvidence, UnitId


class AttestationError(ValueError):
    """Raised when semantic evidence fails protected trust policy."""


class AttestationIssuer(Protocol):
    """Signer surface accepted by the trusted runner."""

    issuer: str

    def public_key_bytes(self) -> bytes:
        """Return the expected Ed25519 public key."""

    def issue(self, request: "AttestationRequest") -> "AttestationEnvelope":
        """Issue one signed attestation envelope."""


class ReplayStore:
    """Interface for atomic cross-verifier attestation nonce consumption."""

    def consume(self, issuer: str, nonce: str, attestation_id: str) -> None:
        """Bind a nonce to one attestation ID, allowing idempotent rechecks."""
        raise NotImplementedError

    def is_durable(self) -> bool:
        """Return whether nonce history survives verifier process exit."""
        raise NotImplementedError


class InMemoryReplayStore(ReplayStore):
    """Process-local replay store for isolated tests and one-shot validation."""

    def __init__(self) -> None:
        self._seen: dict[tuple[str, str], str] = {}

    def consume(self, issuer: str, nonce: str, attestation_id: str) -> None:
        """Reject nonce reuse for a different signed statement."""
        key = (issuer, nonce)
        previous = self._seen.get(key)
        if previous is not None:
            if previous == attestation_id:
                return
            raise AttestationError("attestation nonce was replayed")
        self._seen[key] = attestation_id

    def is_durable(self) -> bool:
        """Return false for process-local test storage."""
        return False


class FileReplayStore(ReplayStore):
    """Locked durable nonce ledger located outside candidate-controlled state."""

    def __init__(self, path: Path) -> None:
        self.path = Path(path).absolute()

    def _ensure_parent(self) -> None:
        parent = self.path.parent
        if parent.exists() and (parent.is_symlink() or not parent.is_dir()):
            raise AttestationError("replay ledger parent is unsafe")
        parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        os.chmod(parent, 0o700)

    def _load(self) -> dict[str, str]:
        if not self.path.exists():
            return {}
        if self.path.is_symlink() or not self.path.is_file():
            raise AttestationError("replay ledger is unsafe")
        try:
            payload = json.loads(self.path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise AttestationError("replay ledger is corrupt") from exc
        if not isinstance(payload, dict) or not all(
            isinstance(key, str) and isinstance(value, str)
            for key, value in payload.items()
        ):
            raise AttestationError("replay ledger has invalid records")
        return payload

    def _write(self, payload: dict[str, str]) -> None:
        descriptor, temporary_name = tempfile.mkstemp(
            prefix=f".{self.path.name}.", suffix=".tmp", dir=self.path.parent
        )
        temporary = Path(temporary_name)
        try:
            os.fchmod(descriptor, 0o600)
            with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
                json.dump(payload, handle, sort_keys=True, indent=2)
                handle.write("\n")
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, self.path)
            fsync_directory(self.path.parent)
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise

    def consume(self, issuer: str, nonce: str, attestation_id: str) -> None:
        """Atomically reject and record every repeated issuer/nonce pair."""
        def consume_record(records):
            if not isinstance(records, dict) or not all(
                isinstance(key, str) and isinstance(value, str)
                for key, value in records.items()
            ):
                raise AttestationError("replay ledger has invalid records")
            key = base64.b64encode(f"{issuer}\0{nonce}".encode()).decode("ascii")
            previous = records.get(key)
            if previous is not None and previous != attestation_id:
                raise AttestationError("attestation nonce was replayed")
            if previous is None:
                records[key] = attestation_id
            return records
        error = None
        for _attempt in range(3):
            try:
                update_json(self.path, {}, consume_record)
                return
            except DescriptorStoreError as exc:
                error = exc
        if error is not None:
            raise AttestationError(str(error)) from error

    def is_durable(self) -> bool:
        """Return true for the fsynced external ledger."""
        return True


def _timestamp(value: datetime) -> str:
    if value.tzinfo is None:
        raise ValueError("attestation timestamps must be timezone-aware")
    return value.astimezone(timezone.utc).isoformat()


def _parse_timestamp(value: str) -> datetime:
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError as exc:
        raise AttestationError("attestation timestamp is malformed") from exc
    if parsed.tzinfo is None:
        raise AttestationError("attestation timestamp must include a timezone")
    return parsed.astimezone(timezone.utc)


@dataclass(frozen=True)
# pylint: disable=too-many-instance-attributes
class AttestationBinding:
    """Complete subject, input, runner, and Git closure for an attestation."""

    subject: UnitId
    snapshot_digest: str
    profile_digest: str
    runner_digest: str
    tool_version: str
    base_sha: str
    checked_sha: str
    playwright_command: tuple[str, ...] | None = None
    playwright_toolchain_manifest: str | None = None


@dataclass(frozen=True)
class AttestationValidity:
    """Freshness and replay fields covered by the signature."""

    issued_at: str
    expires_at: str
    nonce: str


@dataclass(frozen=True)
class AttestationEnvelope:
    """Signed statement covering one unit's complete verification execution."""

    attestation_id: str
    issuer: str
    binding: AttestationBinding
    results: tuple[ObligationEvidence, ...]
    validity: AttestationValidity
    signature: str = ""

    def payload(self) -> bytes:
        """Return canonical signed bytes, excluding the signature itself."""
        data = {
            "attestation_id": self.attestation_id,
            "issuer": self.issuer,
            "binding": {
                "subject": {
                    "repository_id": self.binding.subject.repository_id,
                    "prompt_relpath": self.binding.subject.prompt_relpath.as_posix(),
                    "language_id": self.binding.subject.language_id,
                },
                "snapshot_digest": self.binding.snapshot_digest,
                "profile_digest": self.binding.profile_digest,
                "runner_digest": self.binding.runner_digest,
                "tool_version": self.binding.tool_version,
                "base_sha": self.binding.base_sha,
                "checked_sha": self.binding.checked_sha,
            },
            "results": [
                {
                    "obligation_id": result.obligation_id,
                    "outcome": result.outcome.value,
                }
                for result in sorted(self.results)
            ],
            "validity": {
                "issued_at": self.validity.issued_at,
                "expires_at": self.validity.expires_at,
                "nonce": self.validity.nonce,
            },
        }
        if self.binding.playwright_command is not None:
            data["binding"]["playwright_command"] = list(
                self.binding.playwright_command
            )
        if self.binding.playwright_toolchain_manifest is not None:
            data["binding"]["playwright_toolchain_manifest"] = (
                self.binding.playwright_toolchain_manifest
            )
        return json.dumps(data, sort_keys=True, separators=(",", ":")).encode()


@dataclass(frozen=True)
class AttestationRequest:
    """Inputs supplied by a trusted runner when issuing evidence."""

    attestation_id: str
    binding: AttestationBinding
    results: tuple[ObligationEvidence, ...]
    nonce: str
    issued_at: Optional[datetime] = None
    lifetime: timedelta = timedelta(days=8)


@dataclass(frozen=True)
class EvidenceClaims:
    """Claims retained after signature and policy verification."""

    subject: UnitId
    snapshot_digest: str
    profile_digest: str
    results: tuple[ObligationEvidence, ...]
    attestation_id: str
    issuer: str


_EVIDENCE_SEAL = object()


@dataclass(frozen=True, init=False)
class ValidationEvidence:
    """Evidence that can only be constructed with the module verifier seal."""

    claims: EvidenceClaims

    def __init__(self, claims: EvidenceClaims, *, _seal: object) -> None:
        if _seal is not _EVIDENCE_SEAL:
            raise TypeError("ValidationEvidence must be issued by AttestationTrustPolicy")
        object.__setattr__(self, "claims", claims)

    @property
    def subject(self) -> UnitId:
        """Return the verified subject identity."""
        return self.claims.subject

    @property
    def snapshot_digest(self) -> str:
        """Return the verified snapshot closure digest."""
        return self.claims.snapshot_digest

    @property
    def profile_digest(self) -> str:
        """Return the verified profile digest."""
        return self.claims.profile_digest

    @property
    def attestation_id(self) -> str:
        """Return the verified attestation identifier."""
        return self.claims.attestation_id

    def result_map(self) -> dict[str, EvidenceOutcome]:
        """Index normalized outcomes by obligation identifier."""
        return {result.obligation_id: result.outcome for result in self.claims.results}


class AttestationSigner:
    """Trusted-runner helper that signs verification results."""

    def __init__(self, issuer: str, key: bytes) -> None:
        if not issuer or len(key) != 32:
            raise ValueError("attestation signer requires issuer and key")
        self.issuer = issuer
        self._key = Ed25519PrivateKey.from_private_bytes(key)

    def public_key_bytes(self) -> bytes:
        """Return the raw public key suitable for protected trust policy."""
        return self._key.public_key().public_bytes(
            serialization.Encoding.Raw,
            serialization.PublicFormat.Raw,
        )

    def sign_bytes(self, payload: bytes) -> str:
        """Return a base64 Ed25519 signature for arbitrary canonical bytes."""
        return base64.b64encode(self._key.sign(payload)).decode("ascii")

    def sign(self, envelope: AttestationEnvelope) -> AttestationEnvelope:
        """Attach an HMAC signature to an otherwise complete envelope."""
        signature = self.sign_bytes(envelope.payload())
        return replace(envelope, signature=signature)

    def issue(self, request: AttestationRequest) -> AttestationEnvelope:
        """Create a signed envelope bound to one checked commit and base."""
        return self.sign(_unsigned_envelope(self.issuer, request))


def _unsigned_envelope(
    issuer: str, request: AttestationRequest
) -> AttestationEnvelope:
    """Build the canonical unsigned statement sent to a signing authority."""
    issued = request.issued_at or datetime.now(timezone.utc)
    validity = AttestationValidity(
        _timestamp(issued),
        _timestamp(issued + request.lifetime),
        request.nonce,
    )
    return AttestationEnvelope(
        request.attestation_id,
        issuer,
        request.binding,
        request.results,
        validity,
    )


class RemoteAttestationSigner:
    """Issue evidence through a protected signer command and verify its response."""

    def __init__(self, issuer: str, public_key: bytes, command: tuple[str, ...]) -> None:
        if not issuer or len(public_key) != 32 or not command:
            raise ValueError("remote attestation signer configuration is invalid")
        self.issuer = issuer
        self._public_key = public_key
        self._command = command

    def public_key_bytes(self) -> bytes:
        """Return the protected expected public key."""
        return self._public_key

    def issue(self, request: AttestationRequest) -> AttestationEnvelope:
        """Send canonical claims to the remote authority and verify its signature."""
        envelope = _unsigned_envelope(self.issuer, request)
        result = subprocess.run(
            self._command,
            input=envelope.payload(),
            capture_output=True,
            check=False,
        )
        if result.returncode != 0:
            raise AttestationError("remote attestation signer rejected the request")
        try:
            signature = base64.b64decode(result.stdout.strip(), validate=True)
            Ed25519PublicKey.from_public_bytes(self._public_key).verify(
                signature, envelope.payload()
            )
        except (ValueError, InvalidSignature) as exc:
            raise AttestationError(
                "remote attestation signer returned an invalid signature"
            ) from exc
        return replace(envelope, signature=base64.b64encode(signature).decode("ascii"))


class AttestationTrustPolicy:
    """Protected issuer, freshness, revocation, and replay policy."""

    def __init__(
        self,
        trusted_issuers: Mapping[str, bytes],
        *,
        revoked_issuers: frozenset[str] = frozenset(),
        revoked_attestations: frozenset[str] = frozenset(),
        clock_skew: timedelta = timedelta(minutes=5),
        maximum_lifetime: timedelta = timedelta(days=8),
        replay_store: ReplayStore | None = None,
    ) -> None:
        # pylint: disable=too-many-arguments
        self._trusted_issuers = dict(trusted_issuers)
        self._revoked_issuers = revoked_issuers
        self._revoked_attestations = revoked_attestations
        self._clock_skew = clock_skew
        self._maximum_lifetime = maximum_lifetime
        self._replay_store = replay_store or InMemoryReplayStore()

    def reset_replay_cache(self) -> None:
        """Reject unsafe attempts to erase replay history through the verifier."""
        raise AttestationError("replay history cannot be reset by candidate code")

    def _verify_signature(self, envelope: AttestationEnvelope) -> None:
        key_bytes = self._trusted_issuers.get(envelope.issuer)
        if key_bytes is None:
            raise AttestationError("attestation issuer is not trusted")
        try:
            signature = base64.b64decode(envelope.signature, validate=True)
            Ed25519PublicKey.from_public_bytes(key_bytes).verify(
                signature, envelope.payload()
            )
        except (ValueError, InvalidSignature) as exc:
            raise AttestationError("attestation signature is invalid") from exc

    def _verify_freshness(self, envelope: AttestationEnvelope, now: datetime) -> None:
        issued = _parse_timestamp(envelope.validity.issued_at)
        expires = _parse_timestamp(envelope.validity.expires_at)
        if expires <= issued:
            raise AttestationError("attestation validity interval is invalid")
        if expires - issued > self._maximum_lifetime:
            raise AttestationError("attestation validity interval exceeds policy")
        if issued > now + self._clock_skew:
            raise AttestationError("attestation is not yet valid")
        if expires <= now:
            raise AttestationError("attestation is expired")

    def _verify_replay(self, envelope: AttestationEnvelope) -> None:
        self._replay_store.consume(
            envelope.issuer, envelope.validity.nonce, envelope.attestation_id
        )

    def _verify(
        self,
        envelope: AttestationEnvelope,
        expected: AttestationBinding,
        *,
        now: Optional[datetime] = None,
        consume_replay: bool,
    ) -> ValidationEvidence:
        if envelope.issuer in self._revoked_issuers:
            raise AttestationError("attestation issuer is revoked")
        if envelope.attestation_id in self._revoked_attestations:
            raise AttestationError("attestation is revoked")
        self._verify_signature(envelope)
        self._verify_freshness(envelope, now or datetime.now(timezone.utc))
        if envelope.binding != expected:
            raise AttestationError("attestation does not match the checked closure")
        identifiers = [result.obligation_id for result in envelope.results]
        if len(identifiers) != len(set(identifiers)):
            raise AttestationError("attestation contains duplicate obligation results")
        if not envelope.binding.runner_digest or not envelope.binding.tool_version:
            raise AttestationError("attestation runner identity is incomplete")
        if consume_replay:
            self._verify_replay(envelope)
        claims = EvidenceClaims(
            envelope.binding.subject,
            envelope.binding.snapshot_digest,
            envelope.binding.profile_digest,
            envelope.results,
            envelope.attestation_id,
            envelope.issuer,
        )
        return ValidationEvidence(claims, _seal=_EVIDENCE_SEAL)

    def verify(
        self,
        envelope: AttestationEnvelope,
        expected: AttestationBinding,
        *,
        now: Optional[datetime] = None,
    ) -> ValidationEvidence:
        """Verify all protected bindings and consume evidence exactly once."""
        return self._verify(
            envelope, expected, now=now, consume_replay=True
        )

    def verify_current_for_idempotency(
        self,
        envelope: AttestationEnvelope,
        expected: AttestationBinding,
        *,
        now: Optional[datetime] = None,
    ) -> ValidationEvidence:
        """Recheck current trusted state without claiming a new evidence use."""
        return self._verify(
            envelope, expected, now=now, consume_replay=False
        )


def passing_result(obligation_id: str) -> ObligationEvidence:
    """Build a normalized PASS result for a trusted runner adapter."""
    return ObligationEvidence(obligation_id, EvidenceOutcome.PASS)
