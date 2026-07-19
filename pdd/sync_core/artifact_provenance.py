"""Verification of protected build attestations for candidate wheels."""
# pylint: disable=duplicate-code,too-many-instance-attributes,too-many-boolean-expressions

from __future__ import annotations

import base64
import hashlib
import json
import os
import tempfile
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
from .descriptor_store import DescriptorStoreError, update_json


class CandidateArtifactProvenanceError(ValueError):
    """Raised when a candidate wheel lacks protected build provenance."""


_MAXIMUM_ATTESTATION_LIFETIME = timedelta(minutes=15)


def _reject_symlink_components(path: Path) -> Path:
    """Return an absolute lexical path only when no existing component is a link."""
    candidate = path.expanduser().absolute()
    for component in (candidate, *candidate.parents):
        try:
            if component.is_symlink():
                raise CandidateArtifactProvenanceError(
                    "candidate replay ledger is unsafe"
                )
        except OSError as exc:
            raise CandidateArtifactProvenanceError(
                "candidate replay ledger is unsafe"
            ) from exc
    return candidate


def _canonical_bytes(payload: dict[str, Any]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _timestamp(value: object, field_name: str) -> datetime:
    try:
        parsed = datetime.fromisoformat(str(value))
    except ValueError as exc:
        raise CandidateArtifactProvenanceError(
            f"candidate attestation {field_name} is invalid"
        ) from exc
    if parsed.tzinfo is None:
        raise CandidateArtifactProvenanceError(
            f"candidate attestation {field_name} is not timezone-aware"
        )
    return parsed.astimezone(timezone.utc)


def _sha256_value(value: object, field_name: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise CandidateArtifactProvenanceError(
            f"candidate attestation {field_name} is invalid"
        )
    return value


@dataclass
class CandidateArtifactPolicy:
    """Protected expected identity of a candidate-wheel build lane."""

    issuer: str
    public_key: bytes
    builder_workflow_identity: str
    dependency_lock_sha256: str
    python_implementation: str
    python_version: str
    python_abi: str
    python_platform: str
    replay_ledger_path: Path | None = None
    _consumed: set[tuple[str, str, str]] = field(default_factory=set, init=False)

    def __post_init__(self) -> None:
        if (
            not self.issuer
            or len(self.public_key) != 32
            or not self.builder_workflow_identity
            or not self.python_implementation
            or not self.python_version
            or not self.python_abi
            or not self.python_platform
        ):
            raise ValueError("candidate artifact policy is malformed")
        _sha256_value(self.dependency_lock_sha256, "dependency lock digest")

    def identity(self) -> dict[str, str]:
        """Return public policy claims that the certificate must bind."""
        return {
            "issuer": self.issuer,
            "builder_workflow_identity": self.builder_workflow_identity,
            "dependency_lock_sha256": self.dependency_lock_sha256,
            "python_implementation": self.python_implementation,
            "python_version": self.python_version,
            "python_abi": self.python_abi,
            "python_platform": self.python_platform,
        }

    def consume(self, attestation_id: str, nonce: str) -> None:
        """Reject a build statement reused by a second certification attempt."""
        key = (self.issuer, attestation_id, nonce)
        if self.replay_ledger_path is not None:
            self._consume_durable(key)
            return
        if key in self._consumed:
            raise CandidateArtifactProvenanceError("candidate attestation is replayed")
        self._consumed.add(key)

    def _consume_durable(self, key: tuple[str, str, str]) -> None:
        path = Path(self.replay_ledger_path).absolute()
        def consume_record(records):
            if not isinstance(records, list) or any(
                not isinstance(item, list) or len(item) != 3
                or any(not isinstance(value, str) for value in item)
                for item in records
            ):
                raise CandidateArtifactProvenanceError(
                    "candidate replay ledger is corrupt"
                )
            if list(key) in records:
                raise CandidateArtifactProvenanceError(
                    "candidate attestation is replayed"
                )
            records.append(list(key))
            return records
        error = None
        for _attempt in range(3):
            try:
                update_json(path, [], consume_record, trust_root=path.parent)
                return
            except DescriptorStoreError as exc:
                error = exc
        if error is not None:
            raise CandidateArtifactProvenanceError(
                f"candidate replay ledger is unsafe: {error}"
            ) from error

    def _read_durable_records(self, path: Path) -> list[list[str]]:
        if path.exists():
            try:
                records = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                raise CandidateArtifactProvenanceError(
                    "candidate replay ledger is corrupt"
                ) from exc
            if not isinstance(records, list) or any(
                not isinstance(item, list)
                or len(item) != 3
                or any(not isinstance(value, str) for value in item)
                for item in records
            ):
                raise CandidateArtifactProvenanceError(
                    "candidate replay ledger is corrupt"
                )
            return records
        return []

    def _write_durable_records(self, path: Path, records: list[list[str]]) -> None:
        descriptor, temporary_name = tempfile.mkstemp(
            prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
        )
        temporary = Path(temporary_name)
        try:
            with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
                handle.write(json.dumps(records, sort_keys=True) + "\n")
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, path)
            directory_fd = os.open(path.parent, os.O_RDONLY)
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise


@dataclass(frozen=True)
class CandidateArtifactProvenance:
    """A signed build statement bound to one immutable candidate wheel."""

    issuer: str
    attestation_id: str
    nonce: str
    issued_at: str
    expires_at: str
    wheel_sha256: str
    source_sha: str
    dependency_lock_sha256: str
    python: dict[str, str]
    builder_workflow_identity: str
    signature: str

    @classmethod
    def from_payload(cls, payload: object) -> "CandidateArtifactProvenance":
        """Parse one untrusted JSON build attestation strictly."""
        if not isinstance(payload, dict) or payload.get("schema_version") != 1:
            raise CandidateArtifactProvenanceError("candidate attestation schema is invalid")
        signature = payload.get("signature")
        fields = (
            "issuer", "attestation_id", "nonce", "issued_at", "expires_at",
            "wheel_sha256", "source_sha", "dependency_lock_sha256",
            "builder_workflow_identity",
        )
        if (
            not isinstance(signature, dict)
            or signature.get("algorithm") != "Ed25519"
            or not isinstance(signature.get("value"), str)
            or any(not isinstance(payload.get(name), str) or not payload[name] for name in fields)
            or not isinstance(payload.get("python"), dict)
        ):
            raise CandidateArtifactProvenanceError("candidate attestation is malformed")
        python = payload["python"]
        expected_python = {"implementation", "version", "abi", "platform"}
        if set(python) != expected_python or any(
            not isinstance(python[name], str) or not python[name] for name in expected_python
        ):
            raise CandidateArtifactProvenanceError("candidate attestation interpreter is invalid")
        _sha256_value(payload["wheel_sha256"], "wheel digest")
        _sha256_value(payload["dependency_lock_sha256"], "dependency lock digest")
        source_sha = payload["source_sha"]
        if len(source_sha) != 40 or any(
            character not in "0123456789abcdef" for character in source_sha
        ):
            raise CandidateArtifactProvenanceError("candidate attestation source SHA is invalid")
        _timestamp(payload["issued_at"], "issued_at")
        _timestamp(payload["expires_at"], "expires_at")
        return cls(
            *(payload[name] for name in fields[:8]),
            dict(python),
            payload["builder_workflow_identity"],
            signature["value"],
        )

    def unsigned_payload(self) -> dict[str, Any]:
        """Return the exact canonical payload protected by the builder signature."""
        return {
            "schema_version": 1,
            "issuer": self.issuer,
            "attestation_id": self.attestation_id,
            "nonce": self.nonce,
            "issued_at": self.issued_at,
            "expires_at": self.expires_at,
            "wheel_sha256": self.wheel_sha256,
            "source_sha": self.source_sha,
            "dependency_lock_sha256": self.dependency_lock_sha256,
            "python": self.python,
            "builder_workflow_identity": self.builder_workflow_identity,
        }

    def payload(self) -> dict[str, Any]:
        """Return the serializable signed statement for certificate inclusion."""
        return {
            **self.unsigned_payload(),
            "signature": {"algorithm": "Ed25519", "value": self.signature},
        }

    def verify(
        self,
        policy: CandidateArtifactPolicy,
        *,
        expected_source_sha: str | None,
        now: datetime | None = None,
        consume_replay: bool = True,
    ) -> None:
        """Verify signature, freshness, protected build environment, and source."""
        if self.issuer != policy.issuer:
            raise CandidateArtifactProvenanceError(
                "candidate attestation issuer is untrusted"
            )
        try:
            signature = base64.b64decode(self.signature, validate=True)
            Ed25519PublicKey.from_public_bytes(policy.public_key).verify(
                signature, _canonical_bytes(self.unsigned_payload())
            )
        except (ValueError, InvalidSignature) as exc:
            raise CandidateArtifactProvenanceError(
                "candidate attestation signature is invalid"
            ) from exc
        issued = _timestamp(self.issued_at, "issued_at")
        expires = _timestamp(self.expires_at, "expires_at")
        current = (now or datetime.now(timezone.utc)).astimezone(timezone.utc)
        if expires <= issued or expires <= current:
            raise CandidateArtifactProvenanceError("candidate attestation is expired")
        if expires - issued > _MAXIMUM_ATTESTATION_LIFETIME:
            raise CandidateArtifactProvenanceError(
                "candidate attestation lifetime exceeds protected maximum"
            )
        if issued > current + timedelta(minutes=5):
            raise CandidateArtifactProvenanceError("candidate attestation is not yet valid")
        if expected_source_sha is not None and self.source_sha != expected_source_sha:
            raise CandidateArtifactProvenanceError(
                "candidate attestation source SHA does not match certified PDD head"
            )
        if self.builder_workflow_identity != policy.builder_workflow_identity:
            raise CandidateArtifactProvenanceError(
                "candidate attestation builder workflow is not protected"
            )
        if self.dependency_lock_sha256 != policy.dependency_lock_sha256:
            raise CandidateArtifactProvenanceError(
                "candidate attestation dependency lock does not match"
            )
        expected_python = {
            "implementation": policy.python_implementation,
            "version": policy.python_version,
            "abi": policy.python_abi,
            "platform": policy.python_platform,
        }
        if self.python != expected_python:
            raise CandidateArtifactProvenanceError(
                "candidate attestation interpreter does not match"
            )
        if consume_replay:
            policy.consume(self.attestation_id, self.nonce)


def load_candidate_artifact_provenance(
    path: Path,
    wheel: Path,
    policy: CandidateArtifactPolicy,
) -> CandidateArtifactProvenance:
    """Load an untrusted statement and bind it to exact wheel bytes before use."""
    attestation = Path(path)
    candidate = Path(wheel)
    if candidate.is_symlink() or not candidate.is_file() or candidate.suffix != ".whl":
        raise CandidateArtifactProvenanceError("candidate wheel path is unsafe")
    if attestation.is_symlink() or not attestation.is_file():
        raise CandidateArtifactProvenanceError("candidate attestation path is unsafe")
    try:
        provenance = CandidateArtifactProvenance.from_payload(
            json.loads(attestation.read_text(encoding="utf-8"))
        )
    except (OSError, json.JSONDecodeError) as exc:
        raise CandidateArtifactProvenanceError("candidate attestation cannot be read") from exc
    if _sha256(candidate) != provenance.wheel_sha256:
        raise CandidateArtifactProvenanceError("candidate wheel digest does not match attestation")
    provenance.verify(policy, expected_source_sha=None, consume_replay=False)
    return provenance


def candidate_artifact_policy_from_environment() -> CandidateArtifactPolicy:
    """Load only protected-CI inputs required to authorize a candidate build."""
    names = {
        "issuer": "PDD_CANDIDATE_ATTESTATION_ISSUER",
        "public_key": "PDD_CANDIDATE_ATTESTATION_PUBLIC_KEY",
        "builder_workflow_identity": "PDD_CANDIDATE_BUILDER_WORKFLOW_IDENTITY",
        "dependency_lock_sha256": "PDD_CANDIDATE_DEPENDENCY_LOCK_SHA256",
        "python_implementation": "PDD_CANDIDATE_PYTHON_IMPLEMENTATION",
        "python_version": "PDD_CANDIDATE_PYTHON_VERSION",
        "python_abi": "PDD_CANDIDATE_PYTHON_ABI",
        "python_platform": "PDD_CANDIDATE_PYTHON_PLATFORM",
    }
    values = {name: os.environ.get(env_name, "") for name, env_name in names.items()}
    if not all(values.values()):
        raise CandidateArtifactProvenanceError(
            "protected candidate artifact provenance is required"
        )
    try:
        values["public_key"] = base64.b64decode(values["public_key"], validate=True)
    except ValueError as exc:
        raise CandidateArtifactProvenanceError(
            "candidate artifact public key is malformed"
        ) from exc
    return CandidateArtifactPolicy(**values)
