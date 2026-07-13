"""Versioned canonical fingerprint persistence and legacy read support."""

from __future__ import annotations

import hashlib
import json
import os
import stat
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, Optional

from filelock import FileLock

from .durability import fsync_directory
from .identity import read_repository_identity
from .types import (
    ArtifactSnapshot,
    FingerprintProvenance,
    FingerprintRecord,
    SemanticStatus,
    UnitId,
    UnitSnapshot,
)


class FingerprintStoreError(ValueError):
    """Raised when canonical fingerprint state cannot be validated or persisted."""


class CorruptFingerprintError(FingerprintStoreError):
    """Raised when stored state exists but is malformed or inconsistent."""


@dataclass(frozen=True)
class LegacyFingerprintRecord:
    """Readable legacy metadata that cannot certify canonical synchronization."""

    path: Path
    payload: Mapping[str, Any]


def _unit_payload(unit_id: UnitId) -> dict[str, str]:
    return {
        "repository_id": unit_id.repository_id,
        "prompt_relpath": unit_id.prompt_relpath.as_posix(),
        "language_id": unit_id.language_id,
    }


def _record_payload(record: FingerprintRecord) -> dict[str, Any]:
    return {
        "schema_version": record.schema_version,
        "hash_algorithm_version": record.hash_algorithm_version,
        "unit_id": _unit_payload(record.snapshot.unit_id),
        "artifacts": [
            {
                "role": item.role,
                "path": item.relpath.as_posix(),
                "hash": item.digest,
                "git_mode": item.git_mode,
                "required": item.required,
            }
            for item in sorted(record.snapshot.artifacts)
        ],
        "manifest_digest": record.snapshot.manifest_digest,
        "dependency_snapshot_digest": record.snapshot.dependency_snapshot_digest,
        "verification_profile_digest": record.snapshot.verification_profile_digest,
        "nondeterministic_inputs": record.snapshot.nondeterministic_inputs,
        "provenance": {
            "kind": record.provenance.kind,
            "command": record.provenance.command,
            "transaction_id": record.provenance.transaction_id,
            "git_commit": record.provenance.git_commit,
            "timestamp": record.provenance.timestamp,
            "pdd_version": record.provenance.pdd_version,
            "reviewed_by": record.provenance.reviewed_by,
            "reason": record.provenance.reason,
        },
        "claimed_semantic_status": record.claimed_semantic_status.value,
        "attestation_ref": record.attestation_ref,
    }


def encode_fingerprint(record: FingerprintRecord) -> bytes:
    """Encode a validated record for inclusion in a larger transaction."""
    return json.dumps(
        _record_payload(record), sort_keys=True, indent=2
    ).encode("utf-8") + b"\n"


def _required(payload: Mapping[str, Any], key: str, expected_type: type) -> Any:
    value = payload.get(key)
    if not isinstance(value, expected_type):
        raise CorruptFingerprintError(f"fingerprint field {key!r} has invalid type")
    return value


def _parse_record(payload: Mapping[str, Any]) -> FingerprintRecord:
    try:
        unit_payload = _required(payload, "unit_id", dict)
        unit_id = UnitId(
            _required(unit_payload, "repository_id", str),
            PurePosixPath(_required(unit_payload, "prompt_relpath", str)),
            _required(unit_payload, "language_id", str),
        )
        artifacts_payload = _required(payload, "artifacts", list)
        artifacts = tuple(
            ArtifactSnapshot(
                _required(item, "role", str),
                PurePosixPath(_required(item, "path", str)),
                item.get("hash"),
                item.get("git_mode"),
                item.get("required", True),
            )
            for item in artifacts_payload
            if isinstance(item, dict)
        )
        if len(artifacts) != len(artifacts_payload):
            raise CorruptFingerprintError("fingerprint artifact entry is not an object")
        snapshot = UnitSnapshot(
            unit_id,
            artifacts,
            _required(payload, "manifest_digest", str),
            _required(payload, "dependency_snapshot_digest", str),
            _required(payload, "verification_profile_digest", str),
            bool(payload.get("nondeterministic_inputs", False)),
        )
        provenance_payload = _required(payload, "provenance", dict)
        reviewed_by = provenance_payload.get("reviewed_by")
        reason = provenance_payload.get("reason")
        if reviewed_by is not None and not isinstance(reviewed_by, str):
            raise CorruptFingerprintError("fingerprint reviewer must be a string or null")
        if reason is not None and not isinstance(reason, str):
            raise CorruptFingerprintError("fingerprint reason must be a string or null")
        provenance = FingerprintProvenance(
            _required(provenance_payload, "kind", str),
            _required(provenance_payload, "command", str),
            _required(provenance_payload, "transaction_id", str),
            _required(provenance_payload, "git_commit", str),
            _required(provenance_payload, "timestamp", str),
            _required(provenance_payload, "pdd_version", str),
            reviewed_by,
            reason,
        )
        claimed = SemanticStatus(_required(payload, "claimed_semantic_status", str))
        attestation_ref = payload.get("attestation_ref")
        if attestation_ref is not None and not isinstance(attestation_ref, str):
            raise CorruptFingerprintError("attestation_ref must be a string or null")
        return FingerprintRecord(
            snapshot,
            _required(payload, "schema_version", int),
            _required(payload, "hash_algorithm_version", int),
            provenance,
            claimed,
            attestation_ref,
        )
    except (TypeError, ValueError) as exc:
        if isinstance(exc, CorruptFingerprintError):
            raise
        raise CorruptFingerprintError(f"fingerprint payload is invalid: {exc}") from exc


class FingerprintStore:
    """Locked atomic store for canonical v2 fingerprint records."""

    def __init__(self, checkout_root: Path) -> None:
        self.checkout_root = Path(checkout_root).resolve()
        self.repository_id = read_repository_identity(
            self.checkout_root, require_persistent=True
        ).value
        self.meta_dir = self.checkout_root / ".pdd/meta/v2"
        self.lock_dir = self.checkout_root / ".pdd/locks/fingerprints"

    @staticmethod
    def _key(unit_id: UnitId) -> str:
        payload = json.dumps(_unit_payload(unit_id), sort_keys=True).encode()
        return hashlib.sha256(payload).hexdigest()

    def path_for(self, unit_id: UnitId) -> Path:
        """Return the collision-resistant canonical path for one unit identity."""
        return self.meta_dir / f"{self._key(unit_id)}.json"

    def _ensure_state_directory(self, directory: Path, mode: int) -> None:
        current = self.checkout_root
        for part in directory.relative_to(self.checkout_root).parts:
            current = current / part
            if current.exists() or current.is_symlink():
                current_mode = current.lstat().st_mode
                if stat.S_ISLNK(current_mode) or not stat.S_ISDIR(current_mode):
                    raise FingerprintStoreError(f"state directory is unsafe: {current}")
            else:
                current.mkdir(mode=mode)

    def validate(self, record: FingerprintRecord) -> None:
        """Validate a record before direct or transactional persistence."""
        if record.snapshot.unit_id.repository_id != self.repository_id:
            raise FingerprintStoreError("fingerprint repository identity does not match")
        if not record.valid:
            raise FingerprintStoreError("only complete canonical v2 records may be written")
        missing = [
            item.role
            for item in record.snapshot.artifacts
            if item.required and not item.exists
        ]
        if missing:
            raise FingerprintStoreError(
                "required artifacts have null hash or mode: " + ", ".join(sorted(missing))
            )
        if (
            record.claimed_semantic_status is SemanticStatus.VERIFIED
            and not record.attestation_ref
        ):
            raise FingerprintStoreError("VERIFIED fingerprint requires an attestation")
        if (
            record.provenance.kind == "baseline-reset"
            and record.claimed_semantic_status is not SemanticStatus.UNKNOWN
        ):
            raise FingerprintStoreError("baseline reset must remain semantic UNKNOWN")
        if record.provenance.kind == "baseline-reset" and (
            not record.provenance.reviewed_by or not record.provenance.reason
        ):
            raise FingerprintStoreError(
                "baseline reset requires a recorded reviewer and rationale"
            )

    def load(self, unit_id: UnitId) -> Optional[FingerprintRecord]:
        """Load and validate one canonical record without mutating state."""
        path = self.path_for(unit_id)
        if not path.exists():
            return None
        if path.is_symlink() or not path.is_file():
            raise CorruptFingerprintError("fingerprint path is not a regular file")
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise CorruptFingerprintError(f"cannot decode fingerprint: {path}") from exc
        if not isinstance(payload, dict):
            raise CorruptFingerprintError("fingerprint root must be an object")
        record = _parse_record(payload)
        if record.snapshot.unit_id != unit_id:
            raise CorruptFingerprintError("fingerprint key and embedded identity differ")
        self.validate(record)
        return record

    def write(self, record: FingerprintRecord) -> Path:
        """Atomically replace one validated record while holding its process lock."""
        self.validate(record)
        self._ensure_state_directory(self.meta_dir, 0o755)
        self._ensure_state_directory(self.lock_dir, 0o700)
        path = self.path_for(record.snapshot.unit_id)
        lock_path = self.lock_dir / f"{path.stem}.lock"
        encoded = encode_fingerprint(record)
        with FileLock(str(lock_path)):
            descriptor, temporary_name = tempfile.mkstemp(
                prefix=f".{path.name}.", suffix=".tmp", dir=self.meta_dir
            )
            temporary = Path(temporary_name)
            try:
                os.fchmod(descriptor, 0o644)
                with os.fdopen(descriptor, "wb") as handle:
                    handle.write(encoded)
                    handle.flush()
                    os.fsync(handle.fileno())
                os.replace(temporary, path)
                fsync_directory(self.meta_dir)
            except BaseException:
                temporary.unlink(missing_ok=True)
                raise
        return path

    def read_legacy(self, path: Path) -> LegacyFingerprintRecord:
        """Read legacy JSON for migration without granting it v2 authority."""
        candidate = Path(path)
        if not candidate.is_absolute():
            candidate = self.checkout_root / candidate
        try:
            candidate_mode = candidate.lstat().st_mode
        except OSError as exc:
            raise FingerprintStoreError("legacy fingerprint is not a regular file") from exc
        if stat.S_ISLNK(candidate_mode) or not stat.S_ISREG(candidate_mode):
            raise FingerprintStoreError("legacy fingerprint is not a regular file")
        resolved = candidate.resolve(strict=True)
        try:
            resolved.relative_to(self.checkout_root)
        except ValueError as exc:
            raise FingerprintStoreError("legacy fingerprint escapes checkout") from exc
        if not resolved.is_file():
            raise FingerprintStoreError("legacy fingerprint is not a regular file")
        try:
            payload = json.loads(resolved.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise CorruptFingerprintError("legacy fingerprint is malformed") from exc
        if not isinstance(payload, dict):
            raise CorruptFingerprintError("legacy fingerprint root must be an object")
        return LegacyFingerprintRecord(resolved, payload)
