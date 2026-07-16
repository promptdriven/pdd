"""Versioned canonical fingerprint persistence and legacy read support."""

from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
import tempfile
from dataclasses import dataclass
from enum import Enum
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


class FingerprintMigrationError(FingerprintStoreError):
    """Raised when a migration request or reviewed manifest is invalid."""


class FingerprintMigrationAction(str, Enum):
    """One deterministic migration-planning disposition."""

    NO_OP = "NO_OP"
    VALIDATION_REQUIRED = "VALIDATION_REQUIRED"
    BLOCKED = "BLOCKED"


@dataclass(frozen=True)
class FingerprintMigrationOptions:
    """Read-only-by-default inputs for canonical fingerprint migration."""

    review_manifest_path: Path
    base_ref: str
    head_ref: str = "HEAD"
    modules: tuple[PurePosixPath, ...] = ()
    full_repository: bool = False
    limit: int = 100
    cursor: str | None = None


@dataclass(frozen=True)
class FingerprintMigrationEntry:
    """Auditable disposition for one stable unit identity."""

    unit_id: UnitId
    action: FingerprintMigrationAction
    semantic_status: SemanticStatus
    before_digest: str | None
    after_digest: str | None
    artifacts: tuple[ArtifactSnapshot, ...]
    blockers: tuple[str, ...] = ()
    stored_semantic_status: SemanticStatus | None = None

    def as_dict(self) -> dict[str, Any]:
        """Return a stable machine-readable migration entry."""
        return {
            "unit": _unit_payload(self.unit_id),
            "action": self.action.value,
            "semantic_status": self.semantic_status.value,
            "stored_semantic_status": (
                self.stored_semantic_status.value
                if self.stored_semantic_status is not None
                else None
            ),
            "before_digest": self.before_digest,
            "after_digest": self.after_digest,
            "artifacts": [
                {
                    "role": item.role,
                    "path": item.relpath.as_posix(),
                    "hash": item.digest,
                    "git_mode": item.git_mode,
                    "required": item.required,
                }
                for item in sorted(self.artifacts)
            ],
            "blockers": list(self.blockers),
        }


@dataclass(frozen=True)
class FingerprintMigrationReport:
    """Deterministic migration page with explicit trust limitations."""

    repository_id: str
    base_sha: str
    head_sha: str
    entries: tuple[FingerprintMigrationEntry, ...]
    next_cursor: str | None
    blockers: tuple[str, ...] = ()
    applied: bool = False
    transaction_id: str | None = None

    @property
    def ok(self) -> bool:
        """Return whether planning found no fail-closed blockers."""
        return not self.blockers and all(
            item.action is not FingerprintMigrationAction.BLOCKED
            for item in self.entries
        )

    def as_dict(self) -> dict[str, Any]:
        """Return the stable JSON report contract."""
        return {
            "schema_version": 1,
            "ok": self.ok,
            "mode": "APPLY" if self.applied else "DRY_RUN",
            "repository_id": self.repository_id,
            "base_sha": self.base_sha,
            "head_sha": self.head_sha,
            "trust_status": "NOT_EVALUATED",
            "semantic_status": "UNKNOWN",
            "entries": [item.as_dict() for item in self.entries],
            "next_cursor": self.next_cursor,
            "blockers": list(self.blockers),
            "transaction_id": self.transaction_id,
        }


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


@dataclass(frozen=True)
class _ReviewedMigrationUnit:
    """One human-reviewed semantic decision bound to an exact snapshot."""

    unit_id: UnitId
    expected_snapshot_digest: str
    reviewed_by: str
    reason: str


def _load_migration_reviews(
    path: Path,
    *,
    repository_id: str,
    head_sha: str,
) -> dict[UnitId, _ReviewedMigrationUnit]:
    """Load a strict reviewed manifest without accepting unknown schema fields."""
    try:
        payload = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise FingerprintMigrationError(
            f"cannot read reviewed migration manifest: {path}"
        ) from exc
    expected_root = {"schema_version", "repository_id", "head_sha", "units"}
    if not isinstance(payload, dict) or set(payload) != expected_root:
        raise FingerprintMigrationError("reviewed migration manifest schema is invalid")
    if payload["schema_version"] != 1:
        raise FingerprintMigrationError("unsupported reviewed migration schema")
    if payload["repository_id"] != repository_id:
        raise FingerprintMigrationError("reviewed manifest repository identity differs")
    if payload["head_sha"] != head_sha:
        raise FingerprintMigrationError("reviewed manifest is not bound to checked HEAD")
    rows = payload["units"]
    if not isinstance(rows, list):
        raise FingerprintMigrationError("reviewed migration units must be a list")
    expected_row = {
        "prompt_path",
        "language_id",
        "decision",
        "expected_snapshot_digest",
        "reviewed_by",
        "reason",
    }
    reviews: dict[UnitId, _ReviewedMigrationUnit] = {}
    for index, row in enumerate(rows):
        if not isinstance(row, dict) or set(row) != expected_row:
            raise FingerprintMigrationError(
                f"reviewed migration unit {index} schema is invalid"
            )
        values = tuple(row[name] for name in expected_row)
        if not all(isinstance(value, str) for value in values):
            raise FingerprintMigrationError(
                f"reviewed migration unit {index} fields must be strings"
            )
        if row["decision"] != "REVIEWED":
            raise FingerprintMigrationError(
                f"reviewed migration unit {index} decision must be REVIEWED"
            )
        digest = row["expected_snapshot_digest"]
        if len(digest) != 64 or any(character not in "0123456789abcdef" for character in digest):
            raise FingerprintMigrationError(
                f"reviewed migration unit {index} snapshot digest is invalid"
            )
        reviewed_by = row["reviewed_by"].strip()
        reason = row["reason"].strip()
        if not reviewed_by or not reason:
            raise FingerprintMigrationError(
                f"reviewed migration unit {index} requires reviewer and rationale"
            )
        try:
            unit_id = UnitId(
                repository_id,
                PurePosixPath(row["prompt_path"]),
                row["language_id"],
            )
        except ValueError as exc:
            raise FingerprintMigrationError(
                f"reviewed migration unit {index} identity is invalid"
            ) from exc
        if unit_id in reviews:
            raise FingerprintMigrationError(
                f"duplicate reviewed migration unit: {unit_id.prompt_relpath}"
            )
        reviews[unit_id] = _ReviewedMigrationUnit(
            unit_id, digest, reviewed_by, reason
        )
    return reviews


def _migration_worktree_blocker(root: Path, head_sha: str) -> str | None:
    """Reject snapshots not backed by the exact checked commit."""
    from .git_io import resolve_git_commit

    if resolve_git_commit(root, "HEAD") != head_sha:
        return "checked HEAD does not match the migration head"
    result = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        return "cannot inspect migration checkout state"
    allowed = (
        ".pdd/meta/v2/",
        ".pdd/evidence/v2/",
        ".pdd/locks/fingerprints/",
        ".pdd/locks/transactions/",
        ".pdd/transactions/",
    )
    fields = result.stdout.split(b"\0")
    index = 0
    while index < len(fields) and fields[index]:
        record = fields[index]
        if len(record) < 4:
            return "migration checkout status is malformed"
        code = record[:2]
        paths = [record[3:].decode("utf-8", errors="surrogateescape")]
        if b"R" in code or b"C" in code:
            index += 1
            if index >= len(fields) or not fields[index]:
                return "migration checkout status is malformed"
            paths.append(fields[index].decode("utf-8", errors="surrogateescape"))
        if any(not path.startswith(allowed) for path in paths):
            return "migration requires a clean checkout at the checked HEAD"
        index += 1
    return None


def _selected_migration_units(manifest, options: FingerprintMigrationOptions):
    """Select a stable, exact migration page and return its continuation cursor."""
    if options.full_repository == bool(options.modules):
        raise FingerprintMigrationError(
            "choose exactly one of full_repository or one-or-more modules"
        )
    if options.limit <= 0:
        raise FingerprintMigrationError("migration limit must be positive")
    managed = tuple(sorted(manifest.managed_units, key=lambda item: item.unit_id))
    if options.modules:
        requested = set(options.modules)
        invalid = [
            path for path in requested
            if path.is_absolute() or not path.parts or ".." in path.parts
        ]
        if invalid:
            raise FingerprintMigrationError("migration module paths must be repository-relative")
        selected = tuple(
            unit for unit in managed if unit.unit_id.prompt_relpath in requested
        )
        found = {unit.unit_id.prompt_relpath for unit in selected}
        missing = requested - found
        if missing:
            raise FingerprintMigrationError(
                "migration modules are not exact managed prompts: "
                + ", ".join(path.as_posix() for path in sorted(missing))
            )
    else:
        selected = managed
    if options.cursor is not None:
        cursor = PurePosixPath(options.cursor)
        if cursor.is_absolute() or not cursor.parts or ".." in cursor.parts:
            raise FingerprintMigrationError("migration cursor is invalid")
        selected = tuple(
            unit
            for unit in selected
            if unit.unit_id.prompt_relpath.as_posix() > cursor.as_posix()
        )
    page = selected[: options.limit]
    next_cursor = (
        page[-1].unit_id.prompt_relpath.as_posix()
        if len(selected) > len(page) and page
        else None
    )
    return page, next_cursor


def plan_fingerprint_migration(
    root: Path,
    options: FingerprintMigrationOptions,
) -> FingerprintMigrationReport:
    """Plan canonical v2 migration without writing repository state."""
    from .git_io import resolve_git_commit
    from .manifest import build_unit_manifest, require_valid_manifest
    from .snapshot import SnapshotError, build_unit_snapshot
    from .verification import load_verification_profiles

    repository_root = Path(root).resolve()
    base_sha = resolve_git_commit(repository_root, options.base_ref)
    head_sha = resolve_git_commit(repository_root, options.head_ref)
    manifest = build_unit_manifest(
        repository_root, base_ref=base_sha, head_ref=head_sha
    )
    try:
        require_valid_manifest(manifest)
    except ValueError as exc:
        raise FingerprintMigrationError(str(exc)) from exc
    if {unit.unit_id for unit in manifest.managed_units} != set(
        manifest.expected_managed
    ):
        raise FingerprintMigrationError(
            "migration requires complete protected managed-unit coverage"
        )
    profiles = load_verification_profiles(repository_root, manifest)
    if profiles.invalid_reasons:
        raise FingerprintMigrationError(
            "verification profiles are invalid: " + "; ".join(profiles.invalid_reasons)
        )
    reviews = _load_migration_reviews(
        options.review_manifest_path,
        repository_id=manifest.repository_id,
        head_sha=head_sha,
    )
    units, next_cursor = _selected_migration_units(manifest, options)
    store = FingerprintStore(repository_root)
    worktree_blocker = _migration_worktree_blocker(repository_root, head_sha)
    entries: list[FingerprintMigrationEntry] = []
    for unit in units:
        blockers: list[str] = []
        profile = profiles.for_unit(unit.unit_id)
        snapshot = None
        if profile is None or not profile.complete:
            blockers.append("unit lacks a complete protected verification profile")
        else:
            try:
                snapshot = build_unit_snapshot(
                    repository_root, manifest, unit, profile
                )
            except SnapshotError as exc:
                blockers.append(str(exc))
        if worktree_blocker is not None:
            blockers.append(worktree_blocker)
        record = None
        try:
            record = store.load(unit.unit_id)
        except CorruptFingerprintError as exc:
            blockers.append(str(exc))
        before_digest = record.snapshot.digest() if record is not None else None
        after_digest = snapshot.digest() if snapshot is not None else None
        stored_semantic = (
            record.claimed_semantic_status if record is not None else None
        )
        if blockers:
            action = FingerprintMigrationAction.BLOCKED
        elif record is not None and record.snapshot == snapshot:
            action = FingerprintMigrationAction.NO_OP
        else:
            review = reviews.get(unit.unit_id)
            if review is None:
                blockers.append("exact semantic review is absent")
            elif review.expected_snapshot_digest != after_digest:
                blockers.append("semantic review snapshot digest is stale")
            action = (
                FingerprintMigrationAction.BLOCKED
                if blockers
                else FingerprintMigrationAction.VALIDATION_REQUIRED
            )
        entries.append(
            FingerprintMigrationEntry(
                unit.unit_id,
                action,
                SemanticStatus.UNKNOWN,
                before_digest,
                after_digest,
                snapshot.artifacts if snapshot is not None else (),
                tuple(blockers),
                stored_semantic,
            )
        )
    return FingerprintMigrationReport(
        manifest.repository_id,
        base_sha,
        head_sha,
        tuple(entries),
        next_cursor,
    )


def apply_fingerprint_migration(
    root: Path,
    options: FingerprintMigrationOptions,
    *,
    signer,
    replay_ledger_path: Path | None = None,
    config=None,
) -> FingerprintMigrationReport:
    """Apply one safe unit through the existing trusted finalization path."""
    from .finalize import finalize_unit
    from .runner import RunnerConfig

    report = plan_fingerprint_migration(root, options)
    if not report.ok:
        return FingerprintMigrationReport(
            report.repository_id,
            report.base_sha,
            report.head_sha,
            report.entries,
            report.next_cursor,
            ("migration apply is blocked by the dry-run report",),
        )
    actionable = tuple(
        item
        for item in report.entries
        if item.action is FingerprintMigrationAction.VALIDATION_REQUIRED
    )
    if not actionable:
        return FingerprintMigrationReport(
            report.repository_id,
            report.base_sha,
            report.head_sha,
            report.entries,
            report.next_cursor,
            applied=True,
        )
    if len(actionable) != 1:
        return FingerprintMigrationReport(
            report.repository_id,
            report.base_sha,
            report.head_sha,
            report.entries,
            report.next_cursor,
            (
                "atomic multi-unit trusted finalization is unavailable; "
                "apply one reviewed module at a time",
            ),
        )
    result = finalize_unit(
        Path(root).resolve(),
        actionable[0].unit_id.prompt_relpath,
        base_ref=report.base_sha,
        head_ref=report.head_sha,
        signer=signer,
        config=config if config is not None else RunnerConfig(),
        replay_ledger_path=replay_ledger_path,
    )
    updated = plan_fingerprint_migration(root, options)
    return FingerprintMigrationReport(
        updated.repository_id,
        updated.base_sha,
        updated.head_sha,
        updated.entries,
        updated.next_cursor,
        updated.blockers,
        True,
        result.transaction.transaction_id,
    )
