"""Transactional fingerprint finalization.

Every successful fingerprint write is prepared and validated here.  Callers may
either commit immediately or provide the sync orchestrator's atomic-state buffer;
both paths use the same payload construction and null-hash checks.

``os.replace`` is atomic on POSIX when source and destination share a filesystem.
Windows has weaker replacement guarantees when the destination already exists.
"""
from __future__ import annotations

import hashlib
import json
import logging
import uuid
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Dict, Mapping, Optional

from . import __version__
from .json_atomic import atomic_write_json
from .operation_log import get_fingerprint_path, get_run_report_path
from .sync_determine_operation import (
    Fingerprint,
    calculate_current_hashes,
    get_pdd_file_paths,
    read_fingerprint,
)

logger = logging.getLogger(__name__)


class FingerprintFinalizeError(RuntimeError):
    """Raised when a fingerprint cannot be finalized safely."""

    def __init__(self, operation: str, fingerprint_path: Path, cause: object):
        self.operation = operation
        self.fingerprint_path = Path(fingerprint_path)
        self.cause = cause
        super().__init__(
            f"[{operation}] fingerprint finalization failed for "
            f"{self.fingerprint_path}: {cause}"
        )


@dataclass
class PendingStateUpdate:
    """Fingerprint/run-report payloads waiting for one durable commit."""

    run_report: Optional[Dict[str, Any]] = None
    fingerprint: Optional[Dict[str, Any]] = None
    run_report_path: Optional[Path] = None
    fingerprint_path: Optional[Path] = None
    fingerprint_operation: Optional[str] = None


def _metadata_checkout_root(*paths: Path) -> Path:
    """Return the common project root owning metadata destinations."""
    roots: set[Path] = set()
    for raw_path in paths:
        path = Path(raw_path).resolve(strict=False)
        pdd_dir = next((parent for parent in path.parents if parent.name == ".pdd"), None)
        if pdd_dir is None:
            raise ValueError(f"metadata destination is outside .pdd: {raw_path}")
        roots.add(pdd_dir.parent)
    if len(roots) != 1:
        raise ValueError("fingerprint and run report belong to different projects")
    return roots.pop()


def _metadata_transaction_prefix(basename: str, language: str) -> str:
    identity = f"{basename}\0{language.lower()}".encode("utf-8")
    return f"metadata-{hashlib.sha256(identity).hexdigest()[:20]}-"


def _json_payload_bytes(payload: Mapping[str, Any]) -> bytes:
    """Encode metadata exactly once for the durable multi-file transaction."""
    return (
        json.dumps(payload, indent=2, ensure_ascii=False).encode("utf-8") + b"\n"
    )


def _recover_scoped_transactions(
    manager: Any,
    basename: str,
    language: str,
) -> tuple[str, ...]:
    """Recover only WAL entries owned by one legacy metadata identity."""
    prefix = _metadata_transaction_prefix(basename, language)
    recovered: list[str] = []
    for transaction_id in manager.incomplete():
        if not transaction_id.startswith(prefix):
            continue
        manager.recover(transaction_id)
        recovered.append(transaction_id)
    return tuple(recovered)


def recover_incomplete_metadata_transactions(
    basename: str,
    language: str,
    paths: Optional[Dict[str, Path]] = None,
) -> tuple[str, ...]:
    """Recover crash-interrupted metadata commits for one dev-unit identity.

    Recovery is deliberately scoped by a hashed basename/language prefix; a
    legacy sync must never adopt an unrelated canonical-sync transaction.
    PREPARED journals roll back without publishing bytes, while COMMITTING
    journals finish the complete run-report/fingerprint pair.
    """
    from .sync_core.transaction import TransactionManager

    fingerprint_path = get_fingerprint_path(basename, language, paths=paths)
    run_report_path = get_run_report_path(basename, language, paths=paths)
    root = _metadata_checkout_root(fingerprint_path, run_report_path)
    manager = TransactionManager(root)
    try:
        recovered = _recover_scoped_transactions(manager, basename, language)
    except Exception as exc:
        raise FingerprintFinalizeError(
            "recovery",
            fingerprint_path,
            f"metadata transaction recovery failed: {exc}",
        ) from exc
    return recovered


class AtomicStateUpdate:
    """Crash-durably commit a run report and fingerprint as one closure.

    Each destination is still installed with an atomic rename, but a durable
    write-ahead journal spans both renames. A process death at either boundary
    therefore leaves an explicit COMMITTING record that the next sync recovers
    before selecting an operation. The run report is installed first and the
    fingerprint (the completion checkpoint) last.
    """

    def __init__(
        self,
        basename: str,
        language: str,
        *,
        paths: Optional[Dict[str, Path]] = None,
    ) -> None:
        self.basename = basename
        self.language = language.lower()
        self.paths = paths
        self.pending = PendingStateUpdate()
        self._crash_hook: Optional[Callable[[str], None]] = None

    def __enter__(self) -> "AtomicStateUpdate":
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> bool:
        if exc_type is None:
            self._commit()
        return False

    def set_run_report(self, report: Dict[str, Any], path: Path) -> None:
        """Buffer a run report for the outer durable commit."""
        self.pending.run_report = dict(report)
        self.pending.run_report_path = Path(path)

    def set_fingerprint(
        self,
        fingerprint: Dict[str, Any],
        path: Path,
        *,
        operation: Optional[str] = None,
    ) -> None:
        """Buffer a canonical fingerprint for the outer durable commit."""
        self.pending.fingerprint = dict(fingerprint)
        self.pending.fingerprint_path = Path(path)
        self.pending.fingerprint_operation = operation

    def _commit(self) -> None:
        from .sync_core.transaction import (
            PlannedWrite,
            TransactionManager,
            TransactionPhase,
        )

        destinations = [
            path
            for path in (
                self.pending.run_report_path,
                self.pending.fingerprint_path,
            )
            if path is not None
        ]
        if not destinations:
            return

        diagnostic_path = self.pending.fingerprint_path or destinations[0]
        operation = self.pending.fingerprint_operation or "metadata"
        try:
            root = _metadata_checkout_root(*destinations)
            manager = TransactionManager(root)
            _recover_scoped_transactions(manager, self.basename, self.language)
            writes: list[PlannedWrite] = []
            if (
                self.pending.run_report is not None
                and self.pending.run_report_path is not None
            ):
                relative = self.pending.run_report_path.resolve(strict=False).relative_to(
                    root
                )
                writes.append(
                    PlannedWrite(
                        PurePosixPath(relative.as_posix()),
                        _json_payload_bytes(self.pending.run_report),
                        "100644",
                    )
                )
            if (
                self.pending.fingerprint is not None
                and self.pending.fingerprint_path is not None
            ):
                relative = self.pending.fingerprint_path.resolve(
                    strict=False
                ).relative_to(root)
                writes.append(
                    PlannedWrite(
                        PurePosixPath(relative.as_posix()),
                        _json_payload_bytes(self.pending.fingerprint),
                        "100644",
                    )
                )
            if not writes:
                return

            transaction_id = (
                _metadata_transaction_prefix(self.basename, self.language)
                + uuid.uuid4().hex
            )
            prepared = manager.prepare(transaction_id, tuple(writes))
            if prepared.no_op:
                return
            try:
                committed = manager.commit(
                    transaction_id,
                    crash_hook=self._crash_hook,
                )
            except Exception:
                # Ordinary I/O errors are recoverable in-process when possible.
                # BaseException (SIGKILL simulation/SystemExit) deliberately
                # bypasses this path and leaves the durable journal for restart.
                committed = manager.recover(transaction_id)
            if committed.phase is not TransactionPhase.COMMITTED:
                raise RuntimeError(
                    f"metadata transaction ended in {committed.phase.value}"
                )
        except FingerprintFinalizeError:
            raise
        except Exception as exc:
            raise FingerprintFinalizeError(
                operation,
                diagnostic_path,
                f"atomic state commit failed: {exc}",
            ) from exc


def _coerce_paths(paths: Mapping[str, Any]) -> Dict[str, Any]:
    """Normalize path hints without changing their caller-selected scope."""
    normalized: Dict[str, Any] = {}
    for key, value in paths.items():
        if key == "test_files":
            if value is None:
                normalized[key] = []
            else:
                normalized[key] = [
                    item if isinstance(item, Path) else Path(item)
                    for item in value
                ]
        elif value is None or isinstance(value, Path):
            normalized[key] = value
        else:
            normalized[key] = Path(value)
    return normalized


class FingerprintTransaction:
    """Commit a complete fingerprint on clean context-manager exit.

    ``atomic_state`` is the sync orchestrator's optional metadata buffer.  It is
    deliberately duck-typed so this leaf module never imports the orchestrator.
    """

    def __init__(
        self,
        basename: str,
        language: str,
        operation: str,
        paths: Optional[Dict[str, Path]] = None,
        cost: float = 0.0,
        model: str = "",
        *,
        atomic_state: Optional[Any] = None,
    ) -> None:
        self._basename = basename
        self._language = language.lower()
        self._operation = operation
        self._cost = float(cost or 0.0)
        self._model = model
        self._atomic_state = atomic_state
        self._skipped = False
        self._skip_reason: Optional[str] = None
        self._include_deps_override: Optional[Dict[str, str]] = None

        fallback_path = (
            Path(".pdd")
            / "meta"
            / f"{basename.replace('/', '_')}_{self._language}.json"
        )
        try:
            resolved_paths: Mapping[str, Any]
            if paths:
                # Preserve issue #983: explicit paths are authoritative and must
                # not be replaced by CWD-based discovery.
                resolved_paths = paths
            else:
                resolved_paths = get_pdd_file_paths(basename, self._language)
            self._paths = _coerce_paths(resolved_paths)
            self._fingerprint_path = get_fingerprint_path(
                basename,
                self._language,
                paths=self._paths,
            )
        except Exception as exc:
            raise FingerprintFinalizeError(
                operation,
                fallback_path,
                f"path resolution failed: {exc}",
            ) from exc

    @property
    def fingerprint_path(self) -> Path:
        """Return the eagerly resolved destination path."""
        return self._fingerprint_path

    def __enter__(self) -> "FingerprintTransaction":
        return self

    def skip(self, reason: str) -> None:
        """Suppress finalization for an intentional non-mutating path."""
        self._skipped = True
        self._skip_reason = str(reason)
        logger.info(
            "FingerprintTransaction.skip for %s/%s (%s): %s",
            self._basename,
            self._language,
            self._operation,
            self._skip_reason,
        )

    def set_include_deps_override(self, deps: Dict[str, str]) -> None:
        """Use a pre-mutation include graph for hashing and persistence."""
        self._include_deps_override = dict(deps)

    def _validate_hashes(self, current_hashes: Mapping[str, Any]) -> None:
        """Reject fingerprints that cannot represent their existing inputs."""
        if current_hashes.get("prompt_hash") is None:
            raise FingerprintFinalizeError(
                self._operation,
                self._fingerprint_path,
                "prompt_hash is null",
            )

        for key in ("code", "example", "test"):
            value = self._paths.get(key)
            if isinstance(value, Path) and value.exists():
                hash_field = f"{key}_hash"
                if current_hashes.get(hash_field) is None:
                    raise FingerprintFinalizeError(
                        self._operation,
                        self._fingerprint_path,
                        f"{hash_field} is null for existing path {value}",
                    )

        expected_tests = self._paths.get("test_files") or []
        actual_tests = current_hashes.get("test_files") or {}
        for test_path in expected_tests:
            if isinstance(test_path, Path) and test_path.exists():
                if actual_tests.get(test_path.name) is None:
                    raise FingerprintFinalizeError(
                        self._operation,
                        self._fingerprint_path,
                        f"test_files hash is null for existing path {test_path}",
                    )

    def _build_payload(self) -> Dict[str, Any]:
        previous = read_fingerprint(
            self._basename,
            self._language,
            paths=self._paths,
        )
        stored_deps = (
            self._include_deps_override
            if self._include_deps_override is not None
            else (previous.include_deps if previous else None)
        )
        current_hashes = calculate_current_hashes(
            self._paths,
            stored_include_deps=stored_deps,
        )
        self._validate_hashes(current_hashes)

        include_deps = (
            self._include_deps_override
            if self._include_deps_override is not None
            else current_hashes.get("include_deps")
        )
        fingerprint = Fingerprint(
            pdd_version=__version__,
            timestamp=datetime.now(timezone.utc).isoformat(),
            command=self._operation,
            prompt_hash=current_hashes.get("prompt_hash"),
            code_hash=current_hashes.get("code_hash"),
            example_hash=current_hashes.get("example_hash"),
            test_hash=current_hashes.get("test_hash"),
            test_files=current_hashes.get("test_files"),
            include_deps=include_deps,
        )
        return asdict(fingerprint)

    def _commit(self) -> None:
        try:
            payload = self._build_payload()
            if self._atomic_state is not None:
                setter = getattr(self._atomic_state, "set_fingerprint", None)
                if not callable(setter):
                    raise TypeError("atomic_state does not provide set_fingerprint()")
                setter(
                    payload,
                    self._fingerprint_path,
                    operation=self._operation,
                )
            else:
                atomic_write_json(self._fingerprint_path, payload)
        except FingerprintFinalizeError:
            raise
        except Exception as exc:
            raise FingerprintFinalizeError(
                self._operation,
                self._fingerprint_path,
                exc,
            ) from exc

    def __exit__(self, exc_type, exc_val, exc_tb) -> bool:
        if exc_type is not None:
            return False
        if self._skipped:
            logger.debug(
                "Fingerprint commit suppressed for %s/%s (%s): %s",
                self._basename,
                self._language,
                self._operation,
                self._skip_reason,
            )
            return False
        self._commit()
        return False


__all__ = [
    "AtomicStateUpdate",
    "FingerprintFinalizeError",
    "FingerprintTransaction",
    "recover_incomplete_metadata_transactions",
]
