"""Transactional fingerprint finalization.

Every successful fingerprint write is prepared and validated here.  Callers may
either commit immediately or provide the sync orchestrator's atomic-state buffer;
both paths use the same payload construction and null-hash checks.

``os.replace`` is atomic on POSIX when source and destination share a filesystem.
Windows has weaker replacement guarantees when the destination already exists.
"""
from __future__ import annotations

import logging
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional

from . import __version__
from .json_atomic import atomic_write_json
from .operation_log import get_fingerprint_path
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


__all__ = ["FingerprintFinalizeError", "FingerprintTransaction"]
