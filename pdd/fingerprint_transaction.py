"""Transactional fingerprint finalization.

This module is the one implementation that computes and persists PDD
fingerprints.  ``os.replace`` is atomic on POSIX when source and destination
share a filesystem.  On Windows, replacing an existing destination does not
have the same POSIX atomicity guarantee; this is a known platform limitation.
"""

from __future__ import annotations

import json
import logging
import os
import tempfile
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional

from . import __version__
from .operation_log import get_fingerprint_path
from .sync_determine_operation import (
    Fingerprint,
    calculate_current_hashes,
    read_fingerprint,
)


logger = logging.getLogger(__name__)


class FingerprintFinalizeError(RuntimeError):
    """Raised when a required fingerprint cannot be finalized."""


class FingerprintTransaction:  # pylint: disable=too-many-instance-attributes
    """Compute and atomically persist one command fingerprint on clean exit."""

    def __init__(  # pylint: disable=too-many-arguments,too-many-positional-arguments
        self,
        basename: str,
        language: str,
        operation: str,
        paths: Optional[Dict[str, Path]] = None,
        cost: float = 0.0,
        model: str = "",
    ) -> None:
        self._basename = basename
        self._language = language.lower()
        self._operation = operation
        self._paths: Dict[str, Path] = dict(paths or {})
        self._cost = cost
        self._model = model
        # Resolve once. This prevents a cwd change during a command from moving
        # the final write to a different project (#1211/#1290).
        self._fingerprint_path = get_fingerprint_path(
            basename,
            self._language,
            paths=self._paths,
        )
        self._skipped = False
        self._skip_reason: Optional[str] = None
        self._include_deps_override: Optional[Dict[str, str]] = None

    @property
    def fingerprint_path(self) -> Path:
        """Return the eagerly-resolved destination path."""

        return self._fingerprint_path

    def __enter__(self) -> "FingerprintTransaction":
        return self

    def skip(self, reason: str) -> None:
        """Suppress persistence for an intentional non-mutating path."""

        self._skipped = True
        self._skip_reason = reason
        logger.info(
            "FingerprintTransaction.skip for %s/%s (%s): %s",
            self._basename,
            self._language,
            self._operation,
            reason,
        )

    def set_include_deps_override(self, deps: Dict[str, str]) -> None:
        """Preserve a dependency graph captured before a prompt rewrite."""

        self._include_deps_override = dict(deps)

    def _error(self, cause: Any) -> FingerprintFinalizeError:
        return FingerprintFinalizeError(
            f"[{self._operation}] fingerprint finalization failed for "
            f"{self._fingerprint_path}: {cause}"
        )

    def _build_payload(self) -> Dict[str, Any]:
        """Build and validate the canonical serialized fingerprint payload."""

        previous = read_fingerprint(
            self._basename,
            self._language,
            paths=self._paths,
        )
        stored_deps = previous.include_deps if previous else None
        # Sync captures includes before auto-deps can strip them. Use that
        # graph for hashing as well as persistence when it is supplied.
        hash_deps = (
            self._include_deps_override
            if self._include_deps_override is not None
            else stored_deps
        )
        current_hashes = calculate_current_hashes(
            self._paths,
            stored_include_deps=hash_deps,
        )
        if current_hashes.get("prompt_hash") is None:
            raise self._error("prompt_hash is null")

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

    def prepare(self) -> Dict[str, Any]:
        """Return a validated payload for a surrounding atomic state commit."""

        try:
            return self._build_payload()
        except FingerprintFinalizeError:
            raise
        except Exception as exc:
            raise self._error(exc) from exc

    def _commit(self) -> None:
        tmp_path: Optional[str] = None
        try:
            payload = self._build_payload()
            self._fingerprint_path.parent.mkdir(parents=True, exist_ok=True)
            fd, tmp_path = tempfile.mkstemp(
                dir=self._fingerprint_path.parent,
                prefix=f".{self._fingerprint_path.stem}_",
                suffix=".tmp",
            )
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                json.dump(payload, handle, indent=2)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(tmp_path, self._fingerprint_path)
            tmp_path = None
        except FingerprintFinalizeError:
            raise
        except Exception as exc:
            raise self._error(exc) from exc
        finally:
            if tmp_path is not None:
                try:
                    os.unlink(tmp_path)
                except OSError:
                    pass

    def __exit__(self, exc_type, exc_val, exc_tb) -> bool:
        if exc_type is not None:
            return False
        if self._skipped:
            logger.debug(
                "Fingerprint commit suppressed for %s/%s: %s",
                self._basename,
                self._language,
                self._skip_reason,
            )
            return False
        self._commit()
        return False


__all__ = ["FingerprintFinalizeError", "FingerprintTransaction"]
