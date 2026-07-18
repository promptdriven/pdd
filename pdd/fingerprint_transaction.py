"""Shared, failure-safe finalization for legacy fingerprint state."""
from __future__ import annotations

from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

from . import __version__
from .json_atomic import atomic_write_json
from .sync_determine_operation import (
    Fingerprint,
    calculate_current_hashes,
    get_pdd_file_paths,
    read_fingerprint,
)


class FingerprintFinalizeError(RuntimeError):
    """A mutation could not durably record its canonical fingerprint."""

    def __init__(self, operation: str, fingerprint_path: Path, cause: object):
        self.operation = operation
        self.fingerprint_path = Path(fingerprint_path)
        self.cause = cause
        super().__init__(
            f"[{operation}] fingerprint finalization failed for "
            f"{fingerprint_path}: {cause}"
        )


def _coerce_paths(paths: Mapping[str, Any]) -> dict[str, Any]:
    """Normalize explicit path hints without changing their selected root."""
    normalized: dict[str, Any] = {}
    for key, value in paths.items():
        if key == "test_files":
            normalized[key] = [] if value is None else [Path(item) for item in value]
        elif value is None or isinstance(value, Path):
            normalized[key] = value
        else:
            normalized[key] = Path(value)
    return normalized


class FingerprintTransaction:
    """Build and persist one complete fingerprint only after successful work."""

    def __init__(
        self, basename: str, language: str, operation: str,
        paths: Mapping[str, Any] | None = None, cost: float = 0.0,
        model: str = "unknown", *, atomic_state: Any = None,
        include_deps_override: dict[str, str] | None = None,
    ) -> None:
        from .operation_log import get_fingerprint_path

        self.basename, self.language, self.operation = basename, language.lower(), operation
        self.cost, self.model = float(cost or 0.0), model
        self.atomic_state = atomic_state
        self.include_deps_override = include_deps_override
        fallback = Path(".pdd/meta") / f"{basename.replace('/', '_')}_{self.language}.json"
        try:
            resolved = paths if paths else get_pdd_file_paths(basename, self.language)
            self.paths = _coerce_paths(resolved)
            self.fingerprint_path = get_fingerprint_path(
                basename, self.language, paths=self.paths
            )
        except Exception as exc:
            raise FingerprintFinalizeError(operation, fallback, f"path resolution failed: {exc}") from exc

    def _validate_hashes(self, hashes: Mapping[str, Any]) -> None:
        if hashes.get("prompt_hash") is None:
            raise FingerprintFinalizeError(self.operation, self.fingerprint_path, "prompt_hash is null")
        for artifact in ("code", "example", "test"):
            path = self.paths.get(artifact)
            if isinstance(path, Path) and path.exists() and hashes.get(f"{artifact}_hash") is None:
                raise FingerprintFinalizeError(
                    self.operation, self.fingerprint_path,
                    f"{artifact}_hash is null for existing path {path}",
                )
        test_hashes = hashes.get("test_files") or {}
        for path in self.paths.get("test_files") or []:
            if isinstance(path, Path) and path.exists() and test_hashes.get(path.name) is None:
                raise FingerprintFinalizeError(
                    self.operation, self.fingerprint_path,
                    f"test_files hash is null for existing path {path}",
                )

    def payload(self) -> dict[str, Any]:
        previous = read_fingerprint(self.basename, self.language, paths=self.paths)
        stored_deps = self.include_deps_override if self.include_deps_override is not None else (
            previous.include_deps if previous else None
        )
        hashes = calculate_current_hashes(self.paths, stored_include_deps=stored_deps)
        self._validate_hashes(hashes)
        if self.include_deps_override is not None:
            hashes["include_deps"] = self.include_deps_override
        return asdict(Fingerprint(
            pdd_version=__version__, timestamp=datetime.now(timezone.utc).isoformat(),
            command=self.operation, prompt_hash=hashes.get("prompt_hash"),
            code_hash=hashes.get("code_hash"), example_hash=hashes.get("example_hash"),
            test_hash=hashes.get("test_hash"), test_files=hashes.get("test_files"),
            include_deps=hashes.get("include_deps"),
        ))

    def commit(self) -> None:
        try:
            payload = self.payload()
            if self.atomic_state is None:
                atomic_write_json(self.fingerprint_path, payload)
            else:
                setter = getattr(self.atomic_state, "set_fingerprint", None)
                if not callable(setter):
                    raise TypeError("atomic_state does not provide set_fingerprint()")
                try:
                    setter(payload, self.fingerprint_path, operation=self.operation)
                except TypeError:
                    # Older buffered callers use the two-argument protocol.
                    setter(payload, self.fingerprint_path)
        except FingerprintFinalizeError:
            raise
        except Exception as exc:
            raise FingerprintFinalizeError(self.operation, self.fingerprint_path, exc) from exc


def finalize_fingerprint(*args: Any, **kwargs: Any) -> None:
    """Public thin delegate used by every legacy fingerprint success path."""
    FingerprintTransaction(*args, **kwargs).commit()
