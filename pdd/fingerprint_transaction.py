"""Shared, failure-safe finalization for legacy fingerprint state."""
from __future__ import annotations

from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import tempfile
from typing import Any, Mapping

from . import __version__
from .json_atomic import atomic_write_json, fsync_directory
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


@dataclass
class PendingStateUpdate:
    """The two state records coupled by a sync operation."""

    run_report: dict[str, Any] | None = None
    fingerprint: dict[str, Any] | None = None
    run_report_path: Path | None = None
    fingerprint_path: Path | None = None


class AtomicStateUpdate:
    """Journaled, locked commit protocol for a run report and fingerprint.

    Two ``rename(2)`` calls cannot themselves be atomic.  This protocol records
    durable staged files and hard-link backups before publishing either target.
    A later process recovers an interrupted transaction under the same lock,
    restoring the old pair before any caller can observe it as authoritative.
    The journal has a fixed, two-record shape; payload bytes stay in staged files
    rather than being copied into an unbounded JSON journal.
    """

    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language.lower()
        self.pending = PendingStateUpdate()
        self._lock_handle: Any = None
        self._journal_path: Path | None = None

    def __enter__(self) -> "AtomicStateUpdate":
        return self

    @classmethod
    def recover(cls, basename: str, language: str, directory: Path) -> None:
        """Recover an interrupted transaction before a new command reads state."""
        state = cls(basename, language)
        try:
            state._lock_and_recover(Path(directory).resolve())
        finally:
            state._release_lock()

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> bool:
        try:
            if exc_type is None:
                self._commit()
        finally:
            self._release_lock()
        return False

    def set_run_report(self, report: dict[str, Any], path: Path) -> None:
        self.pending.run_report = report
        self.pending.run_report_path = Path(path)

    def set_fingerprint(
        self, fingerprint: dict[str, Any], path: Path, *, operation: str | None = None,
    ) -> None:
        self.pending.fingerprint = fingerprint
        self.pending.fingerprint_path = Path(path)

    def _targets(self) -> list[tuple[dict[str, Any], Path]]:
        targets: list[tuple[dict[str, Any], Path]] = []
        if self.pending.run_report is not None and self.pending.run_report_path is not None:
            targets.append((self.pending.run_report, self.pending.run_report_path.resolve()))
        if self.pending.fingerprint is not None and self.pending.fingerprint_path is not None:
            targets.append((self.pending.fingerprint, self.pending.fingerprint_path.resolve()))
        paths = [path for _payload, path in targets]
        if len(set(paths)) != len(paths):
            raise ValueError("state transaction has duplicate targets")
        if len({path.parent for path in paths}) > 1:
            raise ValueError("state transaction targets must share one metadata directory")
        return targets

    def _lock_and_recover(self, directory: Path) -> None:
        directory.mkdir(parents=True, exist_ok=True)
        self._journal_path = directory / f".{self.basename.replace('/', '_')}_{self.language}.state-txn.json"
        lock_path = directory / f".{self.basename.replace('/', '_')}_{self.language}.state-txn.lock"
        self._lock_handle = open(lock_path, "a+", encoding="utf-8")
        fcntl.flock(self._lock_handle.fileno(), fcntl.LOCK_EX)
        self._recover_locked()

    def _release_lock(self) -> None:
        if self._lock_handle is None:
            return
        try:
            fcntl.flock(self._lock_handle.fileno(), fcntl.LOCK_UN)
        finally:
            self._lock_handle.close()
            self._lock_handle = None

    @staticmethod
    def _write_staged(directory: Path, target: Path, payload: dict[str, Any]) -> Path:
        fd, temporary = tempfile.mkstemp(
            dir=directory, prefix=f".{target.name}.", suffix=".state-new",
        )
        temporary_path = Path(temporary)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                json.dump(payload, handle, indent=2, ensure_ascii=False, default=str)
                handle.write("\n")
                handle.flush()
                os.fsync(handle.fileno())
            return temporary_path
        except BaseException:
            try:
                temporary_path.unlink()
            except OSError:
                pass
            raise

    def _atomic_write(self, data: dict[str, Any], target_path: Path) -> Path:
        """Compatibility hook for state-writer failure injection tests.

        Unlike the retired implementation, this prepares a durable staged file;
        publication remains journal-controlled in :meth:`_commit`.
        """
        return self._write_staged(target_path.parent, target_path, data)

    @staticmethod
    def _backup_target(target: Path) -> Path | None:
        if not target.exists():
            return None
        if target.is_symlink() or not target.is_file():
            raise ValueError(f"unsafe state target: {target}")
        fd, temporary = tempfile.mkstemp(
            dir=target.parent, prefix=f".{target.name}.", suffix=".state-old",
        )
        backup = Path(temporary)
        try:
            with os.fdopen(fd, "wb") as handle, target.open("rb") as source:
                while chunk := source.read(1024 * 1024):
                    handle.write(chunk)
                handle.flush()
                os.fsync(handle.fileno())
            return backup
        except BaseException:
            try:
                backup.unlink()
            except OSError:
                pass
            raise

    def _write_journal(self, state: str, records: list[dict[str, Any]]) -> None:
        if self._journal_path is None:
            raise RuntimeError("transaction journal is not initialized")
        atomic_write_json(
            self._journal_path,
            {"version": 1, "state": state, "records": records},
        )

    @staticmethod
    def _unlink_if_present(path: Path | None) -> None:
        if path is not None and path.exists():
            path.unlink()

    @staticmethod
    def _restore_backup(backup: Path, target: Path) -> None:
        """Restore without consuming the backup, so recovery itself is restartable."""
        fd, temporary = tempfile.mkstemp(
            dir=target.parent, prefix=f".{target.name}.", suffix=".state-restore",
        )
        temporary_path = Path(temporary)
        try:
            with os.fdopen(fd, "wb") as destination, backup.open("rb") as source:
                while chunk := source.read(1024 * 1024):
                    destination.write(chunk)
                destination.flush()
                os.fsync(destination.fileno())
            os.replace(temporary_path, target)
            fsync_directory(target.parent)
        except BaseException:
            try:
                temporary_path.unlink()
            except OSError:
                pass
            raise

    def _cleanup_records(self, records: list[dict[str, Any]]) -> None:
        for record in records:
            for key in ("staged", "backup"):
                value = record.get(key)
                if value:
                    self._unlink_if_present(Path(value))
        if self._journal_path is not None:
            self._unlink_if_present(self._journal_path)
            fsync_directory(self._journal_path.parent)

    def _recover_locked(self) -> None:
        if self._journal_path is None or not self._journal_path.exists():
            return
        try:
            journal = json.loads(self._journal_path.read_text(encoding="utf-8"))
            records = journal["records"]
            state = journal["state"]
            if not isinstance(records, list) or state not in {
                "prepared", "publishing", "report_published", "committed",
            }:
                raise ValueError("invalid state transaction journal")
            if state != "committed":
                for record in records:
                    target = Path(record["target"])
                    backup_value = record.get("backup")
                    if backup_value is None:
                        self._unlink_if_present(target)
                    else:
                        backup = Path(backup_value)
                        if not backup.exists():
                            raise FileNotFoundError(f"missing transaction backup {backup}")
                        self._restore_backup(backup, target)
            self._cleanup_records(records)
        except Exception as exc:
            raise FingerprintFinalizeError(
                "sync", self._journal_path, f"state transaction recovery failed: {exc}",
            ) from exc

    def _commit(self) -> None:
        targets = self._targets()
        if not targets:
            return
        try:
            directory = targets[0][1].parent
            self._lock_and_recover(directory)
            records: list[dict[str, Any]] = []
            try:
                for payload, target in targets:
                    staged = self._atomic_write(payload, target)
                    record = {
                        "target": str(target),
                        "staged": str(staged),
                        "backup": None,
                    }
                    records.append(record)
                    backup = self._backup_target(target)
                    record["backup"] = str(backup) if backup else None
            except Exception:
                for record in records:
                    self._unlink_if_present(Path(record["staged"]))
                    self._unlink_if_present(
                        Path(record["backup"]) if record["backup"] else None
                    )
                raise
            try:
                self._write_journal("prepared", records)
                self._write_journal("publishing", records)
                for index, record in enumerate(records):
                    target = Path(record["target"])
                    os.replace(record["staged"], target)
                    fsync_directory(target.parent)
                    self._write_journal("report_published" if index == 0 else "committed", records)
                self._cleanup_records(records)
            except Exception:
                # A journal that reached disk is itself the recovery authority.
                # If it never appeared, no target was published and cleanup is safe.
                if self._journal_path is None or not self._journal_path.exists():
                    for record in records:
                        self._unlink_if_present(Path(record["staged"]))
                        self._unlink_if_present(
                            Path(record["backup"]) if record["backup"] else None
                        )
                raise
        except FingerprintFinalizeError:
            raise
        except Exception as exc:
            target = self.pending.fingerprint_path or self.pending.run_report_path
            raise FingerprintFinalizeError(
                "sync", target or Path(".pdd/meta"), f"atomic state commit failed: {exc}",
            ) from exc


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


def _canonical_paths(
    basename: str, language: str, supplied: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Resolve the complete unit once, retaining explicit caller paths.

    Thin mutation callers often only know prompt/code.  Persisting those hints
    directly drops existing examples and tests from the fingerprint, so the
    finalizer owns completion of the canonical source set.
    """
    explicit = _coerce_paths(supplied or {})
    prompt = explicit.get("prompt")
    if prompt is None:
        return _coerce_paths(get_pdd_file_paths(basename, language))
    prompt_path = Path(prompt).resolve()
    prompts_root = next(
        (ancestor for ancestor in (prompt_path.parent, *prompt_path.parents)
         if ancestor.name == "prompts"),
        prompt_path.parent,
    )
    resolved = _coerce_paths(
        get_pdd_file_paths(basename, language, prompts_dir=str(prompts_root))
    )
    # Explicit absolute paths are authoritative for output redirections, but
    # never shrink the canonical set discovered from the prompt's own root.
    resolved.update(explicit)
    resolved["prompt"] = prompt_path
    return resolved


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
            self.paths = _canonical_paths(basename, self.language, paths)
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
