"""Shared, failure-safe finalization for legacy fingerprint state."""
from __future__ import annotations

from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import stat
import tempfile
import threading
from typing import Any, Mapping

from . import __version__
from .json_atomic import atomic_write_json, fsync_directory
from .sync_determine_operation import (
    Fingerprint,
    calculate_current_hashes,
    get_pdd_file_paths,
    read_fingerprint,
)

try:  # Keep module importable on Windows; locking is selected at runtime.
    import fcntl  # type: ignore
except ImportError:  # pragma: no cover - Windows fallback is exercised there.
    fcntl = None
    import msvcrt  # type: ignore


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


_LOCK_CONTEXT = threading.local()
_MAX_STATE_BYTES = 8 * 1024 * 1024
_MAX_JOURNAL_BYTES = 64 * 1024
_COPY_CHUNK_BYTES = 1024 * 1024
_RUN_REPORT_INVALIDATING_OPERATIONS = frozenset({
    "auto-deps", "crash", "example", "fix", "generate", "metadata_sync", "update",
})


def operation_invalidates_run_report(operation: str) -> bool:
    """Return whether this completed operation changes artifact evidence.

    Verification and test operations can create or retain an authoritative run
    report; merely publishing a fingerprint for them must never tombstone that
    evidence. Mutation callers opt in through this explicit policy rather than
    relying on the buffered transaction's incidental pending state.
    """
    return operation.strip().lower() in _RUN_REPORT_INVALIDATING_OPERATIONS


@dataclass
class PendingStateUpdate:
    """The two state records coupled by a sync operation."""

    run_report: dict[str, Any] | None = None
    fingerprint: dict[str, Any] | None = None
    run_report_path: Path | None = None
    fingerprint_path: Path | None = None
    remove_run_report: bool = False


class AtomicStateUpdate:
    """Journaled, locked commit protocol for a run report and fingerprint.

    Two ``rename(2)`` calls cannot themselves be atomic.  This protocol records
    durable staged files and hard-link backups before publishing either target.
    A later process recovers an interrupted transaction under the same lock,
    restoring the old pair before any caller can observe it as authoritative.
    The journal has a fixed, two-record shape; payload bytes stay in staged files
    rather than being copied into an unbounded JSON journal.
    """

    def __init__(self, basename: str, language: str, directory: Path | None = None):
        self.basename = basename
        self.language = language.lower()
        self.pending = PendingStateUpdate()
        self._lock_handle: Any = None
        self._journal_path: Path | None = None
        # Keep a lexical absolute path. ``resolve`` follows symlinks and would
        # turn a state target escape into an apparently valid metadata path.
        self._directory = self._absolute(directory) if directory is not None else None

    @staticmethod
    def _absolute(path: Path | str) -> Path:
        return Path(os.path.abspath(os.fspath(path)))

    @staticmethod
    def _file_identity(path: Path) -> tuple[int, int, int] | None:
        """Return a regular, unaliased file identity without following links."""
        try:
            info = os.lstat(path)
        except FileNotFoundError:
            return None
        if stat.S_ISLNK(info.st_mode):
            raise ValueError(f"symlinked state path is not permitted: {path}")
        if not stat.S_ISREG(info.st_mode):
            raise ValueError(f"state path is not a regular file: {path}")
        if info.st_nlink != 1:
            raise ValueError(f"state path has hard-link aliases: {path}")
        return info.st_dev, info.st_ino, info.st_size

    @classmethod
    def _safe_directory(cls, directory: Path) -> Path:
        """Create a metadata directory while rejecting every symlink component."""
        directory = cls._absolute(directory)
        current = Path(directory.anchor)
        for part in directory.parts[1:]:
            current /= part
            try:
                info = os.lstat(current)
            except FileNotFoundError:
                current.mkdir()
                info = os.lstat(current)
            if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
                raise ValueError(f"unsafe metadata directory component: {current}")
        return directory

    def _safe_basename(self) -> str:
        parts = self.basename.replace("\\", "/").split("/")
        if not parts or any(part in {"", ".", ".."} for part in parts):
            raise ValueError("invalid state transaction basename")
        if not self.language or any(character in "/\\\x00" for character in self.language):
            raise ValueError("invalid state transaction language")
        return "_".join(parts)

    def _expected_targets(self, directory: Path) -> dict[str, Path]:
        name = self._safe_basename()
        return {
            "run_report": directory / f"{name}_{self.language}_run.json",
            "fingerprint": directory / f"{name}_{self.language}.json",
        }

    @classmethod
    def _lock_path_for(cls, directory: Path) -> Path:
        """Return a private, stable OS lock path without polluting metadata.

        Keeping a flock inode in ``.pdd/meta`` makes an otherwise rolled-back
        command leave an untracked directory behind.  Deleting that inode at
        release is unsafe: a waiter could hold the old inode while a newcomer
        creates and locks a new one.  A per-user private temp directory keeps
        the inode stable for the life of the machine and out of project state.
        """
        root = Path(tempfile.gettempdir()) / f"pdd-state-locks-{os.getuid()}"
        try:
            root.mkdir(mode=0o700, exist_ok=True)
            info = os.lstat(root)
        except OSError as exc:
            raise ValueError(f"cannot create state transaction lock directory: {root}") from exc
        if not stat.S_ISDIR(info.st_mode) or stat.S_ISLNK(info.st_mode) or info.st_uid != os.getuid():
            raise ValueError(f"unsafe state transaction lock directory: {root}")
        directory_key = hashlib.sha256(str(cls._absolute(directory)).encode("utf-8")).hexdigest()[:24]
        return root / f"{directory_key}-{cls.__name__}.lock"

    @staticmethod
    def _assert_identity(path: Path, expected: tuple[int, int, int] | None) -> None:
        actual = AtomicStateUpdate._file_identity(path)
        if actual != expected:
            raise ValueError(f"state target was replaced during transaction: {path}")

    @staticmethod
    def _digest(path: Path | None) -> str | None:
        """Hash a bounded regular file without following a symlink."""
        if path is None:
            return None
        identity = AtomicStateUpdate._file_identity(path)
        if identity is None:
            return None
        if identity[2] > _MAX_STATE_BYTES:
            raise ValueError(f"state record exceeds {_MAX_STATE_BYTES} byte limit: {path}")
        descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
        try:
            info = os.fstat(descriptor)
            if (info.st_dev, info.st_ino, info.st_size) != identity:
                raise ValueError(f"state record was replaced while hashing: {path}")
            digest = hashlib.sha256()
            with os.fdopen(descriptor, "rb", closefd=False) as handle:
                copied = 0
                while chunk := handle.read(_COPY_CHUNK_BYTES):
                    copied += len(chunk)
                    if copied > _MAX_STATE_BYTES:
                        raise ValueError(f"state record grew while hashing: {path}")
                    digest.update(chunk)
            AtomicStateUpdate._assert_identity(path, identity)
            return digest.hexdigest()
        finally:
            os.close(descriptor)

    @property
    def _identity(self) -> str:
        raw = f"{self.basename}\0{self.language}".encode("utf-8")
        return hashlib.sha256(raw).hexdigest()[:24]

    def __enter__(self) -> "AtomicStateUpdate":
        if self._directory is not None:
            self._lock_and_recover(self._directory)
        return self

    @classmethod
    def recover(cls, basename: str, language: str, directory: Path) -> None:
        """Recover an interrupted transaction before a new command reads state."""
        directory = cls._absolute(directory)
        probe = cls(basename, language, directory)
        lock_key = (str(directory), probe._identity)
        if lock_key in getattr(_LOCK_CONTEXT, "keys", set()):
            return
        state = cls(basename, language)
        try:
            state._lock_and_recover(directory)
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
        if self.pending.remove_run_report:
            raise ValueError("state transaction cannot write and remove one run report")
        self.pending.run_report = report
        self.pending.run_report_path = Path(path)

    def remove_run_report(self, path: Path) -> None:
        if self.pending.run_report is not None:
            raise ValueError("state transaction cannot write and remove one run report")
        self.pending.remove_run_report = True
        self.pending.run_report_path = Path(path)

    def set_fingerprint(
        self, fingerprint: dict[str, Any], path: Path, *, operation: str | None = None,
    ) -> None:
        self.pending.fingerprint = fingerprint
        self.pending.fingerprint_path = Path(path)

    def _targets(self) -> list[tuple[dict[str, Any] | None, Path]]:
        targets: list[tuple[dict[str, Any] | None, Path]] = []
        if self.pending.run_report_path is not None and (
            self.pending.run_report is not None or self.pending.remove_run_report
        ):
            targets.append((self.pending.run_report, self._absolute(self.pending.run_report_path)))
        if self.pending.fingerprint is not None and self.pending.fingerprint_path is not None:
            targets.append((self.pending.fingerprint, self._absolute(self.pending.fingerprint_path)))
        paths = [path for _payload, path in targets]
        if not paths:
            return targets
        if len(set(paths)) != len(paths):
            raise ValueError("state transaction has duplicate targets")
        if len({path.parent for path in paths}) > 1:
            raise ValueError("state transaction targets must share one metadata directory")
        directory = self._safe_directory(paths[0].parent)
        if self._directory is not None and directory != self._directory:
            raise ValueError("state transaction target directory differs from held lock directory")
        expected = self._expected_targets(directory)
        roles: list[str] = []
        for _payload, target in targets:
            role = next((key for key, value in expected.items() if value == target), None)
            if role is None or role in roles:
                raise ValueError("state transaction target has invalid identity or role")
            self._file_identity(target)
            roles.append(role)
        if len(roles) == 2 and roles != ["run_report", "fingerprint"]:
            raise ValueError("state transaction targets have invalid role order")
        return targets

    def _lock_and_recover(self, directory: Path) -> None:
        if self._lock_handle is not None:
            if self._directory != self._absolute(directory):
                raise ValueError("state transaction attempted to reuse a different metadata lock")
            return
        directory = self._safe_directory(directory)
        if self._directory is not None and self._directory != directory:
            raise ValueError("state transaction lock directory differs from requested directory")
        self._directory = directory
        self._journal_path = directory / f".{self._identity}.state-txn.json"
        lock_base = self._lock_path_for(directory)
        lock_path = lock_base.with_name(f"{lock_base.stem}-{self._identity}.lock")
        self._file_identity(lock_path)
        flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0)
        descriptor = os.open(lock_path, flags, 0o600)
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            os.close(descriptor)
            raise ValueError(f"unsafe state transaction lock: {lock_path}")
        self._lock_handle = os.fdopen(descriptor, "a+", encoding="utf-8")
        if fcntl is not None:
            fcntl.flock(self._lock_handle.fileno(), fcntl.LOCK_EX)
        else:  # pragma: no cover - Windows only
            msvcrt.locking(self._lock_handle.fileno(), msvcrt.LK_LOCK, 1)
        keys = getattr(_LOCK_CONTEXT, "keys", set())
        _LOCK_CONTEXT.keys = {*keys, (str(directory), self._identity)}
        states = getattr(_LOCK_CONTEXT, "states", {})
        _LOCK_CONTEXT.states = {
            **states, (str(directory), self._identity): self,
        }
        self._recover_locked()

    def _release_lock(self) -> None:
        if self._lock_handle is None:
            return
        try:
            if fcntl is not None:
                fcntl.flock(self._lock_handle.fileno(), fcntl.LOCK_UN)
            else:  # pragma: no cover - Windows only
                msvcrt.locking(self._lock_handle.fileno(), msvcrt.LK_UNLCK, 1)
        finally:
            if self._journal_path is not None:
                keys = getattr(_LOCK_CONTEXT, "keys", set())
                _LOCK_CONTEXT.keys = keys - {
                    (str(self._journal_path.parent), self._identity)
                }
                states = getattr(_LOCK_CONTEXT, "states", {})
                states = dict(states)
                states.pop((str(self._journal_path.parent), self._identity), None)
                _LOCK_CONTEXT.states = states
            self._lock_handle.close()
            self._lock_handle = None

    @staticmethod
    def _encoded_payload(payload: dict[str, Any]) -> bytes:
        encoded = (json.dumps(payload, indent=2, ensure_ascii=False, default=str) + "\n").encode("utf-8")
        if len(encoded) > _MAX_STATE_BYTES:
            raise ValueError(f"new state payload exceeds {_MAX_STATE_BYTES} byte limit")
        return encoded

    @staticmethod
    def _write_staged(directory: Path, target: Path, payload: dict[str, Any]) -> Path:
        encoded = AtomicStateUpdate._encoded_payload(payload)
        fd, temporary = tempfile.mkstemp(
            dir=directory, prefix=f".{target.name}.", suffix=".state-new",
        )
        temporary_path = Path(temporary)
        try:
            with os.fdopen(fd, "wb") as handle:
                written = 0
                view = memoryview(encoded)
                while written < len(encoded):
                    count = handle.write(view[written:])
                    if count is None or count <= 0:
                        raise OSError("short state staged write")
                    written += count
                handle.flush()
                os.fsync(handle.fileno())
            AtomicStateUpdate._file_identity(temporary_path)
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
        identity = AtomicStateUpdate._file_identity(target)
        if identity is None:
            return None
        if identity[2] > _MAX_STATE_BYTES:
            raise ValueError(f"state target exceeds {_MAX_STATE_BYTES} byte limit: {target}")
        fd, temporary = tempfile.mkstemp(
            dir=target.parent, prefix=f".{target.name}.", suffix=".state-old",
        )
        backup = Path(temporary)
        try:
            source_fd = os.open(target, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
            source_info = os.fstat(source_fd)
            if (source_info.st_dev, source_info.st_ino, source_info.st_size) != identity:
                os.close(source_fd)
                raise ValueError(f"state target was replaced during backup: {target}")
            with os.fdopen(fd, "wb") as handle, os.fdopen(source_fd, "rb") as source:
                copied = 0
                while chunk := source.read(_COPY_CHUNK_BYTES):
                    copied += len(chunk)
                    if copied > _MAX_STATE_BYTES:
                        raise ValueError(f"state target grew beyond {_MAX_STATE_BYTES} bytes: {target}")
                    if handle.write(chunk) != len(chunk):
                        raise OSError("short state backup write")
                handle.flush()
                os.fsync(handle.fileno())
            AtomicStateUpdate._assert_identity(target, identity)
            AtomicStateUpdate._file_identity(backup)
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
        self._file_identity(self._journal_path)
        journal_records = [
            {key: value for key, value in record.items() if not key.startswith("_")}
            for record in records
        ]
        atomic_write_json(
            self._journal_path,
            {"version": 3, "identity": self._identity, "state": state, "records": journal_records},
        )
        self._file_identity(self._journal_path)

    def _validated_records(self, journal: object) -> tuple[str, list[dict[str, Any]]]:
        """Validate untrusted journal data before any filesystem mutation."""
        if not isinstance(journal, dict) or set(journal) != {"version", "identity", "state", "records"}:
            raise ValueError("invalid state transaction journal schema")
        state = journal.get("state")
        records = journal.get("records")
        version = journal.get("version")
        if version not in {2, 3} or journal.get("identity") != self._identity:
            raise ValueError("state transaction journal identity mismatch")
        if state not in {"prepared", "publishing", "report_published", "committed"}:
            raise ValueError("invalid state transaction state")
        if not isinstance(records, list) or len(records) not in {1, 2}:
            raise ValueError("invalid state transaction record count")
        if self._journal_path is None:
            raise RuntimeError("transaction journal is not initialized")
        directory = self._safe_directory(self._journal_path.parent)
        expected = self._expected_targets(directory)
        seen: set[str] = set()
        validated: list[dict[str, Any]] = []
        for record in records:
            expected_keys = {"role", "target", "staged", "backup"}
            if version == 3:
                expected_keys |= {"target_hash", "staged_hash"}
            if not isinstance(record, dict) or set(record) != expected_keys:
                raise ValueError("invalid state transaction record schema")
            role = record.get("role")
            if role not in expected or role in seen:
                raise ValueError("invalid state transaction record role")
            seen.add(role)
            target = self._absolute(record["target"])
            staged_raw = record["staged"]
            staged = Path(staged_raw) if staged_raw is not None else None
            backup_raw = record["backup"]
            backup = Path(backup_raw) if backup_raw is not None else None
            if target != expected[role] or target.parent != directory:
                raise ValueError("transaction target escapes metadata directory")
            if staged is None and role != "run_report":
                raise ValueError("only run reports may be removed transactionally")
            if version == 3:
                for key in ("target_hash", "staged_hash"):
                    value = record[key]
                    if value is not None and (
                        not isinstance(value, str) or len(value) != 64
                    ):
                        raise ValueError("invalid state transaction digest")
            for candidate, suffix in ((staged, ".state-new"), (backup, ".state-old")):
                if candidate is None:
                    continue
                if not candidate.is_absolute() or candidate.parent != directory or not candidate.name.startswith(f".{target.name}.") or not candidate.name.endswith(suffix):
                    raise ValueError("transaction artifact escapes metadata directory")
                self._file_identity(candidate)
            validated.append({
                "role": role, "target": str(target),
                "staged": str(staged) if staged else None,
                "backup": str(backup) if backup else None,
                "target_hash": record.get("target_hash"),
                "staged_hash": record.get("staged_hash"),
            })
        if len(records) == 2 and [record["role"] for record in validated] != ["run_report", "fingerprint"]:
            raise ValueError("transaction records have invalid order")
        return state, validated

    @staticmethod
    def _unlink_if_present(path: Path | None) -> None:
        if path is not None and AtomicStateUpdate._file_identity(path) is not None:
            path.unlink()

    @staticmethod
    def _restore_backup(backup: Path, target: Path) -> None:
        """Restore without consuming the backup, so recovery itself is restartable."""
        identity = AtomicStateUpdate._file_identity(backup)
        if identity is None:
            raise FileNotFoundError(f"missing state backup: {backup}")
        if identity[2] > _MAX_STATE_BYTES:
            raise ValueError(f"state backup exceeds {_MAX_STATE_BYTES} byte limit: {backup}")
        fd, temporary = tempfile.mkstemp(
            dir=target.parent, prefix=f".{target.name}.", suffix=".state-restore",
        )
        temporary_path = Path(temporary)
        try:
            source_fd = os.open(backup, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
            source_info = os.fstat(source_fd)
            if (source_info.st_dev, source_info.st_ino, source_info.st_size) != identity:
                os.close(source_fd)
                raise ValueError(f"state backup was replaced during recovery: {backup}")
            with os.fdopen(fd, "wb") as destination, os.fdopen(source_fd, "rb") as source:
                copied = 0
                while chunk := source.read(_COPY_CHUNK_BYTES):
                    copied += len(chunk)
                    if copied > _MAX_STATE_BYTES:
                        raise ValueError(f"state backup grew beyond {_MAX_STATE_BYTES} bytes: {backup}")
                    if destination.write(chunk) != len(chunk):
                        raise OSError("short state restore write")
                destination.flush()
                os.fsync(destination.fileno())
            AtomicStateUpdate._assert_identity(backup, identity)
            AtomicStateUpdate._file_identity(temporary_path)
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
            journal_identity = self._file_identity(self._journal_path)
            if journal_identity is None:
                return
            if journal_identity[2] > _MAX_JOURNAL_BYTES:
                raise ValueError("oversized state transaction journal")
            descriptor = os.open(self._journal_path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
            with os.fdopen(descriptor, "rb") as handle:
                raw = handle.read(_MAX_JOURNAL_BYTES + 1)
            self._assert_identity(self._journal_path, journal_identity)
            if len(raw) > _MAX_JOURNAL_BYTES:
                raise ValueError("oversized state transaction journal")
            journal = json.loads(raw.decode("utf-8"))
            state, records = self._validated_records(journal)
            if state != "committed":
                for record in records:
                    target = Path(record["target"])
                    # A pre-commit target may be either the original bytes or
                    # the staged bytes (a crash can occur just after rename and
                    # before the next journal transition). Any third value is
                    # a replacement race and must not be overwritten by
                    # recovery. Version-2 journals predate this evidence and
                    # remain readable only for branch migration.
                    expected_hashes = {
                        value for value in (record.get("target_hash"), record.get("staged_hash"))
                        if value is not None
                    }
                    actual_hash = self._digest(target)
                    if expected_hashes and actual_hash not in expected_hashes and not (
                        record.get("staged") is None and actual_hash is None
                    ):
                        raise ValueError(f"state target was replaced before recovery: {target}")
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
                total_payload = sum(
                    len(self._encoded_payload(payload))
                    for payload, _target in targets
                    if payload is not None
                )
                if total_payload > _MAX_STATE_BYTES:
                    raise ValueError(
                        f"aggregate new state payload exceeds {_MAX_STATE_BYTES} byte limit"
                    )
                for payload, target in targets:
                    staged = self._atomic_write(payload, target) if payload is not None else None
                    role = next(
                        role_name for role_name, expected in self._expected_targets(directory).items()
                        if expected == target
                    )
                    record = {
                        "role": role,
                        "target": str(target),
                        "staged": str(staged) if staged else None,
                        "backup": None,
                        "_target_identity": self._file_identity(target),
                        "_staged_identity": self._file_identity(staged) if staged else None,
                        "target_hash": self._digest(target),
                        "staged_hash": self._digest(staged) if staged else None,
                    }
                    records.append(record)
                    backup = self._backup_target(target)
                    record["backup"] = str(backup) if backup else None
                    record["_backup_identity"] = self._file_identity(backup) if backup else None
            except Exception:
                for record in records:
                    self._unlink_if_present(Path(record["staged"]) if record["staged"] else None)
                    self._unlink_if_present(
                        Path(record["backup"]) if record["backup"] else None
                    )
                raise
            try:
                self._write_journal("prepared", records)
                self._write_journal("publishing", records)
                committed = False
                for index, record in enumerate(records):
                    target = Path(record["target"])
                    if record["staged"] is None:
                        self._assert_identity(target, record["_target_identity"])
                        self._unlink_if_present(target)
                    else:
                        staged = Path(record["staged"])
                        self._assert_identity(target, record["_target_identity"])
                        self._assert_identity(staged, record["_staged_identity"])
                        os.replace(staged, target)
                    fsync_directory(target.parent)
                    phase = "committed" if index == len(records) - 1 else "report_published"
                    self._write_journal(phase, records)
                    committed = committed or phase == "committed"
                try:
                    self._cleanup_records(records)
                except Exception:
                    # ``committed`` is the durable commit point. Cleanup is
                    # restartable bookkeeping, not permission to repeat the
                    # already-successful mutation. Retry once under the lock;
                    # if it still fails the committed journal directs startup
                    # to cleanup rather than rollback.
                    if not committed:
                        raise
                    try:
                        self._cleanup_records(records)
                    except Exception:
                        pass
                    return
            except Exception as publish_error:
                # A journal that reached disk is itself the recovery authority.
                # Recover immediately while this process still owns the lock; a
                # caller must never receive a publish failure beside split state.
                if self._journal_path is None or not self._journal_path.exists():
                    for record in records:
                        self._unlink_if_present(
                            Path(record["staged"]) if record.get("staged") else None
                        )
                        self._unlink_if_present(
                            Path(record["backup"]) if record["backup"] else None
                        )
                else:
                    try:
                        self._recover_locked()
                    except Exception as recovery_error:
                        raise RuntimeError(
                            f"publish failed: {publish_error}; recovery failed: {recovery_error}"
                        ) from recovery_error
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
            if value is None:
                normalized[key] = []
            elif isinstance(value, (str, Path)):
                normalized[key] = [Path(value)]
            else:
                normalized[key] = [Path(item) for item in value]
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
    governing_root = next(
        (candidate for candidate in (prompt_path.parent, *prompt_path.parents)
         if (candidate / ".pddrc").is_file()),
        prompts_root.parent,
    ).resolve()

    def canonical_names(key: str) -> set[str]:
        """Names are an identity boundary even when legacy discovery is absent."""
        discovered = resolved.get(key)
        values = discovered if key == "test_files" else [discovered]
        names = {Path(item).name for item in values or [] if item is not None}
        if names:
            return names
        leaf = basename.replace("\\", "/").split("/")[-1]
        try:
            from .sync_determine_operation import get_extension
            suffix = get_extension(language)
            suffix = suffix if suffix.startswith(".") else f".{suffix}"
        except Exception:
            suffix = ""
        if key == "code":
            return {f"{leaf}{suffix}"}
        if key == "example":
            return {f"{leaf}_example{suffix}"}
        if key in {"test", "test_files"}:
            return {f"test_{leaf}{suffix}"}
        return set()

    def validate_owned(key: str, value: Any) -> None:
        values = value if key == "test_files" else [value]
        for item in values:
            if item is None:
                continue
            raw = Path(item)
            if raw.is_symlink():
                raise ValueError(f"{key} path is a symlink alias: {raw}")
            candidate = Path(item).resolve()
            try:
                candidate.relative_to(governing_root)
            except ValueError as exc:
                raise ValueError(f"{key} path escapes owning project root: {candidate}") from exc
            expected_names = canonical_names(key)
            if expected_names and key != "prompt":
                if key == "test_files":
                    expected_stem = Path(next(iter(expected_names))).stem
                    if not (candidate.stem == expected_stem or candidate.stem.startswith(f"{expected_stem}_")):
                        raise ValueError(f"{key} path has wrong module identity: {candidate}")
                elif candidate.name not in expected_names:
                    raise ValueError(f"{key} path has wrong module identity: {candidate}")

    for key, value in explicit.items():
        if value is not None and not (key == "test_files" and not value):
            validate_owned(key, value)
    # An explicit path is an override only for the same canonical artifact.
    # When configuration can resolve the role inside this project, accepting a
    # different same-root file would write module A's fingerprint over module
    # B's contents.  Ignore cross-root legacy discovery here; it is filtered as
    # advisory data below and cannot define this unit's identity.
    for key, value in explicit.items():
        if key == "prompt" or value is None or (key == "test_files" and not value):
            continue
        discovered = resolved.get(key)
        if discovered is None or (key == "test_files" and not discovered):
            continue
        try:
            validate_owned(key, discovered)
        except ValueError:
            continue
        supplied_values = value if key == "test_files" else [value]
        discovered_values = discovered if key == "test_files" else [discovered]
        # A configured path that does not exist is advisory only.  A real
        # explicit artifact with the canonical role/name may legitimately
        # be the configured non-default output; only two existing,
        # conflicting files establish an ownership conflict.
        if all(Path(item).exists() for item in supplied_values) and all(
            Path(item).exists() for item in discovered_values
        ) and {Path(item).resolve() for item in supplied_values} != {
            Path(item).resolve() for item in discovered_values
        }:
            raise ValueError(f"{key} path conflicts with canonical unit identity")
    # Explicit real paths can override configured outputs, but optional null or
    # empty hints are absence of information, never an instruction to erase a
    # discovered existing artifact.
    for key, value in explicit.items():
        if key == "prompt":
            continue
        if value is None or (key == "test_files" and not value):
            continue
        resolved[key] = value
    resolved["prompt"] = prompt_path

    # Discovery is advisory until it has been proven to belong to the prompt's
    # project.  This matters when a command is launched from a parent checkout:
    # legacy discovery can otherwise return that checkout's default example or
    # test path.  Never hash such an unrelated optional artifact.  Conversely,
    # a real caller-supplied artifact has already been rejected above rather
    # than being silently discarded.
    for key, value in tuple(resolved.items()):
        if key == "prompt" or value is None:
            continue
        try:
            validate_owned(key, value)
        except ValueError:
            if key in explicit and explicit[key] is not None and not (
                key == "test_files" and not explicit[key]
            ):
                raise
            resolved[key] = [] if key == "test_files" else None
    test_files = resolved.get("test_files") or []
    names = [Path(path).name for path in test_files]
    if len(names) != len(set(names)):
        raise ValueError("duplicate test filenames in canonical artifact set")
    identities: dict[tuple[int, int], str] = {}
    for key, value in resolved.items():
        values = value if key == "test_files" else [value]
        for item in values or []:
            if item is None:
                continue
            path = Path(item)
            if path.is_symlink():
                raise ValueError(f"{key} path is a symlink alias: {path}")
            try:
                info = path.stat()
            except FileNotFoundError:
                continue
            identity = (info.st_dev, info.st_ino)
            previous = identities.get(identity)
            if previous is not None and previous != key and {previous, key} != {"test", "test_files"}:
                raise ValueError(f"{key} path aliases {previous} artifact")
            identities[identity] = key
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
        self._supplied_paths = dict(paths or {})
        self._paths_complete = False
        fallback = Path(".pdd/meta") / f"{basename.replace('/', '_')}_{self.language}.json"
        try:
            # This is deliberately only a locking hint.  Completion may read
            # project configuration and must happen under that lock below.
            self.paths = _coerce_paths(self._supplied_paths)
            self.fingerprint_path = get_fingerprint_path(
                basename, self.language, paths=self.paths
            )
        except Exception as exc:
            raise FingerprintFinalizeError(operation, fallback, f"path resolution failed: {exc}") from exc

    def _complete_paths_under_lock(self) -> None:
        """Resolve the canonical source set while holding the unit lock."""
        if self._paths_complete:
            return
        from .operation_log import get_fingerprint_path
        try:
            paths = _canonical_paths(self.basename, self.language, self._supplied_paths)
            fingerprint_path = get_fingerprint_path(
                self.basename, self.language, paths=paths
            )
            if fingerprint_path.parent.resolve() != self.fingerprint_path.parent.resolve():
                raise ValueError(
                    "canonical paths resolved to a different metadata project than the lock"
                )
            self.paths = paths
            self.fingerprint_path = fingerprint_path
            self._paths_complete = True
        except FingerprintFinalizeError:
            raise
        except Exception as exc:
            raise FingerprintFinalizeError(
                self.operation, self.fingerprint_path, f"path resolution failed: {exc}"
            ) from exc

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
        self._complete_paths_under_lock()
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
            active_state = getattr(_LOCK_CONTEXT, "states", {}).get(
                (str(AtomicStateUpdate._absolute(self.fingerprint_path.parent)),
                 AtomicStateUpdate(self.basename, self.language)._identity)
            )
            state_to_use = self.atomic_state or active_state
            if state_to_use is None:
                # Hashing, prior-state reads, recovery, and publication share
                # one per-unit critical section so an older snapshot cannot win
                # after a newer finalizer has already completed.
                state = AtomicStateUpdate(self.basename, self.language)
                state._lock_and_recover(self.fingerprint_path.parent)
                try:
                    payload = self.payload()
                    state.set_fingerprint(payload, self.fingerprint_path)
                    state._commit()
                finally:
                    state._release_lock()
            else:
                setter = getattr(state_to_use, "set_fingerprint", None)
                if not callable(setter):
                    raise TypeError("atomic_state does not provide set_fingerprint()")
                # Paired sync/pin callers must hold this same lock while
                # resolving, hashing, and buffering their fingerprint. The
                # enclosing AtomicStateUpdate releases it only after paired
                # publication, preventing stale last-writer-wins snapshots.
                locker = getattr(state_to_use, "_lock_and_recover", None)
                if not callable(locker):
                    raise TypeError("atomic_state does not provide transaction locking")
                locker(self.fingerprint_path.parent)
                payload = self.payload()
                try:
                    setter(payload, self.fingerprint_path, operation=self.operation)
                except TypeError:
                    # Older buffered callers use the two-argument protocol.
                    setter(payload, self.fingerprint_path)
        except FingerprintFinalizeError:
            raise
        except Exception as exc:
            raise FingerprintFinalizeError(self.operation, self.fingerprint_path, exc) from exc


def finalize_fingerprint(
    basename: str, language: str, operation: str,
    paths: Mapping[str, Any] | None = None, cost: float = 0.0,
    model: str = "unknown", *, atomic_state: Any = None,
    include_deps_override: dict[str, str] | None = None,
    remove_run_report: bool = False,
) -> None:
    """Finalize a fingerprint, optionally tombstoning its stale report atomically."""
    transaction = FingerprintTransaction(
        basename, language, operation, paths, cost, model,
        atomic_state=atomic_state, include_deps_override=include_deps_override,
    )
    active_state = getattr(_LOCK_CONTEXT, "states", {}).get(
        (str(AtomicStateUpdate._absolute(transaction.fingerprint_path.parent)),
         AtomicStateUpdate(basename, language)._identity)
    )
    if atomic_state is None and active_state is not None:
        transaction.atomic_state = active_state
        if remove_run_report:
            active_state.remove_run_report(
                transaction.fingerprint_path.with_name(
                    f"{basename.replace('/', '_')}_{language.lower()}_run.json"
                )
            )
        transaction.commit()
        return
    if not remove_run_report:
        transaction.commit()
        return
    if atomic_state is not None:
        atomic_state.remove_run_report(
            transaction.fingerprint_path.with_name(
                f"{basename.replace('/', '_')}_{language.lower()}_run.json"
            )
        )
        transaction.commit()
        return
    with AtomicStateUpdate(
        basename, language, directory=transaction.fingerprint_path.parent
    ) as state:
        state.remove_run_report(
            transaction.fingerprint_path.with_name(
                f"{basename.replace('/', '_')}_{language.lower()}_run.json"
            )
        )
        transaction.atomic_state = state
        transaction.commit()
