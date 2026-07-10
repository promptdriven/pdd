"""Crash-durable multi-file synchronization transactions."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import stat
import tempfile
from contextlib import ExitStack
from dataclasses import dataclass
from enum import Enum
from pathlib import Path, PurePosixPath
from typing import Callable, Optional

from filelock import FileLock

from .durability import fsync_directory
from .path_policy import PathPolicy


class TransactionError(RuntimeError):
    """Raised when a synchronization transaction cannot proceed safely."""


class TransactionConflict(TransactionError):
    """Raised when a destination changes after transaction planning."""


class RecoveryRequired(TransactionError):
    """Raised when a durable COMMITTING transaction must be recovered."""


class TransactionPhase(str, Enum):
    """Durable WAL state controlling deterministic recovery behavior."""

    PREPARED = "PREPARED"
    COMMITTING = "COMMITTING"
    COMMITTED = "COMMITTED"
    ROLLED_BACK = "ROLLED_BACK"


@dataclass(frozen=True)
class FileState:
    """CAS-relevant content, type, and normalized mode for one destination."""

    exists: bool
    digest: str | None
    git_mode: str | None
    file_type: str


@dataclass(frozen=True)
class PlannedWrite:
    """One repository-relative regular-file output in a transaction."""

    relpath: PurePosixPath
    content: bytes
    git_mode: str
    secret: bool = False
    expected: FileState | None = None

    def __post_init__(self) -> None:
        if self.git_mode not in {"100644", "100755"}:
            raise TransactionError("transactions only install regular Git file modes")


@dataclass(frozen=True)
class TransactionResult:
    """Observable completion state for one mutation attempt."""

    transaction_id: str
    phase: TransactionPhase
    changed_paths: tuple[PurePosixPath, ...]
    no_op: bool


def _digest(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def _git_mode(mode: int) -> str:
    executable = stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH
    return "100755" if mode & executable else "100644"


def _file_state(path: Path) -> FileState:
    if not path.exists() and not path.is_symlink():
        return FileState(False, None, None, "missing")
    mode = path.lstat().st_mode
    if stat.S_ISLNK(mode):
        return FileState(True, None, "120000", "symlink")
    if not stat.S_ISREG(mode):
        return FileState(True, None, None, "special")
    content = path.read_bytes()
    return FileState(True, _digest(content), _git_mode(mode), "regular")


def _state_payload(state: FileState) -> dict[str, object]:
    return {
        "exists": state.exists,
        "digest": state.digest,
        "git_mode": state.git_mode,
        "file_type": state.file_type,
    }


def _parse_state(payload: dict[str, object]) -> FileState:
    return FileState(
        bool(payload["exists"]),
        payload.get("digest") if isinstance(payload.get("digest"), str) else None,
        payload.get("git_mode")
        if isinstance(payload.get("git_mode"), str)
        else None,
        str(payload["file_type"]),
    )


class TransactionManager:
    """Prepare, commit, inspect, and recover repository mutation journals."""

    def __init__(self, checkout_root: Path) -> None:
        self.checkout_root = Path(checkout_root).resolve()
        self.policy = PathPolicy(self.checkout_root)
        self.state_root = self.checkout_root / ".pdd/transactions"
        self.lock_root = self.checkout_root / ".pdd/locks/transactions"

    def _ensure_private_directory(self, path: Path) -> None:
        current = self.checkout_root
        for part in path.relative_to(self.checkout_root).parts:
            current = current / part
            if current.exists() or current.is_symlink():
                mode = current.lstat().st_mode
                if stat.S_ISLNK(mode) or not stat.S_ISDIR(mode):
                    raise TransactionError(f"transaction state path is unsafe: {current}")
            else:
                current.mkdir(mode=0o700)
            if current == path:
                os.chmod(current, 0o700)

    def _transaction_dir(self, transaction_id: str) -> Path:
        safe_characters = (
            "-_.0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
        )
        if not transaction_id or any(
            character not in safe_characters for character in transaction_id
        ):
            raise TransactionError("transaction ID contains unsafe characters")
        return self.state_root / transaction_id

    @staticmethod
    def _journal_path(transaction_dir: Path) -> Path:
        return transaction_dir / "journal.json"

    def _write_journal(self, transaction_dir: Path, payload: dict[str, object]) -> None:
        journal_path = self._journal_path(transaction_dir)
        descriptor, temporary_name = tempfile.mkstemp(
            prefix=".journal.", suffix=".tmp", dir=transaction_dir
        )
        temporary = Path(temporary_name)
        try:
            os.fchmod(descriptor, 0o600)
            encoded = json.dumps(payload, sort_keys=True, indent=2).encode() + b"\n"
            with os.fdopen(descriptor, "wb") as handle:
                handle.write(encoded)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, journal_path)
            fsync_directory(transaction_dir)
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise

    def _read_journal(self, transaction_dir: Path) -> dict[str, object]:
        path = self._journal_path(transaction_dir)
        if path.is_symlink() or not path.is_file():
            raise TransactionError(f"transaction journal is missing or unsafe: {path}")
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise TransactionError(f"transaction journal is corrupt: {path}") from exc
        if not isinstance(payload, dict):
            raise TransactionError("transaction journal root must be an object")
        return payload

    def _write_blob(self, path: Path, content: bytes, mode: int = 0o600) -> None:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())

    def _validate_plan(self, writes: tuple[PlannedWrite, ...]) -> None:
        if not writes:
            raise TransactionError("transaction plan must contain at least one write")
        paths = [write.relpath for write in writes]
        if len(paths) != len(set(paths)):
            raise TransactionError("transaction plan contains duplicate destinations")
        if any(write.secret for write in writes):
            raise TransactionError(
                "secret-labeled rollback content requires configured encryption"
            )
        for write in writes:
            self.policy.resolve(write.relpath, allow_missing=True)

    def _available_space_check(self, writes: tuple[PlannedWrite, ...]) -> None:
        required = sum(len(write.content) for write in writes) * 2 + 1024 * 1024
        if shutil.disk_usage(self.checkout_root).free < required:
            raise TransactionError("insufficient space for prepared and rollback state")

    def _entry(
        self,
        transaction_dir: Path,
        index: int,
        write: PlannedWrite,
    ) -> dict[str, object]:
        resolved = self.policy.resolve(write.relpath, allow_missing=True)
        before = _file_state(resolved.canonical_path)
        if write.expected is not None and before != write.expected:
            raise TransactionConflict(
                f"destination changed before prepare: {write.relpath}"
            )
        if before.file_type not in {"missing", "regular"}:
            raise TransactionError(f"destination is not a regular file: {write.relpath}")
        prepared_name = f"prepared-{index}.blob"
        rollback_name = f"rollback-{index}.blob" if before.exists else None
        self._write_blob(transaction_dir / prepared_name, write.content)
        if rollback_name:
            self._write_blob(transaction_dir / rollback_name, resolved.canonical_path.read_bytes())
        return {
            "relpath": write.relpath.as_posix(),
            "desired_digest": _digest(write.content),
            "desired_mode": write.git_mode,
            "precondition": _state_payload(write.expected or before),
            "prepared_blob": prepared_name,
            "rollback_blob": rollback_name,
            "installed": False,
        }

    def prepare(
        self,
        transaction_id: str,
        writes: tuple[PlannedWrite, ...],
        *,
        shared_resources: tuple[PurePosixPath, ...] = (),
    ) -> TransactionResult:
        """Persist prepared outputs and rollback state without changing destinations."""
        self._validate_plan(writes)
        self._available_space_check(writes)
        desired_states = {
            write.relpath: FileState(True, _digest(write.content), write.git_mode, "regular")
            for write in writes
        }
        current_states = {
            write.relpath: _file_state(
                self.policy.resolve(write.relpath, allow_missing=True).canonical_path
            )
            for write in writes
        }
        for write in writes:
            if write.expected is not None and current_states[write.relpath] != write.expected:
                raise TransactionConflict(
                    f"destination changed before prepare: {write.relpath}"
                )
        if current_states == desired_states:
            return TransactionResult(transaction_id, TransactionPhase.COMMITTED, (), True)
        self._ensure_private_directory(self.state_root)
        self._ensure_private_directory(self.lock_root)
        transaction_dir = self._transaction_dir(transaction_id)
        if transaction_dir.exists():
            raise TransactionError(f"transaction already exists: {transaction_id}")
        transaction_dir.mkdir(mode=0o700)
        entries = [self._entry(transaction_dir, index, write) for index, write in enumerate(writes)]
        payload: dict[str, object] = {
            "schema_version": 1,
            "transaction_id": transaction_id,
            "phase": TransactionPhase.PREPARED.value,
            "shared_resources": [path.as_posix() for path in sorted(shared_resources)],
            "entries": entries,
        }
        self._write_journal(transaction_dir, payload)
        fsync_directory(self.state_root)
        return TransactionResult(
            transaction_id,
            TransactionPhase.PREPARED,
            tuple(write.relpath for write in writes),
            False,
        )

    def _locks(self, payload: dict[str, object]) -> ExitStack:
        self._ensure_private_directory(self.lock_root)
        resources = [str(item) for item in payload.get("shared_resources", [])]
        entries = payload.get("entries", [])
        if not isinstance(entries, list):
            raise TransactionError("transaction entries are malformed")
        resources.extend(str(item.get("relpath")) for item in entries if isinstance(item, dict))
        stack = ExitStack()
        for resource in sorted(set(resources)):
            lock_name = hashlib.sha256(resource.encode()).hexdigest() + ".lock"
            stack.enter_context(FileLock(str(self.lock_root / lock_name)))
        return stack

    def _install_entry(
        self,
        transaction_dir: Path,
        entry: dict[str, object],
    ) -> None:
        relpath = PurePosixPath(str(entry["relpath"]))
        resolved = self.policy.resolve(relpath, allow_missing=True)
        current = _file_state(resolved.canonical_path)
        desired = FileState(
            True,
            str(entry["desired_digest"]),
            str(entry["desired_mode"]),
            "regular",
        )
        if current == desired:
            return
        precondition_payload = entry.get("precondition")
        if not isinstance(precondition_payload, dict):
            raise TransactionError("transaction precondition is malformed")
        if current != _parse_state(precondition_payload):
            raise TransactionConflict(f"destination changed: {relpath}")
        resolved.canonical_path.parent.mkdir(parents=True, exist_ok=True)
        prepared = transaction_dir / str(entry["prepared_blob"])
        if prepared.is_symlink() or not prepared.is_file():
            raise TransactionError(f"prepared transaction blob is unsafe: {relpath}")
        content = prepared.read_bytes()
        if _digest(content) != desired.digest:
            raise TransactionError(f"prepared transaction blob is corrupt: {relpath}")
        descriptor, temporary_name = tempfile.mkstemp(
            prefix=f".{resolved.canonical_path.name}.",
            suffix=".pdd-tmp",
            dir=resolved.canonical_path.parent,
        )
        temporary = Path(temporary_name)
        try:
            os.fchmod(descriptor, 0o755 if desired.git_mode == "100755" else 0o644)
            with os.fdopen(descriptor, "wb") as handle:
                handle.write(content)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, resolved.canonical_path)
            fsync_directory(resolved.canonical_path.parent)
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise

    def _validate_prepared_entries(
        self, transaction_dir: Path, entries: list[object]
    ) -> None:
        """Validate the complete prepared set before changing any destination."""
        for item in entries:
            if not isinstance(item, dict):
                raise TransactionError("transaction entry is malformed")
            relpath = PurePosixPath(str(item["relpath"]))
            prepared = transaction_dir / str(item["prepared_blob"])
            if prepared.is_symlink() or not prepared.is_file():
                raise TransactionError(f"prepared transaction blob is unsafe: {relpath}")
            if _digest(prepared.read_bytes()) != str(item["desired_digest"]):
                raise TransactionError(f"prepared transaction blob is corrupt: {relpath}")
            precondition = item.get("precondition")
            if not isinstance(precondition, dict):
                raise TransactionError("transaction precondition is malformed")
            before = _parse_state(precondition)
            rollback_name = item.get("rollback_blob")
            if not before.exists:
                if rollback_name is not None:
                    raise TransactionError(
                        f"unexpected rollback transaction blob: {relpath}"
                    )
                continue
            rollback = transaction_dir / str(rollback_name)
            if rollback.is_symlink() or not rollback.is_file():
                raise TransactionError(f"rollback transaction blob is unsafe: {relpath}")
            if _digest(rollback.read_bytes()) != before.digest:
                raise TransactionError(f"rollback transaction blob is corrupt: {relpath}")

    def _restore_entries(
        self, transaction_dir: Path, entries: list[object]
    ) -> None:
        """Restore every already-installed destination from durable pre-state."""
        for item in reversed(entries):
            if not isinstance(item, dict) or item.get("installed") is not True:
                continue
            relpath = PurePosixPath(str(item["relpath"]))
            destination = self.policy.resolve(relpath, allow_missing=True).canonical_path
            precondition = item.get("precondition")
            if not isinstance(precondition, dict):
                raise TransactionError("transaction rollback precondition is malformed")
            before = _parse_state(precondition)
            rollback_name = item.get("rollback_blob")
            if not before.exists:
                destination.unlink(missing_ok=True)
                fsync_directory(destination.parent)
                continue
            rollback = transaction_dir / str(rollback_name)
            if rollback.is_symlink() or not rollback.is_file():
                raise TransactionError(f"rollback transaction blob is unsafe: {relpath}")
            content = rollback.read_bytes()
            if _digest(content) != before.digest:
                raise TransactionError(f"rollback transaction blob is corrupt: {relpath}")
            descriptor, temporary_name = tempfile.mkstemp(
                prefix=f".{destination.name}.", suffix=".pdd-rollback", dir=destination.parent
            )
            temporary = Path(temporary_name)
            try:
                os.fchmod(descriptor, 0o755 if before.git_mode == "100755" else 0o644)
                with os.fdopen(descriptor, "wb") as handle:
                    handle.write(content)
                    handle.flush()
                    os.fsync(handle.fileno())
                os.replace(temporary, destination)
                fsync_directory(destination.parent)
            except BaseException:
                temporary.unlink(missing_ok=True)
                raise

    def commit(
        self,
        transaction_id: str,
        *,
        crash_hook: Optional[Callable[[str], None]] = None,
    ) -> TransactionResult:
        """Install all prepared writes after a durable COMMITTING marker."""
        transaction_dir = self._transaction_dir(transaction_id)
        payload = self._read_journal(transaction_dir)
        phase = TransactionPhase(str(payload["phase"]))
        if phase is TransactionPhase.COMMITTED:
            return TransactionResult(transaction_id, phase, (), True)
        if phase is not TransactionPhase.PREPARED:
            raise RecoveryRequired(f"pdd recover --transaction {transaction_id}")
        hook = crash_hook or (lambda _event: None)
        entries = payload.get("entries")
        if not isinstance(entries, list):
            raise TransactionError("transaction entries are malformed")
        with self._locks(payload):
            self._validate_prepared_entries(transaction_dir, entries)
            for item in entries:
                if not isinstance(item, dict):
                    raise TransactionError("transaction entry is malformed")
                relpath = PurePosixPath(str(item["relpath"]))
                current = _file_state(
                    self.policy.resolve(relpath, allow_missing=True).canonical_path
                )
                precondition = item.get("precondition")
                if not isinstance(precondition, dict) or current != _parse_state(precondition):
                    raise TransactionConflict(f"destination changed: {relpath}")
            payload["phase"] = TransactionPhase.COMMITTING.value
            self._write_journal(transaction_dir, payload)
            hook("after_committing")
            changed: list[PurePosixPath] = []
            try:
                for index, item in enumerate(entries):
                    if not isinstance(item, dict):
                        raise TransactionError("transaction entry is malformed")
                    self._install_entry(transaction_dir, item)
                    item["installed"] = True
                    changed.append(PurePosixPath(str(item["relpath"])))
                    self._write_journal(transaction_dir, payload)
                    hook(f"after_install:{index}")
            except TransactionError:
                self._restore_entries(transaction_dir, entries)
                payload["phase"] = TransactionPhase.ROLLED_BACK.value
                self._write_journal(transaction_dir, payload)
                raise
            payload["phase"] = TransactionPhase.COMMITTED.value
            self._write_journal(transaction_dir, payload)
            hook("after_commit")
        return TransactionResult(
            transaction_id, TransactionPhase.COMMITTED, tuple(changed), False
        )

    def incomplete(self) -> tuple[str, ...]:
        """List transactions requiring explicit recovery without changing bytes."""
        if not self.state_root.exists():
            return ()
        pending: list[str] = []
        for transaction_dir in sorted(self.state_root.iterdir()):
            if not transaction_dir.is_dir() or transaction_dir.is_symlink():
                continue
            phase = TransactionPhase(str(self._read_journal(transaction_dir)["phase"]))
            if phase not in {TransactionPhase.COMMITTED, TransactionPhase.ROLLED_BACK}:
                pending.append(transaction_dir.name)
        return tuple(pending)

    def recover(self, transaction_id: str) -> TransactionResult:
        """Complete COMMITTING work or discard a PREPARED transaction idempotently."""
        transaction_dir = self._transaction_dir(transaction_id)
        payload = self._read_journal(transaction_dir)
        phase = TransactionPhase(str(payload["phase"]))
        if phase is TransactionPhase.COMMITTED:
            return TransactionResult(transaction_id, phase, (), True)
        if phase is TransactionPhase.PREPARED:
            payload["phase"] = TransactionPhase.ROLLED_BACK.value
            self._write_journal(transaction_dir, payload)
            return TransactionResult(
                transaction_id, TransactionPhase.ROLLED_BACK, (), False
            )
        if phase is not TransactionPhase.COMMITTING:
            return TransactionResult(transaction_id, phase, (), True)
        entries = payload.get("entries")
        if not isinstance(entries, list):
            raise TransactionError("transaction entries are malformed")
        changed: list[PurePosixPath] = []
        with self._locks(payload):
            try:
                self._validate_prepared_entries(transaction_dir, entries)
                for item in entries:
                    if not isinstance(item, dict):
                        raise TransactionError("transaction entry is malformed")
                    self._install_entry(transaction_dir, item)
                    item["installed"] = True
                    changed.append(PurePosixPath(str(item["relpath"])))
                    self._write_journal(transaction_dir, payload)
            except TransactionError:
                self._restore_entries(transaction_dir, entries)
                payload["phase"] = TransactionPhase.ROLLED_BACK.value
                self._write_journal(transaction_dir, payload)
                raise
            payload["phase"] = TransactionPhase.COMMITTED.value
            self._write_journal(transaction_dir, payload)
        return TransactionResult(
            transaction_id, TransactionPhase.COMMITTED, tuple(changed), False
        )
