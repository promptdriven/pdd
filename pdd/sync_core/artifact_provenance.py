"""Verification of protected build attestations for candidate wheels."""
# pylint: disable=duplicate-code,too-many-instance-attributes,too-many-boolean-expressions
# pylint: disable=too-many-locals,too-many-branches,too-many-statements

from __future__ import annotations

import base64
import argparse
import csv
import hashlib
import io
import json
import os
import re
import stat
import sys
import tempfile
import zipfile
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from pathlib import PurePosixPath
from typing import Any, Iterable

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
from packaging.utils import InvalidWheelFilename, canonicalize_name, parse_wheel_filename
from packaging.version import InvalidVersion, Version
from .descriptor_store import DescriptorStoreError, update_json


class CandidateArtifactProvenanceError(ValueError):
    """Raised when a candidate wheel lacks protected build provenance."""


class TargetRuntimeLockError(ValueError):
    """Raised when an untrusted target runtime lock or wheel closure is invalid."""


TARGET_RUNTIME = "linux_x86_64-cp312"
TARGET_BASE_IMAGE = (
    "python:3.12.13-slim-bookworm@"
    "sha256:72d3d75f2639ab82b34b29390ad3d6e0827c775befee94edda8e9976818f488d"
)
TARGET_RESOLVER = "pip==25.1.1"
_LOCK_HEADER = (
    "# pdd-runtime-lock-format: 1",
    f"# target: {TARGET_RUNTIME}",
    f"# resolver: {TARGET_RESOLVER}",
    f"# base-image: {TARGET_BASE_IMAGE}",
)
_LOCK_ROW = re.compile(
    r"(?P<name>[a-z0-9]+(?:-[a-z0-9]+)*)==(?P<version>[^ ]+)"
    r"(?P<hashes>(?: --hash=sha256:[0-9a-f]{64})+)"
)
_SHA256_HASH = re.compile(r"[0-9a-f]{64}")
_MANYLINUX_PLATFORM = re.compile(r"manylinux(?:_[0-9]+|[0-9]+)_[0-9]+_x86_64")


@dataclass(frozen=True)
class TargetRuntimeLockEntry:
    """One exact, hash-bound dependency in the target runtime closure."""

    name: str
    version: str
    hashes: tuple[str, ...]


@dataclass(frozen=True)
class TargetRuntimeLock:
    """Canonical Linux CPython 3.12 dependency lock."""

    entries: tuple[TargetRuntimeLockEntry, ...]

    def bytes(self) -> bytes:
        """Serialize the lock in its sole accepted canonical representation."""
        rows = list(_LOCK_HEADER)
        for entry in self.entries:
            hashes = "".join(f" --hash=sha256:{value}" for value in entry.hashes)
            rows.append(f"{entry.name}=={entry.version}{hashes}")
        return ("\n".join(rows) + "\n").encode("ascii")


@dataclass(frozen=True)
class _WheelInfo:
    """Verified wheel identity and archive bytes used by closure validators."""

    path: Path
    name: str
    version: str
    digest: str
    files: dict[PurePosixPath, bytes]


def _runtime_error(message: str) -> TargetRuntimeLockError:
    return TargetRuntimeLockError(f"target runtime lock: {message}")


def _canonical_version(value: object) -> str:
    if not isinstance(value, str) or not value:
        raise _runtime_error("version is invalid")
    try:
        parsed = Version(value)
    except InvalidVersion as exc:
        raise _runtime_error("version is not PEP 440") from exc
    if str(parsed) != value:
        raise _runtime_error("version is not canonical PEP 440")
    return value


def _canonical_name(value: object) -> str:
    if not isinstance(value, str) or not re.fullmatch(
        r"[a-z0-9]+(?:-[a-z0-9]+)*", value
    ):
        raise _runtime_error("distribution name is not normalized")
    if canonicalize_name(value) != value:
        raise _runtime_error("distribution name is not normalized")
    return value


def parse_target_runtime_lock(payload: bytes) -> TargetRuntimeLock:
    """Strictly parse canonical bytes for the one supported target runtime."""
    if not isinstance(payload, bytes) or not payload or b"\r" in payload:
        raise _runtime_error("lock bytes are malformed")
    try:
        text = payload.decode("ascii")
    except UnicodeDecodeError as exc:
        raise _runtime_error("lock must be ASCII") from exc
    if not text.endswith("\n") or "\n\n" in text:
        raise _runtime_error("lock formatting is malformed")
    lines = text[:-1].split("\n")
    if tuple(lines[: len(_LOCK_HEADER)]) != _LOCK_HEADER:
        raise _runtime_error("header is malformed or does not bind the target")
    entries: list[TargetRuntimeLockEntry] = []
    previous = ""
    seen: set[str] = set()
    for line in lines[len(_LOCK_HEADER) :]:
        matched = _LOCK_ROW.fullmatch(line)
        if matched is None:
            raise _runtime_error("contains an unrecognized requirement line")
        name = _canonical_name(matched.group("name"))
        version = _canonical_version(matched.group("version"))
        if name == "pdd-cli":
            raise _runtime_error("must not include pdd-cli")
        hashes = tuple(
            item.removeprefix(" --hash=sha256:")
            for item in re.findall(r" --hash=sha256:[0-9a-f]{64}", matched.group("hashes"))
        )
        if (
            not hashes
            or len(hashes) != len(set(hashes))
            or tuple(sorted(hashes)) != hashes
            or any(_SHA256_HASH.fullmatch(item) is None for item in hashes)
        ):
            raise _runtime_error("hash list is malformed")
        if name in seen or name <= previous:
            raise _runtime_error("distribution rows are duplicate or unsorted")
        seen.add(name)
        previous = name
        entries.append(TargetRuntimeLockEntry(name, version, hashes))
    lock = TargetRuntimeLock(tuple(entries))
    if lock.bytes() != payload:
        raise _runtime_error("lock is not canonical")
    return lock


def _safe_directory(path: Path, label: str) -> Path:
    candidate = Path(path)
    if candidate.is_symlink() or not candidate.is_dir():
        raise _runtime_error(f"{label} is unsafe")
    return candidate


def _wheel_tags_are_compatible(filename: str) -> bool:
    """Accept only pure or manylinux x86_64 wheels usable by CPython 3.12."""
    try:
        _name, _version, _build, tags = parse_wheel_filename(filename)
    except InvalidWheelFilename:
        return False
    for tag in tags:
        if tag.platform == "any" and tag.abi == "none" and tag.interpreter in {
            "py3", "py312", "py2.py3"
        }:
            return True
        if _MANYLINUX_PLATFORM.fullmatch(tag.platform) is None:
            continue
        if tag.interpreter == "cp312" and tag.abi in {"cp312", "abi3", "none"}:
            return True
        match = re.fullmatch(r"cp(3[0-9]{1,2})", tag.interpreter)
        if match and tag.abi == "abi3" and 32 <= int(match.group(1)) <= 312:
            return True
    return False


def _safe_zip_path(value: str) -> PurePosixPath:
    if not value or "\\" in value:
        raise _runtime_error("wheel archive contains an unsafe member")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or path == PurePosixPath("."):
        raise _runtime_error("wheel archive contains an unsafe member")
    return path


def _metadata_identity(metadata: bytes) -> tuple[str, str]:
    """Read the two required core metadata fields without coercion."""
    try:
        text = metadata.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise _runtime_error("wheel METADATA is not UTF-8") from exc
    fields: dict[str, list[str]] = {}
    for line in text.splitlines():
        if not line:
            break
        if line[0] in " \t" or ":" not in line:
            raise _runtime_error("wheel METADATA headers are malformed")
        name, value = line.split(":", 1)
        if not name or not value.startswith(" "):
            raise _runtime_error("wheel METADATA headers are malformed")
        fields.setdefault(name.lower(), []).append(value.strip())
    names = fields.get("name", [])
    versions = fields.get("version", [])
    if len(names) != 1 or len(versions) != 1:
        raise _runtime_error("wheel METADATA identity is malformed")
    raw_name = names[0]
    normalized = canonicalize_name(raw_name)
    if not raw_name or normalized == "" or "\n" in raw_name:
        raise _runtime_error("wheel METADATA name is malformed")
    return normalized, _canonical_version(versions[0])


def _inspect_wheel(path: Path) -> _WheelInfo:
    """Return one safe wheel only after filename, tags, metadata, and bytes agree."""
    wheel = Path(path)
    if wheel.is_symlink() or not wheel.is_file() or wheel.suffix != ".whl":
        raise _runtime_error("wheel path is unsafe")
    if not _wheel_tags_are_compatible(wheel.name):
        raise _runtime_error("wheel tags are incompatible with linux_x86_64-cp312")
    try:
        filename_name, filename_version, _build, _tags = parse_wheel_filename(wheel.name)
    except InvalidWheelFilename as exc:
        raise _runtime_error("wheel filename is malformed") from exc
    name = canonicalize_name(str(filename_name))
    version = _canonical_version(str(filename_version))
    files: dict[PurePosixPath, bytes] = {}
    members: set[PurePosixPath] = set()
    metadata_members: list[PurePosixPath] = []
    record_members: list[PurePosixPath] = []
    try:
        with zipfile.ZipFile(wheel) as archive:
            for member in archive.infolist():
                member_path = _safe_zip_path(member.filename.rstrip("/"))
                mode = member.external_attr >> 16
                if stat.S_ISLNK(mode) or member_path in members:
                    raise _runtime_error("wheel archive contains unsafe duplicate or link")
                members.add(member_path)
                if member.is_dir():
                    continue
                files[member_path] = archive.read(member)
                if member_path.name == "METADATA" and member_path.parent.name.endswith(
                    ".dist-info"
                ):
                    metadata_members.append(member_path)
                if member_path.name == "RECORD" and member_path.parent.name.endswith(
                    ".dist-info"
                ):
                    record_members.append(member_path)
    except (OSError, zipfile.BadZipFile) as exc:
        raise _runtime_error("wheel archive cannot be read") from exc
    if len(metadata_members) != 1 or len(record_members) != 1:
        raise _runtime_error("wheel archive lacks an unambiguous dist-info record")
    metadata_name, metadata_version = _metadata_identity(files[metadata_members[0]])
    if metadata_name != name or metadata_version != version:
        raise _runtime_error("wheel filename and METADATA identity disagree")
    return _WheelInfo(wheel, name, version, _sha256(wheel), files)


def _wheelhouse_wheels(wheelhouse: Path) -> tuple[Path, ...]:
    root = _safe_directory(wheelhouse, "wheelhouse")
    wheels: list[Path] = []
    for child in sorted(root.iterdir(), key=lambda item: item.name):
        if child.is_symlink() or not child.is_file() or child.suffix != ".whl":
            raise _runtime_error("wheelhouse contains a non-wheel or unsafe member")
        wheels.append(child)
    return tuple(wheels)


def validate_target_wheelhouse(
    lock: TargetRuntimeLock, wheelhouse: Path
) -> dict[str, _WheelInfo]:
    """Require an exact lock-to-wheel bijection for the fixed target runtime."""
    lock = parse_target_runtime_lock(lock.bytes())
    expected = {entry.name: entry for entry in lock.entries}
    found: dict[str, _WheelInfo] = {}
    for wheel in _wheelhouse_wheels(wheelhouse):
        info = _inspect_wheel(wheel)
        if info.name in found:
            raise _runtime_error("wheelhouse has duplicate distributions")
        entry = expected.get(info.name)
        if entry is None:
            raise _runtime_error("wheelhouse has an extra distribution")
        if info.version != entry.version or info.digest not in entry.hashes:
            raise _runtime_error("wheelhouse wheel does not match lock identity or hash")
        found[info.name] = info
    if set(found) != set(expected):
        raise _runtime_error("wheelhouse is missing a locked distribution")
    return found


def generate_target_runtime_lock(wheelhouse: Path) -> TargetRuntimeLock:
    """Generate canonical bytes only from a complete, target-compatible wheelhouse."""
    entries: list[TargetRuntimeLockEntry] = []
    seen: set[str] = set()
    for wheel in _wheelhouse_wheels(wheelhouse):
        info = _inspect_wheel(wheel)
        if info.name == "pdd-cli":
            raise _runtime_error("wheelhouse generator input must exclude pdd-cli")
        if info.name in seen:
            raise _runtime_error("wheelhouse has duplicate distributions")
        seen.add(info.name)
        entries.append(TargetRuntimeLockEntry(info.name, info.version, (info.digest,)))
    lock = TargetRuntimeLock(tuple(sorted(entries, key=lambda entry: entry.name)))
    # Validate the generated contract against the same wheelhouse before emission.
    validate_target_wheelhouse(lock, wheelhouse)
    return parse_target_runtime_lock(lock.bytes())


def _record_rows(record: Path) -> Iterable[tuple[str, str, str]]:
    try:
        with record.open("r", encoding="utf-8", newline="") as handle:
            text = handle.read()
    except (OSError, UnicodeDecodeError) as exc:
        raise _runtime_error("installed RECORD cannot be read") from exc
    try:
        rows = tuple(csv.reader(io.StringIO(text)))
    except csv.Error as exc:
        raise _runtime_error("installed RECORD is malformed") from exc
    if not rows or any(len(row) != 3 for row in rows):
        raise _runtime_error("installed RECORD is malformed")
    return tuple((row[0], row[1], row[2]) for row in rows)


def _installed_path(root: Path, relative: str) -> tuple[Path, PurePosixPath]:
    try:
        path = _safe_zip_path(relative)
    except TargetRuntimeLockError as exc:
        raise _runtime_error("installed RECORD has an unsafe path") from exc
    target = root.joinpath(*path.parts)
    if target.is_symlink() or not target.is_file():
        raise _runtime_error("installed RECORD references an unsafe or missing file")
    return target, path


def _record_hash(value: bytes) -> str:
    encoded = base64.urlsafe_b64encode(hashlib.sha256(value).digest())
    return encoded.rstrip(b"=").decode("ascii")


def _wheel_install_path(path: PurePosixPath) -> PurePosixPath | None:
    """Map only the wheel layouts allowed in the isolated --target installation."""
    if path.name == "RECORD" and path.parent.name.endswith(".dist-info"):
        return None
    for index, part in enumerate(path.parts):
        if not part.endswith(".data"):
            continue
        if (
            index + 2 < len(path.parts)
            and path.parts[index + 1] in {"purelib", "platlib"}
        ):
            return PurePosixPath(*path.parts[index + 2 :])
        return None
    return path


def _expected_installed_files(info: _WheelInfo) -> dict[PurePosixPath, bytes]:
    expected: dict[PurePosixPath, bytes] = {}
    for archive_path, content in info.files.items():
        installed_path = _wheel_install_path(archive_path)
        if installed_path is None:
            continue
        if installed_path in expected:
            raise _runtime_error("wheel has ambiguous installed paths")
        expected[installed_path] = content
    return expected


def validate_installed_target_runtime(
    lock: TargetRuntimeLock,
    wheelhouse: Path,
    site_packages: Path,
    project_wheel: Path,
) -> None:
    """Verify an isolated install against locked wheels plus one exact pdd-cli wheel."""
    lock = parse_target_runtime_lock(lock.bytes())
    wheels = validate_target_wheelhouse(lock, wheelhouse)
    project = _inspect_wheel(project_wheel)
    if project.name != "pdd-cli":
        raise _runtime_error("separate project wheel is not pdd-cli")
    expected_wheels = {**wheels, project.name: project}
    root = _safe_directory(site_packages, "installed site-packages")
    dist_infos = sorted(root.glob("*.dist-info"), key=lambda item: item.name)
    if any(item.is_symlink() or not item.is_dir() for item in dist_infos):
        raise _runtime_error("installed distribution metadata is unsafe")
    installed: dict[str, tuple[Path, _WheelInfo]] = {}
    seen_files: dict[PurePosixPath, str] = {}
    for dist_info in dist_infos:
        metadata = dist_info / "METADATA"
        record = dist_info / "RECORD"
        if (
            metadata.is_symlink()
            or record.is_symlink()
            or not metadata.is_file()
            or not record.is_file()
        ):
            raise _runtime_error("installed distribution lacks regular METADATA or RECORD")
        name, version = _metadata_identity(metadata.read_bytes())
        expected = expected_wheels.get(name)
        if expected is None or expected.version != version or name in installed:
            raise _runtime_error("installed distribution set does not match target runtime")
        installed[name] = (dist_info, expected)
        record_relative = PurePosixPath(dist_info.name, "RECORD")
        expected_files = _expected_installed_files(expected)
        recorded_expected: set[PurePosixPath] = set()
        for relative, declared_hash, declared_size in _record_rows(record):
            target, relative_path = _installed_path(root, relative)
            if relative_path in seen_files:
                raise _runtime_error("installed RECORD closure overlaps")
            seen_files[relative_path] = name
            if relative_path == record_relative:
                if declared_hash or declared_size:
                    raise _runtime_error("installed RECORD self row must omit hash and size")
                continue
            content = target.read_bytes()
            if (
                not re.fullmatch(r"sha256=[A-Za-z0-9_-]+", declared_hash)
                or declared_hash.removeprefix("sha256=") != _record_hash(content)
                or declared_size != str(len(content))
            ):
                raise _runtime_error("installed RECORD hash or size does not match")
            allowed_generated = (
                relative_path.parent == PurePosixPath(dist_info.name)
                and relative_path.name in {"INSTALLER", "REQUESTED"}
            )
            expected_content = expected_files.get(relative_path)
            if not allowed_generated and expected_content != content:
                raise _runtime_error("installed files do not match their exact wheel")
            if not allowed_generated:
                recorded_expected.add(relative_path)
        if recorded_expected != set(expected_files):
            raise _runtime_error("installed RECORD does not close over its exact wheel")
    if set(installed) != set(expected_wheels):
        raise _runtime_error("installed distribution set is incomplete or has extras")
    actual_files: set[PurePosixPath] = set()
    expected_directories = {PurePosixPath(".")}
    for relative in seen_files:
        expected_directories.update(relative.parents)
    for current, directories, filenames in os.walk(root, followlinks=False):
        current_path = Path(current)
        relative_directory = PurePosixPath(current_path.relative_to(root).as_posix())
        if relative_directory not in expected_directories:
            raise _runtime_error("installed tree contains an extra directory")
        for directory in directories:
            path = current_path / directory
            if path.is_symlink() or not path.is_dir():
                raise _runtime_error("installed tree contains an unsafe directory")
        for filename in filenames:
            path = current_path / filename
            relative = PurePosixPath(path.relative_to(root).as_posix())
            if path.is_symlink() or not path.is_file():
                raise _runtime_error("installed tree contains a non-regular file")
            actual_files.add(relative)
    if actual_files != set(seen_files):
        raise _runtime_error("installed RECORD closure has missing or extra files")


def target_wheel_inventory(wheelhouse: Path) -> bytes:
    """Produce a compact deterministic inventory for the candidate artifact."""
    inventory = [
        {"filename": wheel.name, "sha256": _inspect_wheel(wheel).digest}
        for wheel in _wheelhouse_wheels(wheelhouse)
    ]
    return (json.dumps(inventory, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def _runtime_lock_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="pdd-target-runtime-lock")
    commands = parser.add_subparsers(dest="command", required=True)
    generate = commands.add_parser("generate")
    generate.add_argument("--wheelhouse", type=Path, required=True)
    generate.add_argument("--output", type=Path, required=True)
    generate.add_argument("--inventory", type=Path, required=True)
    validate_wheelhouse = commands.add_parser("validate-wheelhouse")
    validate_wheelhouse.add_argument("--lock", type=Path, required=True)
    validate_wheelhouse.add_argument("--wheelhouse", type=Path, required=True)
    validate_installed = commands.add_parser("validate-installed")
    validate_installed.add_argument("--lock", type=Path, required=True)
    validate_installed.add_argument("--wheelhouse", type=Path, required=True)
    validate_installed.add_argument("--site-packages", type=Path, required=True)
    validate_installed.add_argument("--project-wheel", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "generate":
            args.output.write_bytes(generate_target_runtime_lock(args.wheelhouse).bytes())
            args.inventory.write_bytes(target_wheel_inventory(args.wheelhouse))
        else:
            lock = parse_target_runtime_lock(args.lock.read_bytes())
            if args.command == "validate-wheelhouse":
                validate_target_wheelhouse(lock, args.wheelhouse)
            else:
                validate_installed_target_runtime(
                    lock, args.wheelhouse, args.site_packages, args.project_wheel
                )
    except (OSError, TargetRuntimeLockError) as exc:
        parser.error(str(exc))
    return 0


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


if __name__ == "__main__":  # pragma: no cover
    sys.exit(_runtime_lock_main())
