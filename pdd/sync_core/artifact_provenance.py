"""Verification of protected build attestations for candidate wheels."""
# pylint: disable=duplicate-code,too-many-instance-attributes,too-many-boolean-expressions
# pylint: disable=too-many-branches

from __future__ import annotations

import base64
import argparse
import hashlib
import importlib.metadata
import json
import os
import re
import site
import subprocess
import tempfile
import sys
import sysconfig
import zipfile
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from email.parser import BytesParser
from pathlib import Path
from pathlib import PurePosixPath
from typing import Any, Iterable, Mapping

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
from .descriptor_store import DescriptorStoreError, update_json


class CandidateArtifactProvenanceError(ValueError):
    """Raised when a candidate wheel lacks protected build provenance."""


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


# The release checker has a second, deliberately separate policy: unlike a
# candidate build attestation, this closes the checker process and its installed
# runtime before any candidate repository input is parsed.
RUNTIME_BUNDLE_SCHEMA_VERSION = 1
LINUX_X86_64_PLATFORM = "linux_x86_64"
_RUNTIME_SHA256 = re.compile(r"[0-9a-f]{64}")
_RUNTIME_SHA1 = re.compile(r"[0-9a-f]{40}")
_RUNTIME_WHEEL = re.compile(r"[A-Za-z0-9_.+-]+\.whl")
_RUNTIME_ROOT_KEYS = frozenset({
    "schema_version", "repository", "tag", "source_sha", "pdd_wheel",
    "runtime_lock", "wheelhouse", "runtime", "interpreter",
    "console_entry_points", "installed_distributions", "startup", "native_closure",
    "independent_provenance",
})


class RuntimeBundleError(ValueError):
    """Raised when a released checker runtime cannot prove its complete closure."""


def _runtime_canonical(payload: object) -> bytes:
    try:
        return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise RuntimeBundleError("runtime bundle cannot be canonicalized") from exc


def canonical_runtime_manifest_sha256(payload: object) -> str:
    """Return the protected pin digest for one canonical runtime manifest."""
    return hashlib.sha256(_runtime_canonical(payload)).hexdigest()


def _runtime_sha(value: object, name: str) -> str:
    if not isinstance(value, str) or _RUNTIME_SHA256.fullmatch(value) is None:
        raise RuntimeBundleError(f"{name} is not a lowercase SHA-256")
    return value


def _runtime_name(value: str) -> str:
    return re.sub(r"[-_.]+", "-", value).lower()


def _runtime_relative(value: object, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise RuntimeBundleError(f"{name} must be a relative path")
    path = PurePosixPath(value)
    if path.is_absolute() or "." in path.parts or ".." in path.parts:
        raise RuntimeBundleError(f"{name} contains traversal")
    return path.as_posix()


def _runtime_file(root: Path, relative: str, name: str) -> Path:
    path = root / PurePosixPath(_runtime_relative(relative, name))
    if path.is_symlink() or not path.is_file():
        raise RuntimeBundleError(f"{name} is missing or unsafe")
    return path


def _runtime_wheel_identity(path: Path) -> tuple[str, str]:
    try:
        with zipfile.ZipFile(path) as archive:
            metadata = [name for name in archive.namelist() if name.endswith(".dist-info/METADATA")]
            if len(metadata) != 1 or len(archive.namelist()) != len(set(archive.namelist())):
                raise RuntimeBundleError("wheel metadata is ambiguous")
            parsed = BytesParser().parsebytes(archive.read(metadata[0]))
    except (OSError, zipfile.BadZipFile, KeyError) as exc:
        raise RuntimeBundleError("wheel cannot be inspected") from exc
    name, version = parsed.get("Name"), parsed.get("Version")
    if not isinstance(name, str) or not name or not isinstance(version, str) or not version:
        raise RuntimeBundleError("wheel has no exact distribution identity")
    return name, version


def _runtime_wheel_members(wheelhouse: Path) -> list[dict[str, str]]:
    if wheelhouse.is_symlink() or not wheelhouse.is_dir():
        raise RuntimeBundleError("wheelhouse is unsafe")
    names: set[str] = set()
    distributions: set[str] = set()
    members: list[dict[str, str]] = []
    for wheel in sorted(wheelhouse.iterdir(), key=lambda item: item.name):
        if (
                wheel.is_symlink()
                or not wheel.is_file()
                or _RUNTIME_WHEEL.fullmatch(wheel.name) is None
        ):
            raise RuntimeBundleError("wheelhouse contains an unsafe non-wheel member")
        normalized = wheel.name.lower()
        if normalized in names:
            raise RuntimeBundleError("wheelhouse contains duplicate normalized members")
        names.add(normalized)
        distribution, _version = _runtime_wheel_identity(wheel)
        distribution = _runtime_name(distribution)
        if distribution in distributions:
            raise RuntimeBundleError("wheelhouse contains ambiguous distributions")
        distributions.add(distribution)
        members.append({"name": wheel.name, "sha256": _sha256(wheel)})
    if not members:
        raise RuntimeBundleError("wheelhouse is empty")
    return members


def _runtime_wheelhouse_digest(members: Iterable[Mapping[str, str]]) -> str:
    return hashlib.sha256(_runtime_canonical(list(members))).hexdigest()


def write_runtime_bundle_lock(wheelhouse: Path, output: Path) -> None:
    """Write a one-wheel-per-distribution, fully hash-pinned offline lock."""
    rows = []
    for member in _runtime_wheel_members(wheelhouse):
        name, version = _runtime_wheel_identity(wheelhouse / member["name"])
        rows.append((_runtime_name(name), version, member["sha256"]))
    output.write_text(
        "".join(f"{name}=={version} --hash=sha256:{digest}\n"
                for name, version, digest in sorted(rows)), encoding="utf-8"
    )


def _runtime_identity() -> dict[str, str]:
    if (
            sys.implementation.name != "cpython" or sys.version_info[:2] != (3, 12)
            or sys.platform != "linux" or os.uname().machine != "x86_64"
            or not str(sysconfig.get_config_var("SOABI") or "").startswith("cpython-312")
    ):
        raise RuntimeBundleError("runtime only supports Linux x86_64 CPython 3.12")
    return {
        "implementation": "CPython",
        "version": f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
        "abi": "cp312", "platform": LINUX_X86_64_PLATFORM,
    }


def _runtime_site_packages() -> Path:
    paths = [Path(path) for path in site.getsitepackages() if Path(path).is_dir()]
    if len(paths) != 1 or paths[0].is_symlink():
        raise RuntimeBundleError("runtime site-packages is ambiguous or unsafe")
    return paths[0]


def _runtime_record_file(root: Path, raw: object) -> tuple[str, Path]:
    """Resolve a RECORD member, allowing only pip's canonical bin-script escape."""
    if not isinstance(raw, str) or not raw:
        raise RuntimeBundleError("RECORD member is malformed")
    lexical = PurePosixPath(raw)
    if lexical.is_absolute():
        raise RuntimeBundleError("RECORD member contains traversal")
    try:
        target = (root / lexical).resolve(strict=True)
    except OSError as exc:
        raise RuntimeBundleError("RECORD member is missing or unsafe") from exc
    if target.is_symlink() or not target.is_file():
        raise RuntimeBundleError("RECORD member is missing or unsafe")
    try:
        return target.relative_to(root).as_posix(), target
    except ValueError:
        pass
    bin_root = Path(sys.prefix).resolve() / "bin"
    try:
        name = target.relative_to(bin_root)
    except ValueError as exc:
        raise RuntimeBundleError("RECORD member contains traversal") from exc
    if len(name.parts) != 1 or not raw.startswith("../../../bin/"):
        raise RuntimeBundleError("RECORD member contains traversal")
    return f"@bin/{name.as_posix()}", target


def _runtime_installed_distributions(root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    names: set[str] = set()
    declared: set[str] = set()
    for distribution in importlib.metadata.distributions(path=[str(root)]):
        name, version = distribution.metadata.get("Name"), distribution.version
        if not isinstance(name, str) or not name or not isinstance(version, str) or not version:
            raise RuntimeBundleError("installed distribution metadata is malformed")
        normalized = _runtime_name(name)
        if normalized in names or not distribution.files:
            raise RuntimeBundleError("installed distributions are ambiguous or lack RECORD")
        names.add(normalized)
        files = []
        for package_path in distribution.files:
            relative, path = _runtime_record_file(root, str(package_path))
            if relative in declared:
                raise RuntimeBundleError("installed RECORD closures overlap")
            declared.add(relative)
            files.append({"path": relative, "sha256": _sha256(path)})
        if len({item["path"] for item in files}) != len(files):
            raise RuntimeBundleError("installed RECORD has duplicate members")
        rows.append({"name": normalized, "version": version,
                     "files": sorted(files, key=lambda item: item["path"])})
    actual = set()
    for path in root.rglob("*"):
        if "__pycache__" in path.parts:
            continue
        if path.is_symlink():
            raise RuntimeBundleError("installed closure contains a symlink")
        if path.is_file():
            actual.add(path.relative_to(root).as_posix())
    scripts = Path(sys.prefix).resolve() / "bin"
    for path in scripts.iterdir():
        if path.name.startswith(("activate", "python")):
            continue
        if path.is_symlink() or not path.is_file():
            raise RuntimeBundleError("runtime script closure contains a symlink or directory")
        actual.add(f"@bin/{path.name}")
    if not rows or actual != declared:
        raise RuntimeBundleError("installed closure has missing or extra files")
    return sorted(rows, key=lambda item: item["name"])


def _runtime_entry_points(root: Path) -> list[dict[str, str]]:
    pdd = next((distribution for distribution in importlib.metadata.distributions(path=[str(root)])
                if _runtime_name(str(distribution.metadata.get("Name", ""))) == "pdd-cli"), None)
    if pdd is None:
        raise RuntimeBundleError("pdd-cli distribution is absent")
    scripts = Path(sys.prefix) / "bin"
    entries = []
    for point in pdd.entry_points:
        if point.group == "console_scripts":
            path = scripts / point.name
            if path.is_symlink() or not path.is_file():
                raise RuntimeBundleError("console entry point is missing or unsafe")
            entries.append({"name": point.name, "path": f"bin/{point.name}",
                            "sha256": _sha256(path)})
    if not any(item["name"] == "pdd-sync-checker" for item in entries) or len(
            {item["name"] for item in entries}) != len(entries):
        raise RuntimeBundleError("pdd-sync-checker console entry point is not closed")
    return sorted(entries, key=lambda item: item["name"])


def _runtime_startup(root: Path) -> dict[str, Any]:
    entries = []
    for path in sorted(root.glob("*.pth"), key=lambda item: item.name):
        if path.is_symlink() or not path.is_file():
            raise RuntimeBundleError("startup .pth is unsafe")
        entries.append({"path": path.name, "sha256": _sha256(path)})
    result: dict[str, Any] = {"pth": entries}
    for filename, key in (("sitecustomize.py", "sitecustomize"),
                          ("usercustomize.py", "usercustomize")):
        path = root / filename
        if path.exists():
            if path.is_symlink() or not path.is_file():
                raise RuntimeBundleError("startup customization is unsafe")
            result[key] = {"path": filename, "sha256": _sha256(path)}
        else:
            result[key] = None
    return result


def _runtime_native_closure(root: Path) -> dict[str, Any]:
    members = []
    for path in sorted(root.rglob("*"), key=lambda item: item.as_posix()):
        if path.is_file() and path.suffix in {".so", ".pyd", ".dll", ".dylib"}:
            if path.is_symlink():
                raise RuntimeBundleError("native extension is unsafe")
            members.append({"path": path.relative_to(root).as_posix(), "sha256": _sha256(path)})
    libraries: dict[str, str] = {}
    for target in [Path(sys.executable).resolve(), *(root / item["path"] for item in members)]:
        result = subprocess.run(["ldd", str(target)], check=False, capture_output=True,
                                text=True, timeout=15)
        output = result.stdout + result.stderr
        if "not a dynamic executable" in output:
            continue
        if result.returncode != 0 or "not found" in output:
            raise RuntimeBundleError("native shared-library closure is unsupported")
        for match in re.finditer(r"=>\s+(/[^\s]+)", output):
            library = Path(match.group(1))
            if library.is_symlink() or not library.is_file():
                raise RuntimeBundleError("native shared library is unsafe")
            libraries[str(library)] = _sha256(library)
    return {"status": "complete", "members": members,
            "shared_libraries": [{"path": path, "sha256": digest}
                                 for path, digest in sorted(libraries.items())]}


def build_runtime_bundle_manifest(
    bundle: Path, *, repository: str, tag: str, source_sha: str
) -> dict[str, Any]:
    """Build the manifest from an offline-installed release runtime."""
    if (
            re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository) is None
            or re.fullmatch(r"v\d+\.\d+\.\d+", tag) is None
            or _RUNTIME_SHA1.fullmatch(source_sha) is None
    ):
        raise RuntimeBundleError("release identity is malformed")
    members = _runtime_wheel_members(bundle / "wheelhouse")
    pdd = [item for item in members if _runtime_name(
        _runtime_wheel_identity(bundle / "wheelhouse" / item["name"])[0]) == "pdd-cli"]
    if len(pdd) != 1:
        raise RuntimeBundleError("bundle must contain exactly one pdd-cli wheel")
    lock = _runtime_file(bundle, "runtime.lock", "runtime lock")
    root = _runtime_site_packages()
    interpreter = Path(sys.executable).resolve()
    if not interpreter.is_file():
        raise RuntimeBundleError("interpreter executable is unsafe")
    return {
        "schema_version": RUNTIME_BUNDLE_SCHEMA_VERSION, "repository": repository,
        "tag": tag, "source_sha": source_sha, "pdd_wheel": pdd[0],
        "runtime_lock": {"name": "runtime.lock", "sha256": _sha256(lock)},
        "wheelhouse": {"members": members, "digest": _runtime_wheelhouse_digest(members)},
        "runtime": _runtime_identity(), "interpreter": {"sha256": _sha256(interpreter)},
        "console_entry_points": _runtime_entry_points(root),
        "installed_distributions": _runtime_installed_distributions(root),
        "startup": _runtime_startup(root), "native_closure": _runtime_native_closure(root),
        # No independently signed bundle provenance exists in this release lane.
        "independent_provenance": {"status": "unsigned-blocked"},
    }


@dataclass(frozen=True)
class RuntimeBundlePolicy:
    """Protected caller expectations for a single immutable release runtime."""

    manifest_sha256: str
    repository: str
    tag: str
    source_sha: str

    def __post_init__(self) -> None:
        _runtime_sha(self.manifest_sha256, "protected manifest digest")
        if (
                re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", self.repository) is None
                or re.fullmatch(r"v\d+\.\d+\.\d+", self.tag) is None
                or _RUNTIME_SHA1.fullmatch(self.source_sha) is None
        ):
            raise RuntimeBundleError("protected release identity is malformed")


def runtime_bundle_policy_from_environment() -> tuple[Path, RuntimeBundlePolicy]:
    """Read only protected caller policy; bundle files never supply policy."""
    values = {
        "manifest_sha256": os.environ.get("PDD_RUNTIME_BUNDLE_MANIFEST_SHA256", ""),
        "repository": os.environ.get("PDD_RUNTIME_BUNDLE_REPOSITORY", ""),
        "tag": os.environ.get("PDD_RUNTIME_BUNDLE_TAG", ""),
        "source_sha": os.environ.get("PDD_RUNTIME_BUNDLE_SOURCE_SHA", ""),
    }
    directory = os.environ.get("PDD_RUNTIME_BUNDLE_DIR", "")
    if not directory or not all(values.values()):
        raise RuntimeBundleError("protected runtime bundle policy is required")
    return Path(directory), RuntimeBundlePolicy(**values)


def _runtime_manifest(bundle: Path) -> dict[str, Any]:
    manifest = _runtime_file(bundle, "runtime-manifest.json", "runtime manifest")
    try:
        payload = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RuntimeBundleError("runtime manifest cannot be read") from exc
    if not isinstance(payload, dict) or set(payload) != _RUNTIME_ROOT_KEYS:
        raise RuntimeBundleError("runtime manifest schema is closed and malformed")
    if payload.get("schema_version") != RUNTIME_BUNDLE_SCHEMA_VERSION:
        raise RuntimeBundleError("runtime manifest schema version is unsupported")
    return payload


def _runtime_validate_assets(bundle: Path, payload: Mapping[str, Any]) -> None:
    wheel = payload["pdd_wheel"]
    lock = payload["runtime_lock"]
    wheelhouse = payload["wheelhouse"]
    if not isinstance(wheel, Mapping) or set(wheel) != {"name", "sha256"}:
        raise RuntimeBundleError("pdd wheel schema is malformed")
    name = _runtime_relative(wheel["name"], "pdd wheel name")
    if "/" in name or _RUNTIME_WHEEL.fullmatch(name) is None or _sha256(
            _runtime_file(bundle / "wheelhouse", name, "pdd wheel")) != _runtime_sha(
                wheel["sha256"], "pdd wheel digest"):
        raise RuntimeBundleError("pdd wheel does not match")
    if (
            not isinstance(lock, Mapping)
            or set(lock) != {"name", "sha256"}
            or lock.get("name") != "runtime.lock"
    ):
        raise RuntimeBundleError("runtime lock schema is malformed")
    if _sha256(_runtime_file(bundle, "runtime.lock", "runtime lock")) != _runtime_sha(
            lock["sha256"], "runtime lock digest"):
        raise RuntimeBundleError("runtime lock digest does not match")
    if not isinstance(wheelhouse, Mapping) or set(wheelhouse) != {"members", "digest"}:
        raise RuntimeBundleError("wheelhouse schema is malformed")
    members = wheelhouse["members"]
    if not isinstance(members, list) or not all(
            isinstance(item, Mapping) and set(item) == {"name", "sha256"} for item in members):
        raise RuntimeBundleError("wheelhouse member schema is malformed")
    expected = _runtime_wheel_members(bundle / "wheelhouse")
    if members != expected or _runtime_wheelhouse_digest(expected) != _runtime_sha(
            wheelhouse["digest"], "wheelhouse digest"):
        raise RuntimeBundleError("wheelhouse closure does not match")
    lock_names: set[str] = set()
    for line in _runtime_file(bundle, "runtime.lock", "runtime lock").read_text(
            encoding="utf-8").splitlines():
        match = re.fullmatch(r"([A-Za-z0-9_.-]+)==([^\s]+) --hash=sha256:([0-9a-f]{64})", line)
        if match is None or _runtime_name(match.group(1)) in lock_names:
            raise RuntimeBundleError("runtime lock is not exact and hash pinned")
        lock_names.add(_runtime_name(match.group(1)))
    names = {_runtime_name(_runtime_wheel_identity(bundle / "wheelhouse" / item["name"])[0])
             for item in expected}
    if lock_names != names:
        raise RuntimeBundleError("runtime lock does not close the wheelhouse")


def validate_runtime_bundle(bundle: Path, policy: RuntimeBundlePolicy) -> dict[str, Any]:
    """Verify protected identity, offline assets, and installed runtime closure."""
    if bundle.is_symlink() or not bundle.is_dir():
        raise RuntimeBundleError("runtime bundle directory is unsafe")
    payload = _runtime_manifest(bundle)
    if canonical_runtime_manifest_sha256(payload) != policy.manifest_sha256:
        raise RuntimeBundleError("runtime manifest digest does not match protected policy")
    if (payload["repository"], payload["tag"], payload["source_sha"]) != (
            policy.repository, policy.tag, policy.source_sha):
        raise RuntimeBundleError("runtime manifest identity does not match protected policy")
    _runtime_validate_assets(bundle, payload)
    interpreter = payload["interpreter"]
    root = _runtime_site_packages()
    if (
            payload["runtime"] != _runtime_identity()
            or not isinstance(interpreter, Mapping)
            or set(interpreter) != {"sha256"}
            or _sha256(Path(sys.executable).resolve()) != _runtime_sha(
                interpreter["sha256"], "interpreter digest")
            or payload["installed_distributions"] != _runtime_installed_distributions(root)
            or payload["console_entry_points"] != _runtime_entry_points(root)
            or payload["startup"] != _runtime_startup(root)
            or not isinstance(payload["native_closure"], Mapping)
            or payload["native_closure"].get("status") != "complete"
            or payload["native_closure"] != _runtime_native_closure(root)
    ):
        raise RuntimeBundleError("runtime closure does not match")
    return payload


def require_independent_runtime_provenance(payload: Mapping[str, Any]) -> None:
    """Fail closed until a separately verified release-bundle signer is introduced."""
    provenance = payload.get("independent_provenance")
    if provenance != {"status": "signed"}:
        raise RuntimeBundleError("independent runtime bundle provenance is unavailable")


def _runtime_bundle_main() -> None:
    parser = argparse.ArgumentParser(description="Build or verify a closed checker runtime bundle")
    commands = parser.add_subparsers(dest="command", required=True)
    lock = commands.add_parser("write-lock")
    lock.add_argument("--wheelhouse", required=True, type=Path)
    lock.add_argument("--output", required=True, type=Path)
    manifest = commands.add_parser("write-manifest")
    manifest.add_argument("--bundle", required=True, type=Path)
    manifest.add_argument("--repository", required=True)
    manifest.add_argument("--tag", required=True)
    manifest.add_argument("--source-sha", required=True)
    verify = commands.add_parser("verify")
    verify.add_argument("--bundle", required=True, type=Path)
    verify.add_argument("--manifest-sha256", required=True)
    verify.add_argument("--repository", required=True)
    verify.add_argument("--tag", required=True)
    verify.add_argument("--source-sha", required=True)
    args = parser.parse_args()
    if args.command == "write-lock":
        write_runtime_bundle_lock(args.wheelhouse, args.output)
    elif args.command == "write-manifest":
        payload = build_runtime_bundle_manifest(
            args.bundle, repository=args.repository, tag=args.tag, source_sha=args.source_sha
        )
        (args.bundle / "runtime-manifest.json").write_bytes(_runtime_canonical(payload))
    else:
        validate_runtime_bundle(args.bundle, RuntimeBundlePolicy(
            args.manifest_sha256, args.repository, args.tag, args.source_sha
        ))


if __name__ == "__main__":
    _runtime_bundle_main()
