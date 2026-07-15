"""Fail-closed OS sandbox and complete process-group supervision."""
# pylint: disable=too-many-arguments,too-many-lines

from __future__ import annotations

import json
import hashlib
import math
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from functools import lru_cache
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
import sysconfig


# Capture the executable that loaded this trusted module. Tests and callers may
# replace ``sys.executable`` to model argv-prefix portability; that synthetic
# spelling must never become a measured file or sandbox mount source.
_SUPERVISOR_EXECUTABLE = Path(sys.executable)
_TRUSTED_ROOT_PATH = "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
_FRAMEWORK_OBSERVATION_PATH = Path("/run/pdd-framework-observation")
_SCOPE_PATTERN = re.compile(r"pdd-validator-[0-9a-f]{32}\.scope")
_TRUSTED_POSTPROCESS_SECONDS = 5
_TRUSTED_COMMAND_SECONDS = 5
_TRUSTED_SETUP_SECONDS = 30
_MAX_BINDING_ATTESTATION_BYTES = 4 * 1024 * 1024
_VITEST_ATTESTATION_SCHEMA = "pdd-vitest-toolchain-attestation-v1"
_BINDING_RECORD_SCHEMA = "pdd-immutable-binding-record-v1"
_CANDIDATE_IDENTITY_SCHEMA = "pdd-candidate-identity-v1"
_VITEST_MEMBER_ROLES = frozenset({
    "launcher", "entrypoint", "dependencies", "native_runtime", "lockfile",
})

_PIDFD_PROTOCOL_SOURCE = """
def _supervise_candidate(pid, timeout):
    pidfd = None
    reaped = False
    try:
        if not hasattr(os, 'pidfd_open'):
            raise RuntimeError('pidfd_open unavailable')
        pidfd = os.pidfd_open(pid, 0)
        poller = select.poll()
        poller.register(pidfd, select.POLLIN)
        events = poller.poll(math.ceil(timeout * 1000))
        if events and not any(
            fd == pidfd and mask & select.POLLIN for fd, mask in events
        ):
            raise RuntimeError('pidfd poll returned invalid events')
        timed_out = not events
        if timed_out:
            os.kill(pid, 9)
        waited, status = os.waitpid(pid,0)
        if waited != pid:
            raise RuntimeError('waitpid returned wrong child')
        reaped = True
        return (
            124 if timed_out else os.waitstatus_to_exitcode(status),
            timed_out,
        )
    finally:
        if pidfd is not None:
            os.close(pidfd)
        if not reaped:
            try:
                os.kill(pid, 9)
            except ProcessLookupError:
                pass
            try:
                waited, _status = os.waitpid(pid,0)
                if waited != pid:
                    raise RuntimeError('waitpid returned wrong child')
            except ChildProcessError:
                pass
"""


@dataclass(frozen=True)
class SupervisorLimits:
    """Hard limits applied to every untrusted validator process tree."""

    max_output_bytes: int = 16 * 1024 * 1024
    max_writable_bytes: int = 512 * 1024 * 1024
    max_memory_bytes: int = 2 * 1024 * 1024 * 1024
    max_virtual_memory_bytes: int = 2 * 1024 * 1024 * 1024
    max_cpu_seconds: int = 300
    max_processes: int = 128


@dataclass(frozen=True)
# pylint: disable-next=too-many-instance-attributes
class ImmutableBindingProof:
    """Descriptor-bound identity authorizing one copied runtime replacement."""

    copied_source: Path
    protected_source: Path
    destination: Path
    descriptor_attestation: str
    descriptor_identity: str
    member_role: str
    member_path: str
    collision_category: str


@dataclass(frozen=True)
# pylint: disable-next=too-many-instance-attributes
class _ValidatedBindingProof:
    """Canonical immutable binding authority ready for helper serialization."""

    copied_source: Path
    protected_source: Path
    destination: Path
    descriptor_attestation: str
    descriptor_identity: str
    member_role: str
    member_path: str
    collision_category: str
    member_digest: str
    member_mode: int


@dataclass(frozen=True)
# pylint: disable-next=too-many-instance-attributes
class _TrustedTools:
    """Exact privileged executable identities used by one protected run."""

    bwrap: Path
    mount: Path
    setpriv: Path
    sudo: Path
    systemctl: Path
    systemd_run: Path
    umount: Path
    unshare: Path


@dataclass(frozen=True)
# pylint: disable-next=too-many-instance-attributes
class _ScopePlan:
    """Immutable transient-scope construction and cleanup state."""

    unit_name: str
    control_directory: Path
    helper_source: str
    bwrap_argv: tuple[str, ...]
    sources: tuple[Path, ...]
    staging_targets: tuple[Path, ...]
    tools: _TrustedTools
    immutable_binding_proofs: tuple[str, ...] = ()


@dataclass(frozen=True)
class _CandidateRecord:
    """Validated terminal status emitted by the privileged direct-child helper."""

    returncode: int
    timed_out: bool


def _canonical_json(payload: object) -> str:
    """Return the one accepted compact, key-sorted JSON spelling."""
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def _validate_vitest_member_payload(member: object) -> dict[str, object]:
    """Validate one exact typed member from a canonical Vitest descriptor."""
    # pylint: disable=unidiomatic-typecheck
    if type(member) is not dict or set(member) != {
        "role", "path", "kind", "mode", "digest", "target",
    }:
        raise ValueError("invalid member fields")
    role = member["role"]
    relative = member["path"]
    kind = member["kind"]
    mode = member["mode"]
    digest = member["digest"]
    target = member["target"]
    if type(role) is not str or role not in _VITEST_MEMBER_ROLES:
        raise ValueError("invalid member role")
    if type(relative) is not str or not relative or len(relative) > 4096:
        raise ValueError("invalid member path")
    parsed = PurePosixPath(relative)
    if (
        parsed.is_absolute()
        or ".." in parsed.parts
        or parsed.as_posix() != relative
    ):
        raise ValueError("non-canonical member path")
    if type(kind) is not str or kind not in {"file", "directory", "symlink"}:
        raise ValueError("invalid member kind")
    if type(mode) is not int or not 0 <= mode <= 0o777:
        raise ValueError("invalid member mode")
    if kind == "file":
        if (
            type(digest) is not str
            or re.fullmatch(r"[0-9a-f]{64}", digest) is None
            or target is not None
        ):
            raise ValueError("invalid regular member identity")
    elif kind == "directory":
        if digest is not None or target is not None:
            raise ValueError("invalid directory member identity")
    elif (
        digest is not None
        or type(target) is not str
        or not target
        or len(target) > 4096
    ):
        raise ValueError("invalid symlink member identity")
    return member


def _parse_vitest_descriptor_attestation(
    encoded: str,
) -> tuple[dict[str, object], str]:
    """Independently validate and identify one canonical Vitest attestation."""
    # pylint: disable=too-many-locals,too-many-branches,unidiomatic-typecheck
    if (
        type(encoded) is not str
        or not encoded
        or len(encoded.encode("utf-8")) > _MAX_BINDING_ATTESTATION_BYTES
    ):
        raise ValueError("invalid attestation encoding")
    payload = json.loads(encoded)
    if type(payload) is not dict or set(payload) != {
        "schema", "adapter", "members", "native_runtime", "launch_policy",
    }:
        raise ValueError("invalid attestation fields")
    if (
        payload["schema"] != _VITEST_ATTESTATION_SCHEMA
        or type(payload["schema"]) is not str
        or payload["adapter"] != "vitest"
        or type(payload["adapter"]) is not str
    ):
        raise ValueError("invalid attestation authority")
    policy = payload["launch_policy"]
    if (
        type(policy) is not dict
        or set(policy) != {"linux_wasm_trap_handler_disabled"}
        or type(policy["linux_wasm_trap_handler_disabled"]) is not bool
    ):
        raise ValueError("invalid attestation launch policy")
    members = payload["members"]
    if type(members) is not list or not members:
        raise ValueError("invalid attestation members")
    validated = [_validate_vitest_member_payload(member) for member in members]
    keys = [(member["role"], member["path"]) for member in validated]
    if keys != sorted(keys) or len(keys) != len(set(keys)):
        raise ValueError("non-canonical attestation members")
    if _VITEST_MEMBER_ROLES - {member["role"] for member in validated}:
        raise ValueError("incomplete attestation roles")
    native_members = [
        member for member in validated if member["role"] == "native_runtime"
    ]
    native_runtime = payload["native_runtime"]
    if (
        type(native_runtime) is not list
        or len(native_runtime) != len(native_members)
        or not native_runtime
    ):
        raise ValueError("invalid native runtime topology")
    path_type = type(Path())
    for index, (value, member) in enumerate(zip(
        native_runtime, native_members, strict=True
    )):
        if (
            type(value) is not str
            or not value
            or len(value) > 4096
            or member["path"] != str(index)
        ):
            raise ValueError("invalid native runtime destination")
        path = Path(value)
        if type(path) is not path_type or not path.is_absolute():
            raise ValueError("invalid native runtime destination")
        try:
            metadata = path.lstat()
            canonical = path.resolve(strict=True)
        except OSError as exc:
            raise ValueError("unresolvable native runtime destination") from exc
        if (
            canonical != path
            or not stat.S_ISREG(metadata.st_mode)
            or stat.S_ISLNK(metadata.st_mode)
        ):
            raise ValueError("non-canonical native runtime destination")
    if encoded != _canonical_json(payload):
        raise ValueError("non-canonical attestation encoding")
    members_identity = hashlib.sha256(
        _canonical_json(validated).encode("utf-8")
    ).hexdigest()
    descriptor_identity = hashlib.sha256(_canonical_json({
        "members": members_identity,
        "launch_policy": policy,
    }).encode("utf-8")).hexdigest()
    return payload, descriptor_identity


def _vitest_descriptor_attestation(
    members: tuple[dict[str, object], ...], native_runtime: tuple[Path, ...],
    *, linux_wasm_trap_handler_disabled: bool,
) -> tuple[str, str]:
    """Build and independently reparse one canonical descriptor attestation."""
    payload = {
        "schema": _VITEST_ATTESTATION_SCHEMA,
        "adapter": "vitest",
        "members": list(members),
        "native_runtime": [str(path) for path in native_runtime],
        "launch_policy": {
            "linux_wasm_trap_handler_disabled": linux_wasm_trap_handler_disabled,
        },
    }
    encoded = _canonical_json(payload)
    _payload, identity = _parse_vitest_descriptor_attestation(encoded)
    return encoded, identity


def _regular_file_matches(path: Path, digest: str, mode: int) -> bool:
    """Match a no-follow regular file to one canonical descriptor member."""
    try:
        descriptor = os.open(
            path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | os.O_CLOEXEC
        )
    except OSError:
        return False
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or stat.S_IMODE(before.st_mode) != mode
        ):
            return False
        actual = hashlib.sha256()
        while chunk := os.read(descriptor, 1024 * 1024):
            actual.update(chunk)
        after = os.fstat(descriptor)
        stable = (
            before.st_dev, before.st_ino, before.st_size,
            before.st_mtime_ns, before.st_ctime_ns,
        ) == (
            after.st_dev, after.st_ino, after.st_size,
            after.st_mtime_ns, after.st_ctime_ns,
        )
        return stable and actual.hexdigest() == digest
    except OSError:
        return False
    finally:
        os.close(descriptor)


def _validate_immutable_binding_proof(
    proof: ImmutableBindingProof,
) -> _ValidatedBindingProof:
    """Validate exact proof authority, topology, member, and live identities."""
    # pylint: disable=unidiomatic-typecheck
    try:
        if type(proof) is not ImmutableBindingProof:
            raise ValueError("invalid proof type")
        path_type = type(Path())
        if any(type(value) is not path_type for value in (
            proof.copied_source, proof.protected_source, proof.destination
        )):
            raise ValueError("invalid proof path type")
        if any(type(value) is not str for value in (
            proof.descriptor_attestation,
            proof.descriptor_identity,
            proof.member_role,
            proof.member_path,
            proof.collision_category,
        )):
            raise ValueError("invalid proof scalar type")
        if (
            re.fullmatch(r"[0-9a-f]{64}", proof.descriptor_identity) is None
            or proof.member_role != "native_runtime"
            or not proof.member_path.isdecimal()
            or str(int(proof.member_path)) != proof.member_path
            or proof.collision_category != "vitest_inferred_runtime"
        ):
            raise ValueError("invalid proof authority")
        payload, descriptor_identity = _parse_vitest_descriptor_attestation(
            proof.descriptor_attestation
        )
        if descriptor_identity != proof.descriptor_identity:
            raise ValueError("descriptor identity mismatch")
        native_members = [
            member for member in payload["members"]
            if member["role"] == "native_runtime"
        ]
        member_index = int(proof.member_path)
        if member_index >= len(native_members):
            raise ValueError("descriptor member is absent")
        member = native_members[member_index]
        if member["path"] != proof.member_path or member["kind"] != "file":
            raise ValueError("descriptor member mismatch")
        copied = proof.copied_source.resolve(strict=True)
        protected = proof.protected_source.resolve(strict=True)
        destination = proof.destination
        if (
            copied != proof.copied_source
            or protected != proof.protected_source
            or destination != protected
            or payload["native_runtime"][member_index] != str(protected)
        ):
            raise ValueError("proof destination topology mismatch")
        for path in (copied, protected):
            metadata = path.lstat()
            if not stat.S_ISREG(metadata.st_mode) or stat.S_ISLNK(metadata.st_mode):
                raise ValueError("proof source is not a regular file")
        digest = member["digest"]
        mode = member["mode"]
        if not (
            _regular_file_matches(copied, digest, mode)
            and _regular_file_matches(protected, digest, mode)
        ):
            raise ValueError("proof member identity mismatch")
        return _ValidatedBindingProof(
            copied, protected, destination,
            proof.descriptor_attestation, descriptor_identity,
            proof.member_role, proof.member_path, proof.collision_category,
            digest, mode,
        )
    except (AttributeError, json.JSONDecodeError, OSError, TypeError, ValueError) as exc:
        raise RuntimeError("protected sandbox immutable binding proof is malformed") from exc


_IMMUTABLE_STAGING_SOURCE = r'''
def _immutable_failure():
    raise RuntimeError("protected sandbox immutable binding proof failed at staging")

def _canonical_staging_json(value):
    return json.dumps(value,sort_keys=True,separators=(",",":"))

def _validated_candidate_identity(encoded,argv):
    if type(encoded) is not str or not encoded or len(encoded.encode("utf-8"))>1024:
        _immutable_failure()
    try: identity=json.loads(encoded)
    except (TypeError,ValueError): _immutable_failure()
    if type(identity) is not dict or set(identity)!={"schema","uid","gid"} or encoded!=_canonical_staging_json(identity):
        _immutable_failure()
    uid=identity["uid"]; gid=identity["gid"]
    if type(identity["schema"]) is not str or identity["schema"]!="pdd-candidate-identity-v1":
        _immutable_failure()
    if type(uid) is not int or not 0<uid<=0xfffffffe or type(gid) is not int or not 0<=gid<=0xfffffffe:
        _immutable_failure()
    if os.geteuid()!=0 or os.getegid()!=0 or os.environ.get("SUDO_UID")!=str(uid) or os.environ.get("SUDO_GID")!=str(gid):
        _immutable_failure()
    if type(argv) is not list or any(type(value) is not str for value in argv):
        _immutable_failure()
    try: separator=argv.index("--")
    except ValueError: _immutable_failure()
    expected=["--reuid",str(uid),"--regid",str(gid),"--clear-groups","--"]
    if argv[separator+2:separator+8]!=expected:
        _immutable_failure()
    return uid,gid

def _staging_member(member):
    if type(member) is not dict or set(member)!={"role","path","kind","mode","digest","target"}:
        _immutable_failure()
    role=member["role"]; relative=member["path"]; kind=member["kind"]
    mode=member["mode"]; digest=member["digest"]; target=member["target"]
    if type(role) is not str or role not in {"launcher","entrypoint","dependencies","native_runtime","lockfile"}:
        _immutable_failure()
    if type(relative) is not str or not relative or len(relative)>4096:
        _immutable_failure()
    parsed=pathlib.PurePosixPath(relative)
    if parsed.is_absolute() or ".." in parsed.parts or parsed.as_posix()!=relative:
        _immutable_failure()
    if type(kind) is not str or kind not in {"file","directory","symlink"}:
        _immutable_failure()
    if type(mode) is not int or not 0<=mode<=0o777:
        _immutable_failure()
    if kind=="file":
        if type(digest) is not str or len(digest)!=64 or any(value not in "0123456789abcdef" for value in digest) or target is not None:
            _immutable_failure()
    elif kind=="directory":
        if digest is not None or target is not None: _immutable_failure()
    elif digest is not None or type(target) is not str or not target or len(target)>4096:
        _immutable_failure()
    return member

def _staging_attestation(encoded,expected_identity):
    if type(encoded) is not str or not encoded or len(encoded.encode("utf-8"))>4194304:
        _immutable_failure()
    try: payload=json.loads(encoded)
    except (TypeError,ValueError): _immutable_failure()
    if type(payload) is not dict or set(payload)!={"schema","adapter","members","native_runtime","launch_policy"}:
        _immutable_failure()
    if type(payload["schema"]) is not str or payload["schema"]!="pdd-vitest-toolchain-attestation-v1" or type(payload["adapter"]) is not str or payload["adapter"]!="vitest":
        _immutable_failure()
    policy=payload["launch_policy"]
    if type(policy) is not dict or set(policy)!={"linux_wasm_trap_handler_disabled"} or type(policy["linux_wasm_trap_handler_disabled"]) is not bool:
        _immutable_failure()
    members=payload["members"]
    if type(members) is not list or not members: _immutable_failure()
    members=[_staging_member(member) for member in members]
    keys=[(member["role"],member["path"]) for member in members]
    if keys!=sorted(keys) or len(keys)!=len(set(keys)):
        _immutable_failure()
    if {"launcher","entrypoint","dependencies","native_runtime","lockfile"}-{member["role"] for member in members}:
        _immutable_failure()
    native=[member for member in members if member["role"]=="native_runtime"]
    destinations=payload["native_runtime"]
    if type(destinations) is not list or not destinations or len(destinations)!=len(native):
        _immutable_failure()
    for index,(value,member) in enumerate(zip(destinations,native,strict=True)):
        if type(value) is not str or not value or len(value)>4096 or member["path"]!=str(index):
            _immutable_failure()
        if str(_canonical_staging_path(value))!=value:
            _immutable_failure()
    if encoded!=_canonical_staging_json(payload): _immutable_failure()
    members_identity=hashlib.sha256(_canonical_staging_json(members).encode("utf-8")).hexdigest()
    identity=hashlib.sha256(_canonical_staging_json({"members":members_identity,"launch_policy":policy}).encode("utf-8")).hexdigest()
    if type(expected_identity) is not str or identity!=expected_identity:
        _immutable_failure()
    return payload,native

def _canonical_staging_path(value):
    if type(value) is not str or not value or len(value)>4096:
        _immutable_failure()
    path=pathlib.Path(value)
    try: metadata=path.lstat(); canonical=path.resolve(strict=True)
    except OSError: _immutable_failure()
    if not path.is_absolute() or canonical!=path or not stat.S_ISREG(metadata.st_mode) or stat.S_ISLNK(metadata.st_mode):
        _immutable_failure()
    return path

def _verified_staging_fd(path,digest,mode,uid=None,gid=None):
    try: descriptor=os.open(path,os.O_RDONLY|getattr(os,"O_NOFOLLOW",0)|os.O_CLOEXEC)
    except OSError: _immutable_failure()
    try:
        before=os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or stat.S_IMODE(before.st_mode)!=mode:
            _immutable_failure()
        if uid is not None and (before.st_uid!=uid or before.st_gid!=gid):
            _immutable_failure()
        actual=hashlib.sha256()
        while True:
            chunk=os.read(descriptor,1048576)
            if not chunk: break
            actual.update(chunk)
        after=os.fstat(descriptor)
        before_identity=(before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)
        after_identity=(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns)
        if before_identity!=after_identity or actual.hexdigest()!=digest:
            _immutable_failure()
        os.lseek(descriptor,0,os.SEEK_SET)
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise

def _stage_immutable_snapshot(encoded,target,candidate_uid,candidate_gid):
    if type(encoded) is not str or not encoded or len(encoded.encode("utf-8"))>8388608:
        _immutable_failure()
    try: record=json.loads(encoded)
    except (TypeError,ValueError): _immutable_failure()
    fields={"schema","source_index","copied_source","protected_source","destination","descriptor_attestation","descriptor_identity","member_role","member_path","collision_category"}
    if type(record) is not dict or set(record)!=fields or encoded!=_canonical_staging_json(record):
        _immutable_failure()
    if type(record["schema"]) is not str or record["schema"]!="pdd-immutable-binding-record-v1":
        _immutable_failure()
    if type(candidate_uid) is not int or not 0<candidate_uid<=0xfffffffe or type(candidate_gid) is not int or not 0<=candidate_gid<=0xfffffffe:
        _immutable_failure()
    if type(record["source_index"]) is not int or record["source_index"]<0:
        _immutable_failure()
    for name in fields-{"source_index"}:
        if type(record[name]) is not str: _immutable_failure()
    if record["member_role"]!="native_runtime" or not record["member_path"].isdecimal() or str(int(record["member_path"]))!=record["member_path"] or record["collision_category"]!="vitest_inferred_runtime":
        _immutable_failure()
    payload,native=_staging_attestation(record["descriptor_attestation"],record["descriptor_identity"])
    index=int(record["member_path"])
    if index>=len(native): _immutable_failure()
    member=native[index]
    if member["path"]!=record["member_path"] or member["kind"]!="file":
        _immutable_failure()
    copied=_canonical_staging_path(record["copied_source"])
    protected=_canonical_staging_path(record["protected_source"])
    if record["destination"]!=str(protected) or payload["native_runtime"][index]!=str(protected):
        _immutable_failure()
    copied_fd=_verified_staging_fd(copied,member["digest"],member["mode"])
    protected_fd=_verified_staging_fd(protected,member["digest"],member["mode"])
    target_fd=None
    try:
        target_fd=os.open(target,os.O_WRONLY|os.O_TRUNC|getattr(os,"O_NOFOLLOW",0)|os.O_CLOEXEC)
        actual=hashlib.sha256()
        while True:
            chunk=os.read(copied_fd,1048576)
            if not chunk: break
            actual.update(chunk); os.write(target_fd,chunk)
        if actual.hexdigest()!=member["digest"]: _immutable_failure()
        os.fchown(target_fd,candidate_uid,candidate_gid)
        os.fchmod(target_fd,member["mode"]); os.fsync(target_fd)
    except OSError:
        _immutable_failure()
    finally:
        if target_fd is not None: os.close(target_fd)
        os.close(protected_fd); os.close(copied_fd)
    snapshot_fd=_verified_staging_fd(target,member["digest"],member["mode"],candidate_uid,candidate_gid)
    os.close(snapshot_fd)
    return record["source_index"]
'''.strip()


def _scope_unit_name() -> str:
    """Return an unguessable unit name reserved to one supervisor invocation."""
    return f"pdd-validator-{uuid.uuid4().hex}.scope"


def _validated_scope_unit(unit_name: str) -> str:
    """Reject any unit spelling that could target another systemd object."""
    if _SCOPE_PATTERN.fullmatch(unit_name) is None:
        raise RuntimeError("invalid protected scope unit name")
    return unit_name


def _trusted_executable(name: str) -> Path:
    """Resolve one regular executable from the fixed trusted root PATH."""
    value = shutil.which(name, path=_TRUSTED_ROOT_PATH)
    if value is None:
        raise RuntimeError(f"protected sandbox requires trusted {name}")
    try:
        path = Path(value).resolve(strict=True)
    except OSError as exc:
        raise RuntimeError(f"protected sandbox cannot resolve trusted {name}") from exc
    if not path.is_file() or not os.access(path, os.X_OK):
        raise RuntimeError(f"protected sandbox trusted {name} is not executable")
    return path


def _trusted_tools() -> _TrustedTools:
    """Resolve the complete privileged toolchain once for probe and execution."""
    return _TrustedTools(**{
        name.replace("-", "_"): _trusted_executable(name)
        for name in (
            "bwrap", "mount", "setpriv", "sudo", "systemctl", "systemd-run",
            "umount", "unshare",
        )
    })


def _linked_libraries(path: Path) -> tuple[Path, ...]:
    """Resolve loader-visible and physical paths for ELF dependencies."""
    if not sys.platform.startswith("linux"):
        return ()
    try:
        result = subprocess.run(
            ["ldd", str(path)], capture_output=True, text=True, check=False,
            timeout=_TRUSTED_COMMAND_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError("trusted ldd command timed out") from exc
    libraries: set[Path] = set()
    for line in result.stdout.splitlines():
        fields = line.strip().split()
        candidates = (
            fields[2:3] if len(fields) >= 3 and fields[1:2] == ["=>"] else fields[:1]
        )
        for value in candidates:
            candidate = Path(value)
            if candidate.is_absolute() and candidate.is_file():
                libraries.add(candidate)
                # The dynamic loader may retain the /lib alias while the host
                # mount operation follows it to /usr/lib.  Bind both spellings
                # so the empty namespace contains the loader's lookup path and
                # the resolved dependency used by the host mount.
                libraries.add(candidate.resolve())
    return tuple(sorted(libraries))


def _runtime_directories() -> tuple[tuple[str, Path], ...]:
    """Return Python directories whose complete readable contents are mounted."""
    locations = sysconfig.get_paths()
    labels = {
        "stdlib": locations.get("stdlib"),
        "platstdlib": locations.get("platstdlib"),
        "purelib": locations.get("purelib"),
        "platlib": locations.get("platlib"),
    }
    candidates = []
    for label, value in labels.items():
        if not value:
            continue
        path = Path(value).resolve()
        if path.is_dir() and path not in {item[1] for item in candidates}:
            candidates.append((label, path))
    result = []
    for label, path in sorted(candidates, key=lambda item: len(item[1].parts)):
        if any(path.is_relative_to(parent) for _parent_label, parent in result):
            continue
        result.append((label, path))
    result = [
        (f"python-runtime/{label}", path) for label, path in result
    ]
    return tuple(result)


@lru_cache(maxsize=1)
def released_runtime_closure_paths() -> tuple[tuple[str, Path], ...]:
    """Return every regular file exposed by the sandbox with logical names."""
    entries: dict[str, Path] = {}
    native: set[Path] = {_SUPERVISOR_EXECUTABLE.resolve()}
    for label, directory in _runtime_directories():
        for path in sorted(directory.rglob("*")):
            if path.is_file() and not path.is_symlink():
                entries[f"{label}/{path.relative_to(directory).as_posix()}"] = path
                if path.suffix in {".so", ".dylib"}:
                    native.add(path)
    sandbox_commands = {}
    if sys.platform.startswith("linux"):
        for name in (
            "bwrap", "mount", "setpriv", "sudo", "systemctl", "systemd-run",
            "umount", "unshare",
        ):
            if shutil.which(name, path=_TRUSTED_ROOT_PATH):
                sandbox_commands[name] = _trusted_executable(name)
    for name, value in sandbox_commands.items():
        path = Path(value).resolve()
        entries[f"sandbox/{name}"] = path
        native.add(path)
    entries["interpreter/python"] = _SUPERVISOR_EXECUTABLE.resolve()
    for path in sorted(native):
        for library in _linked_libraries(path):
            entries.setdefault(
                f"native/{library.as_posix().lstrip('/')}", library
            )
    return tuple(sorted(entries.items()))


def _runtime_roots(command: list[str], cwd: Path) -> tuple[Path, ...]:
    """Return the measured runtime closure plus the checker working directory."""
    roots: set[Path] = {cwd.resolve()}
    directories = tuple(directory for _label, directory in _runtime_directories())
    roots.update(directories)
    executables = (
        _SUPERVISOR_EXECUTABLE, Path(shutil.which(command[0]) or command[0]),
    )
    for executable in executables:
        resolved_executable = executable.resolve()
        if not executable.is_relative_to(cwd):
            roots.add(executable)
        if not resolved_executable.is_relative_to(cwd):
            roots.add(resolved_executable)
    for _label, path in released_runtime_closure_paths():
        if path.name in {
            "bwrap", "setpriv", "sudo", "systemctl", "systemd-run", "mount", "umount",
        } or any(
            path.is_relative_to(directory) for directory in directories
        ):
            continue
        roots.add(path)
    return tuple(sorted(roots, key=lambda item: (len(item.parts), str(item))))


def _sandbox_library_path(environment: dict[str, str]) -> str:
    """Return loader search directories derived only from the measured closure."""
    directories = []
    for label, path in released_runtime_closure_paths():
        if label.startswith("native/"):
            directories.append(str(path.parent))
    directories.append(str(Path(sys.prefix) / "lib"))
    directories.extend(
        item for item in environment.get("LD_LIBRARY_PATH", "").split(os.pathsep)
        if item
    )
    return os.pathsep.join(dict.fromkeys(directories))


def _validate_limits(limits: SupervisorLimits) -> None:
    """Require exact positive integers for every authoritative numeric limit."""
    # Exact built-in integers reject bool and authority-confusing subclasses.
    # pylint: disable=unidiomatic-typecheck
    if any(
        type(value) is not int or value <= 0 for value in vars(limits).values()
    ):
        raise RuntimeError("invalid protected supervisor limits")
    # pylint: enable=unidiomatic-typecheck


def _limited_command(command: list[str], limits: SupervisorLimits) -> list[str]:
    """Apply non-raiseable POSIX limits after the namespace uid drop."""
    _validate_limits(limits)
    script = (
        "import os,resource,sys;"
        "v=[int(x) for x in sys.argv[1:5]];"
        "resource.setrlimit(resource.RLIMIT_AS,(v[0],v[0]));"
        "resource.setrlimit(resource.RLIMIT_CPU,(v[1],v[1]));"
        "resource.setrlimit(resource.RLIMIT_FSIZE,(v[2],v[2]));"
        "resource.setrlimit(resource.RLIMIT_NOFILE,(v[3],v[3]));"
        "os.execvpe(sys.argv[5],sys.argv[5:],os.environ)"
    )
    return [str(_SUPERVISOR_EXECUTABLE), "-c", script, str(limits.max_virtual_memory_bytes),
            str(limits.max_cpu_seconds), str(limits.max_writable_bytes), "256", *command]


def _staged_bwrap(
    argv: list[str], sources: list[Path], path_tokens: list[str], *,
    writable_roots: tuple[Path, ...], writable_specs: list[tuple[str, int, str]],
    immutable_binding_proofs: tuple[str, ...],
    candidate_identity: str,
    unit_name: str, control_directory: Path, limits: SupervisorLimits,
    candidate_timeout: float, tools: _TrustedTools,
) -> tuple[list[str], _ScopePlan]:
    """Build one scope-held helper that releases Bubblewrap after verification."""
    # pylint: disable=too-many-locals
    unit_name = _validated_scope_unit(unit_name)
    staging_root = control_directory / "binds"
    source_targets = tuple(
        control_directory / "binds" / str(index) for index in range(len(sources))
    )
    fifo_source_indices = []
    for index, value in enumerate(argv):
        if (
            value == str(_FRAMEWORK_OBSERVATION_PATH)
            and index >= 2
            and argv[index - 2] == "--bind"
            and argv[index - 1] in path_tokens
        ):
            fifo_source_indices.append(path_tokens.index(argv[index - 1]))
    if len(fifo_source_indices) > 1:
        raise RuntimeError("protected sandbox has ambiguous observation staging")
    helper = "\n".join((
        "import hashlib,json,math,os,pathlib,select,shutil,stat,subprocess,sys,time",
        "if len(sys.argv)!=13: raise RuntimeError('invalid protected helper protocol')",
        "control=pathlib.Path(sys.argv[1]); mount=sys.argv[2]; umount=sys.argv[3]",
        "candidate_identity=sys.argv[4]; proof_records=json.loads(sys.argv[5])",
        "writable_roots=[pathlib.Path(value) for value in json.loads(sys.argv[6])]",
        "writable_specs=json.loads(sys.argv[7])",
        "path_tokens=json.loads(sys.argv[8]); "
        "argv=json.loads(sys.argv[9]); paths=json.loads(sys.argv[10])",
        "fifo_indices=json.loads(sys.argv[11])",
        "limits=json.loads(sys.argv[12])",
        "targets=[control/'binds'/str(index) for index in range(len(paths))]",
        "staged=[]; result=None; timed_out=False; cleanup_error=None; pid=None",
        "scope_cgroup=None; monitor_cgroup=None; candidate_cgroup=None",
        _PIDFD_PROTOCOL_SOURCE.strip(),
        _IMMUTABLE_STAGING_SOURCE,
        "candidate_uid,candidate_gid="
        "_validated_candidate_identity(candidate_identity,argv)",
        "def wait_for(name):",
        " path=control/name",
        " while not path.exists(): time.sleep(.01)",
        "def own_cgroup():",
        " lines=pathlib.Path('/proc/self/cgroup').read_text(encoding='ascii').splitlines()",
        " relative=next((line[3:] for line in lines if line.startswith('0::')),None)",
        " if not relative: raise RuntimeError('protected scope has no cgroup-v2 membership')",
        " source=pathlib.Path('/sys/fs/cgroup')/relative.lstrip('/')",
        " if source == pathlib.Path('/sys/fs/cgroup') or not source.is_dir(): "
        "raise RuntimeError('protected scope cgroup is invalid')",
        " return source",
        "def flat_values(path):",
        " values={}",
        " for line in path.read_text(encoding='ascii').splitlines():",
        "  fields=line.split()",
        "  if len(fields)!=2 or fields[0] in values: "
        "raise RuntimeError(f'invalid cgroup event file: {path.name}')",
        "  values[fields[0]]=fields[1]",
        " return values",
        "def wait_candidate_empty():",
        " deadline=time.monotonic()+limits['trusted_timeout']",
        " while time.monotonic()<deadline:",
        "  if flat_values(candidate_cgroup/'cgroup.events').get('populated')=='0': return",
        "  time.sleep(.01)",
        " raise RuntimeError('candidate cgroup remained populated')",
        "def kill_candidate_leaf():",
        " (candidate_cgroup/'cgroup.kill').write_text('1',encoding='ascii')",
        " wait_candidate_empty()",
        "def configure_candidate_leaf():",
        " global scope_cgroup,monitor_cgroup,candidate_cgroup",
        " scope_cgroup=own_cgroup()",
        " monitor_cgroup=scope_cgroup/'monitor'",
        " candidate_cgroup=scope_cgroup/'candidate'",
        " monitor_cgroup.mkdir(mode=0o755); monitor_cgroup.chmod(0o755)",
        " candidate_cgroup.mkdir(mode=0o755); candidate_cgroup.chmod(0o755)",
        " (monitor_cgroup/'cgroup.procs').write_text(str(os.getpid()),encoding='ascii')",
        " available=set((scope_cgroup/'cgroup.controllers').read_text("
        "encoding='ascii').split())",
        " if not {'memory','pids'}<=available: "
        "raise RuntimeError('delegated cgroup controllers unavailable')",
        " (scope_cgroup/'cgroup.subtree_control').write_text("
        "'+memory +pids',encoding='ascii')",
        " enabled=set((scope_cgroup/'cgroup.subtree_control').read_text("
        "encoding='ascii').split())",
        " if not {'memory','pids'}<=enabled: "
        "raise RuntimeError('delegated cgroup controllers not enabled')",
        " (candidate_cgroup/'memory.max').write_text(str(limits['memory']),encoding='ascii')",
        " (candidate_cgroup/'memory.swap.max').write_text('0',encoding='ascii')",
        " (candidate_cgroup/'memory.oom.group').write_text('1',encoding='ascii')",
        " (candidate_cgroup/'pids.max').write_text(str(limits['pids']),encoding='ascii')",
        " kill_file=candidate_cgroup/'cgroup.kill'",
        " if not kill_file.exists(): raise RuntimeError('candidate cgroup.kill unavailable')",
        " kill_file.write_text('1',encoding='ascii')",
        " wait_candidate_empty()",
        "def validate_tree(root):",
        " total=0",
        " for path in (root,*root.rglob('*')):",
        "  metadata=path.lstat()",
        "  if stat.S_ISLNK(metadata.st_mode): "
        "raise RuntimeError('writable tree contains symlink')",
        "  if stat.S_ISREG(metadata.st_mode): total+=metadata.st_size",
        "  elif not stat.S_ISDIR(metadata.st_mode): "
        "raise RuntimeError('writable tree contains special file')",
        " return total",
        "def copy_owned(source,target):",
        " if source.is_dir(): shutil.copytree(source,target)",
        " else: shutil.copy2(source,target)",
        " pairs=[(source,target)]",
        " if source.is_dir(): pairs.extend((item,target/item.relative_to(source)) "
        "for item in source.rglob('*'))",
        " for original,copied in pairs:",
        "  metadata=original.stat(follow_symlinks=False)",
        "  os.chown(copied,metadata.st_uid,metadata.st_gid,follow_symlinks=False)",
        "try:",
        " staging_root=control/'binds'",
        " subprocess.run([mount,'-t','tmpfs','-o',"
        "f\"size={limits['staging']},mode=0700,nosuid,nodev\",'tmpfs',"
        "str(staging_root)],check=True,timeout=limits['trusted_timeout'])",
        " staged.append(staging_root)",
        " mount_lines=pathlib.Path('/proc/self/mountinfo').read_text("
        "encoding='utf-8').splitlines()",
        " mount_fields=[line.split() for line in mount_lines]",
        " staging_mount=next((fields for fields in mount_fields if len(fields)>6 and "
        "pathlib.Path(fields[4])==staging_root),None)",
        " if staging_mount is None or '-' not in staging_mount or "
        "staging_mount[staging_mount.index('-')+1]!='tmpfs': "
        "raise RuntimeError('protected staging tmpfs mount probe failed')",
        " if type(proof_records) is not list or "
        "any(type(value) is not str for value in proof_records): "
        "raise RuntimeError('invalid immutable binding proof protocol')",
        " proof_by_index={}",
        " for encoded in proof_records:",
        "  try: preliminary=json.loads(encoded); source_index=preliminary['source_index']",
        "  except (TypeError,ValueError,KeyError): _immutable_failure()",
        "  if type(source_index) is not int or source_index<0 or "
        "source_index>=len(paths) or source_index in proof_by_index: "
        "_immutable_failure()",
        "  proof_by_index[source_index]=encoded",
        " if type(fifo_indices) is not list or len(fifo_indices)>1 or "
        "any(type(value) is not int or value<0 or value>=len(paths) "
        "for value in fifo_indices): "
        "raise RuntimeError('invalid protected FIFO staging protocol')",
        " for index,(source,target) in enumerate(zip(paths,targets)):",
        "  metadata=pathlib.Path(source).lstat()",
        "  if index in proof_by_index or stat.S_ISREG(metadata.st_mode): target.touch(mode=0o600)",
        "  elif stat.S_ISDIR(metadata.st_mode): target.mkdir(mode=0o700)",
        "  elif index in fifo_indices and stat.S_ISFIFO(metadata.st_mode): "
        "os.mkfifo(target,mode=0o600)",
        "  else: raise RuntimeError('protected staging source type is invalid')",
        " writable_target=control/'binds'/'writable'",
        " writable_target.mkdir(mode=0o700)",
        " cgroup_target=control/'binds'/'cgroup'",
        " cgroup_target.mkdir(mode=0o700)",
        " subprocess.run([mount,'-t','tmpfs','-o',"
        "f\"size={limits['writable']},mode=0700,nosuid,nodev\",'tmpfs',"
        "str(writable_target)],check=True,timeout=limits['trusted_timeout'])",
        " staged.append(writable_target)",
        " mount_lines=pathlib.Path('/proc/self/mountinfo').read_text("
        "encoding='utf-8').splitlines()",
        " mount_fields=[line.split() for line in mount_lines]",
        " mounted=next((fields for fields in mount_fields if len(fields)>6 and "
        "pathlib.Path(fields[4])==writable_target),None)",
        " if mounted is None or '-' not in mounted or "
        "mounted[mounted.index('-')+1]!='tmpfs': "
        "raise RuntimeError('writable tmpfs mount probe failed')",
        " capacity=os.statvfs(writable_target).f_blocks*"
        "os.statvfs(writable_target).f_frsize",
        " if capacity > limits['writable']+os.sysconf('SC_PAGE_SIZE'): "
        "raise RuntimeError('writable tmpfs size probe failed')",
        " writable_paths=[]",
        " for index,source in enumerate(writable_roots):",
        "  target=writable_target/str(index); copy_owned(source,target); "
        "writable_paths.append(target)",
        " if sum(validate_tree(path) for path in writable_paths) > "
        "limits['writable']: raise RuntimeError('initial writable quota exceeded')",
        " for index,(source,target) in enumerate(zip(paths,targets)):",
        "  if index in proof_by_index:",
        "   if _stage_immutable_snapshot(proof_by_index[index],target,"
        "candidate_uid,candidate_gid)!=index: _immutable_failure()",
        "  else:",
        "   subprocess.run([mount,'--bind',source,str(target)],check=True,"
        "timeout=limits['trusted_timeout'])",
        "   staged.append(target)",
        " path_map={token:str(targets[index]) for index,token in enumerate(path_tokens)}",
        " for token,index,relative in writable_specs: "
        "path_map[token]=str(writable_paths[index]/relative)",
        " argv=[path_map.get(value,value) for value in argv]",
        " configure_candidate_leaf()",
        " subprocess.run([mount,'--bind',str(candidate_cgroup),str(cgroup_target)],"
        "check=True,timeout=limits['trusted_timeout'])",
        " staged.append(cgroup_target)",
        " subprocess.run([umount,str(cgroup_target)],check=True,"
        "timeout=limits['trusted_timeout'])",
        " staged.pop()",
        " subprocess.run([mount,'--bind',str(candidate_cgroup),str(cgroup_target)],"
        "check=True,timeout=limits['trusted_timeout'])",
        " staged.append(cgroup_target)",
        " argv=[str(cgroup_target) if value == '@PDD-CGROUP@' else value for value in argv]",
        " (control/'ready').write_text('ready',encoding='ascii')",
        " wait_for('start')",
        " release_read,release_write=os.pipe()",
        " pid=os.fork()",
        " if pid == 0:",
        "  os.close(release_write)",
        "  try:",
        "   if os.read(release_read,1)!=b'1': os._exit(125)",
        "   os.close(release_read)",
        "   os.execvpe(argv[0],argv,os.environ)",
        "  except OSError: os._exit(125)",
        " os.close(release_read)",
        " (candidate_cgroup/'cgroup.procs').write_text(str(pid),encoding='ascii')",
        " members=(candidate_cgroup/'cgroup.procs').read_text(encoding='ascii').split()",
        " if str(pid) not in members: raise RuntimeError('candidate cgroup placement failed')",
        " os.write(release_write,b'1'); os.close(release_write)",
        " result,timed_out=_supervise_candidate(pid,limits['timeout'])",
        " kill_candidate_leaf()",
        " record={'version':1,'state':'terminal','returncode':result,"
        "'timed_out':timed_out}",
        " candidate=control/'candidate.tmp'",
        " candidate.write_text(json.dumps(record),encoding='ascii')",
        " os.replace(candidate,control/'candidate.json')",
        " if sum(validate_tree(path) for path in writable_paths) > "
        "limits['writable']: raise RuntimeError('final writable quota exceeded')",
        " temporary=control/'result.tmp'",
        " temporary.write_text(json.dumps(record),encoding='ascii')",
        " os.replace(temporary,control/'result.json')",
        " wait_for('finish')",
        "finally:",
        " if pid is not None and result is None:",
        "  try: os.kill(pid,9)",
        "  except ProcessLookupError: pass",
        "  try: os.waitpid(pid,0)",
        "  except ChildProcessError: pass",
        " for target in reversed(staged):",
        "  try:",
        "   completed=subprocess.run([umount,str(target)],capture_output=True,"
        "text=True,check=False,timeout=limits['trusted_timeout'])",
        "  except subprocess.TimeoutExpired:",
        "   cleanup_error='umount timed out'; continue",
        "  if completed.returncode != 0: cleanup_error=completed.stderr or 'umount failed'",
        " if candidate_cgroup is not None and candidate_cgroup.exists():",
        "  try: kill_candidate_leaf(); candidate_cgroup.rmdir()",
        "  except (OSError,RuntimeError) as error: cleanup_error=str(error)",
        " if scope_cgroup is not None:",
        "  try:",
        "   (scope_cgroup/'cgroup.subtree_control').write_text("
        "'-memory -pids',encoding='ascii')",
        "   (scope_cgroup/'cgroup.procs').write_text(str(os.getpid()),encoding='ascii')",
        "   if monitor_cgroup is not None: monitor_cgroup.rmdir()",
        "  except OSError as error: cleanup_error=str(error)",
        "if cleanup_error:",
        " (control/'cleanup-error').write_text(cleanup_error,encoding='utf-8')",
        " raise SystemExit(125)",
        "raise SystemExit(result if result is not None and result >= 0 else "
        "(128-result if result is not None else 125))",
    ))
    plan = _ScopePlan(
        unit_name, control_directory, helper, tuple(argv), tuple(sources),
        (staging_root, *source_targets, control_directory / "binds" / "writable",
         control_directory / "binds" / "cgroup"), tools,
        immutable_binding_proofs,
    )
    command = [
        str(tools.sudo), "-n", "-E", str(tools.systemd_run), "--scope", "--quiet",
        f"--unit={unit_name}", "--property=Delegate=yes",
        "--property=MemoryMax=infinity", "--property=MemorySwapMax=infinity",
        "--property=TasksMax=infinity", "--property=OOMPolicy=continue",
        "--property=KillMode=control-group", "--",
        str(tools.unshare), "--mount", "--propagation", "private", "--wd", "/",
        str(_SUPERVISOR_EXECUTABLE), "-c", helper, str(control_directory),
        str(tools.mount), str(tools.umount),
        candidate_identity,
        json.dumps(list(immutable_binding_proofs)),
        json.dumps([str(path) for path in writable_roots]), json.dumps(writable_specs),
        json.dumps(path_tokens), json.dumps(argv),
        json.dumps([str(path) for path in sources]),
        json.dumps(fifo_source_indices),
        json.dumps({"memory": limits.max_memory_bytes, "pids": limits.max_processes,
                    "writable": limits.max_writable_bytes,
                    "staging": max(
                        1024 * 1024,
                        sum(path.stat().st_size for path in sources if path.is_file())
                        + 1024 * 1024,
                    ),
                    "timeout": candidate_timeout,
                    "trusted_timeout": _TRUSTED_COMMAND_SECONDS}),
    ]
    return command, plan


def _framework_observation_command(
    command: list[str], result_fd: int, source_path: Path,
) -> list[str]:
    """Open the namespace-local standard-framework observation channel."""
    script = (
        "import os,sys;"
        "path=sys.argv[1];target=int(sys.argv[2]);"
        "source=os.open(path,os.O_WRONLY|os.O_CLOEXEC);"
        "os.dup2(source,target);"
        "os.close(source) if source!=target else None;"
        "os.execvpe(sys.argv[3],sys.argv[3:],os.environ)"
    )
    return [str(_SUPERVISOR_EXECUTABLE), "-c", script,
            str(source_path), str(result_fd), *command]

def _supervised_descendants(token: str) -> set[int]:
    """Find descendants carrying the unforgeable per-run environment marker."""
    found: set[int] = set()
    if sys.platform.startswith("linux"):
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit():
                continue
            try:
                environment = (entry / "environ").read_bytes()
            except (OSError, PermissionError):
                continue
            if f"PDD_SUPERVISION_TOKEN={token}".encode() in environment.split(b"\0"):
                found.add(int(entry.name))
        return found
    try:
        listing = subprocess.run(
            ["ps", "eww", "-axo", "pid=,command="], capture_output=True,
            text=True, check=False, timeout=_TRUSTED_COMMAND_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError("trusted process inventory timed out") from exc
    marker = f"PDD_SUPERVISION_TOKEN={token}"
    for line in listing.stdout.splitlines():
        if marker not in line:
            continue
        try:
            found.add(int(line.strip().split(None, 1)[0]))
        except (ValueError, IndexError):
            continue
    return found


def _process_identity(pid: int) -> str | None:
    """Return a stable Linux process identity, including kernel start time."""
    if sys.platform.startswith("linux"):
        try:
            stat_fields = Path(f"/proc/{pid}/stat").read_text(
                encoding="utf-8"
            ).rsplit(")", 1)[1].split()
            return stat_fields[19]
        except (OSError, IndexError):
            return None
    return None


def _load_candidate_record(path: Path) -> _CandidateRecord:
    """Read one strict bounded terminal record from the protected helper."""
    try:
        encoded = path.read_bytes()
        if len(encoded) > 4096:
            raise RuntimeError("protected candidate record is invalid")
        payload = json.loads(encoded)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise RuntimeError("protected candidate record is invalid") from exc
    expected_keys = {"version", "state", "returncode", "timed_out"}
    if not isinstance(payload, dict) or set(payload) != expected_keys:
        raise RuntimeError("protected candidate record is invalid")
    returncode = payload["returncode"]
    timed_out = payload["timed_out"]
    valid_header = (
        type(payload["version"]) is int  # pylint: disable=unidiomatic-typecheck
        and payload["version"] == 1
        and payload["state"] == "terminal"
    )
    valid_returncode = (
        isinstance(returncode, int)
        and not isinstance(returncode, bool)
        and -255 <= returncode <= 255
    )
    valid_timeout = isinstance(timed_out, bool) and (
        not timed_out or returncode == 124
    )
    if not (valid_header and valid_returncode and valid_timeout):
        raise RuntimeError("protected candidate record is invalid")
    return _CandidateRecord(returncode, timed_out)


def _live_processes(pids: dict[int, str | None]) -> set[int]:
    """Return only observations whose stable process identity still matches."""
    live = set()
    for pid, identity in pids.items():
        if identity is None or _process_identity(pid) != identity:
            continue
        try:
            os.kill(pid, 0)
        except (ProcessLookupError, PermissionError):
            continue
        live.add(pid)
    return live


def _writable_size(roots: tuple[Path, ...]) -> int:
    """Measure logical bytes for diagnostics, failing on incomplete traversal."""
    total = 0
    try:
        for root in roots:
            paths = (root, *root.rglob("*")) if root.is_dir() else (root,)
            for path in paths:
                metadata = path.lstat()
                if stat.S_ISLNK(metadata.st_mode):
                    raise RuntimeError("writable accounting rejects symlinks")
                if stat.S_ISREG(metadata.st_mode):
                    total += metadata.st_size
                elif not stat.S_ISDIR(metadata.st_mode):
                    raise RuntimeError("writable accounting rejects special files")
    except OSError as exc:
        raise RuntimeError("writable accounting failed") from exc
    return total


def _writable_storage_roots(paths: tuple[Path, ...]) -> tuple[Path, ...]:
    """Return disjoint real roots mirrored into one bounded writable filesystem."""
    resolved = []
    for path in paths:
        try:
            if path.is_symlink():
                raise RuntimeError("writable storage root cannot be a symlink")
            value = path.resolve(strict=True)
        except OSError as exc:
            raise RuntimeError("writable storage root is unavailable") from exc
        if not (value.is_dir() or value.is_file()):
            raise RuntimeError("writable storage root must be a regular file or directory")
        resolved.append(value)
    roots = []
    for path in sorted(set(resolved), key=lambda item: (len(item.parts), str(item))):
        if not any(path == root or path.is_relative_to(root) for root in roots):
            roots.append(path)
    return tuple(roots)


def _root_environment() -> dict[str, str]:
    """Return the fixed environment used for every privileged tool invocation."""
    return {"PATH": _TRUSTED_ROOT_PATH, "LANG": "C", "LC_ALL": "C"}


def _root_run(
    tools: _TrustedTools, arguments: list[str], *, check: bool = False,
) -> subprocess.CompletedProcess[str]:
    """Invoke systemctl through the exact sudo/systemctl identities already probed."""
    try:
        return subprocess.run(
            [str(tools.sudo), "-n", str(tools.systemctl), *arguments],
            capture_output=True, text=True, check=check, env=_root_environment(),
            timeout=_TRUSTED_COMMAND_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError("trusted systemctl command timed out") from exc


def _scope_properties(unit_name: str, tools: _TrustedTools) -> dict[str, str]:
    """Read authoritative transient-scope state without collecting the unit."""
    unit_name = _validated_scope_unit(unit_name)
    names = (
        "LoadState", "ActiveState", "ControlGroup", "MemoryMax",
        "MemorySwapMax", "TasksMax", "OOMPolicy", "KillMode", "Delegate", "Result",
        "OOMKilled",
    )
    completed = _root_run(
        tools, ["show", unit_name, *(f"--property={name}" for name in names)],
    )
    if completed.returncode != 0:
        raise RuntimeError(
            "protected scope probe failed: " + (completed.stderr.strip() or "systemctl show failed")
        )
    properties = {}
    for line in completed.stdout.splitlines():
        name, separator, value = line.partition("=")
        if separator:
            properties[name] = value
    return properties


def _scope_cgroup(properties: dict[str, str]) -> Path:
    """Validate the systemd-owned workload cgroup path."""
    relative = properties.get("ControlGroup", "")
    if not relative.startswith("/") or relative == "/" or ".." in Path(relative).parts:
        raise RuntimeError("protected scope has invalid ControlGroup")
    root = Path("/sys/fs/cgroup")
    path = root / relative.lstrip("/")
    try:
        if not path.resolve(strict=True).is_relative_to(root.resolve(strict=True)):
            raise RuntimeError("protected scope escaped cgroup-v2 root")
    except OSError as exc:
        raise RuntimeError("protected scope cgroup does not exist") from exc
    return path


def _cgroup_events(cgroup: Path, filename: str) -> dict[str, int]:
    """Read one kernel cgroup event file as non-negative counters."""
    try:
        lines = (cgroup / filename).read_text(encoding="ascii").splitlines()
        events = {}
        for line in lines:
            fields = line.split()
            if len(fields) != 2 or fields[0] in events:
                raise ValueError("invalid event record")
            events[fields[0]] = int(fields[1])
    except (OSError, ValueError) as exc:
        raise RuntimeError(f"protected scope cannot read {filename}") from exc
    required = {"memory.events": {"oom", "oom_kill"}, "pids.events": {"max"}}
    missing = required.get(filename, set()) - events.keys()
    if missing:
        raise RuntimeError(
            f"protected scope has invalid {filename}: missing {','.join(sorted(missing))}"
        )
    if any(value < 0 for value in events.values()):
        raise RuntimeError(f"protected scope has invalid {filename}")
    return events


def _probe_scope(
    plan: _ScopePlan, limits: SupervisorLimits,
) -> tuple[Path, dict[str, int], dict[str, int]]:
    # pylint: disable=too-many-locals,too-many-boolean-expressions
    """Prove the delegated candidate leaf limits before releasing the child."""
    properties = _scope_properties(plan.unit_name, plan.tools)
    expected = {
        "LoadState": "loaded", "ActiveState": "active",
        "MemoryMax": "infinity", "MemorySwapMax": "infinity",
        "TasksMax": "infinity", "OOMPolicy": "continue",
        "KillMode": "control-group", "Delegate": "yes",
    }
    differences = [
        f"{name}={properties.get(name, '<missing>')}"
        for name, value in expected.items() if properties.get(name) != value
    ]
    if differences:
        raise RuntimeError("protected scope properties unverified: " + ", ".join(differences))
    parent = _scope_cgroup(properties)
    cgroup = parent / "candidate"
    monitor = parent / "monitor"
    try:
        parent_resolved = parent.resolve(strict=True)
        metadata = cgroup.lstat()
        monitor_metadata = monitor.lstat()
        if (
            not stat.S_ISDIR(metadata.st_mode)
            or stat.S_ISLNK(metadata.st_mode)
            or stat.S_IMODE(metadata.st_mode) != 0o755
            or not stat.S_ISDIR(monitor_metadata.st_mode)
            or stat.S_ISLNK(monitor_metadata.st_mode)
            or stat.S_IMODE(monitor_metadata.st_mode) != 0o755
            or cgroup.resolve(strict=True).parent != parent_resolved
            or monitor.resolve(strict=True).parent != parent_resolved
        ):
            raise RuntimeError("protected scope candidate leaf topology is invalid")
        parent_members = (parent / "cgroup.procs").read_text(encoding="ascii").split()
        monitor_members = (monitor / "cgroup.procs").read_text(encoding="ascii").split()
        candidate_members = (cgroup / "cgroup.procs").read_text(encoding="ascii").split()
    except OSError as exc:
        raise RuntimeError("protected scope candidate leaf is unavailable") from exc
    if (
        parent_members
        or len(monitor_members) != 1
        or not monitor_members[0].isdecimal()
        or candidate_members
    ):
        raise RuntimeError("protected scope candidate leaf membership is invalid")
    kernel_limits = {
        "memory.max": str(limits.max_memory_bytes), "memory.swap.max": "0",
        "memory.oom.group": "1", "pids.max": str(limits.max_processes),
    }
    for filename, expected_value in kernel_limits.items():
        try:
            actual = (cgroup / filename).read_text(encoding="ascii").strip()
        except OSError as exc:
            raise RuntimeError(f"protected scope cannot read {filename}") from exc
        if actual != expected_value:
            raise RuntimeError(
                f"protected scope kernel limit mismatch: {filename}={actual}"
            )
    return cgroup, _cgroup_events(cgroup, "memory.events"), _cgroup_events(cgroup, "pids.events")


def _stop_scope(unit_name: str, tools: _TrustedTools) -> None:
    """Kill the exact whole scope and prove that systemd removed it."""
    unit_name = _validated_scope_unit(unit_name)

    def absent() -> bool:
        completed = _root_run(tools, ["show", unit_name, "--property=LoadState"])
        if completed.returncode != 0:
            raise RuntimeError(
                "protected scope teardown failed: "
                + (completed.stderr.strip() or "cannot probe scope")
            )
        output = completed.stdout.strip()
        if not output.startswith("LoadState=") or "\n" in output:
            raise RuntimeError("protected scope teardown returned invalid load state")
        return output == "LoadState=not-found"

    if absent():
        return
    errors = []
    for arguments in (
        ["kill", "--kill-whom=all", "--signal=SIGKILL", unit_name],
        ["stop", unit_name],
        ["reset-failed", unit_name],
    ):
        completed = _root_run(tools, arguments)
        if completed.returncode != 0:
            errors.append(completed.stderr.strip() or " ".join(arguments) + " failed")
        if absent():
            if errors:
                # An exact post-action not-found probe proves narrow collection;
                # command errors are stale state only when the unit is now absent.
                errors.clear()
            return
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        if absent():
            break
        time.sleep(.05)
    else:
        errors.append("scope unit was not removed")
    if errors:
        raise RuntimeError("protected scope teardown failed: " + "; ".join(errors))


def _prepare_staging(plan: _ScopePlan) -> None:
    """Create only the mountpoint for the helper-owned staging tmpfs."""
    binds = plan.control_directory / "binds"
    binds.mkdir(mode=0o700)


def _mounted_paths() -> set[Path]:
    """Return host mountpoints using the kernel's escaped mount table."""
    paths = set()
    try:
        lines = Path("/proc/self/mountinfo").read_text(encoding="utf-8").splitlines()
    except OSError as exc:
        raise RuntimeError("protected mount table is unavailable") from exc
    for line in lines:
        fields = line.split()
        if len(fields) > 4:
            paths.add(Path(fields[4].replace("\\040", " ").replace("\\134", "\\")))
    return paths


def _cleanup_staging(plan: _ScopePlan) -> None:
    """Remove any helper mounts left after authoritative scope termination."""
    errors = []
    for target in reversed(plan.staging_targets):
        if target not in _mounted_paths():
            continue
        try:
            completed = subprocess.run(
                [str(plan.tools.sudo), "-n", str(plan.tools.umount), str(target)],
                capture_output=True, text=True, check=False, env=_root_environment(),
                timeout=_TRUSTED_COMMAND_SECONDS,
            )
        except subprocess.TimeoutExpired:
            errors.append(f"trusted umount timed out for {target}")
            continue
        if completed.returncode != 0:
            errors.append(completed.stderr.strip() or f"cannot unmount {target}")
    if any(target in _mounted_paths() for target in plan.staging_targets):
        errors.append("protected bind staging remains mounted")
    if errors:
        raise RuntimeError("protected scope staging cleanup failed: " + "; ".join(errors))


def _sandbox_command(
    command: list[str], writable_roots: tuple[Path, ...], *, cwd: Path | None = None,
    limits: SupervisorLimits = SupervisorLimits(),
    candidate_timeout: float = 300,
    readable_roots: tuple[Path, ...] = (),
    readable_bindings: tuple[tuple[Path, Path], ...] = (),
    immutable_binding_proofs: tuple[ImmutableBindingProof, ...] = (),
    writable_bindings: tuple[tuple[Path, Path], ...] = (),
    result_fifo: Path | None = None,
    result_fd: int = 198,
    unit_name: str | None = None,
    control_directory: Path | None = None,
) -> tuple[list[str], _ScopePlan]:
    # pylint: disable=too-many-locals,too-many-branches,too-many-statements
    # pylint: disable=unidiomatic-typecheck
    """Return an explicitly detected macOS/Linux sandbox command."""
    _validate_limits(limits)
    if sys.platform == "darwin":
        raise RuntimeError(
            "unsupported protected sandbox: macOS cannot prove process lifetime isolation"
        )
    if sys.platform.startswith("linux"):
        if (
            isinstance(candidate_timeout, bool)
            or not isinstance(candidate_timeout, (int, float))
            or candidate_timeout <= 0
            or not math.isfinite(candidate_timeout)
        ):
            raise RuntimeError("protected sandbox requires a finite positive timeout")
        tools = _trusted_tools()
        candidate_uid = os.getuid()
        candidate_gid = os.getgid()
        if type(candidate_uid) is not int or type(candidate_gid) is not int:
            raise RuntimeError("protected sandbox caller identity is invalid")
        if candidate_uid == 0:
            raise RuntimeError(
                "protected sandbox requires a non-root caller so process limits "
                "remain kernel-enforced"
            )
        if not 0<candidate_uid<=0xfffffffe or not 0<=candidate_gid<=0xfffffffe:
            raise RuntimeError("protected sandbox caller identity is invalid")
        candidate_identity = _canonical_json({
            "schema": _CANDIDATE_IDENTITY_SCHEMA,
            "uid": candidate_uid,
            "gid": candidate_gid,
        })
        try:
            privilege_probe = subprocess.run(
                [str(tools.sudo), "-n", str(_SUPERVISOR_EXECUTABLE), "-c", "pass"],
                capture_output=True, check=False, env=_root_environment(),
                timeout=_TRUSTED_COMMAND_SECONDS,
            )
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError("trusted sudo probe timed out") from exc
        if privilege_probe.returncode != 0:
            raise RuntimeError("protected sandbox requires privileged bind staging")
        workdir = (cwd or Path.cwd()).resolve()
        writable_sources = tuple(
            source for source, _destination in writable_bindings
        ) + writable_roots
        storage_roots = _writable_storage_roots(writable_sources)
        if _writable_size(storage_roots) > limits.max_writable_bytes:
            raise RuntimeError("initial writable quota exceeded")
        argv = [str(tools.bwrap), "--unshare-ipc", "--unshare-pid", "--unshare-net",
                "--unshare-uts", "--unshare-cgroup", "--die-with-parent", "--new-session",
                "--tmpfs", "/", "--proc", "/proc", "--dir", "/tmp",
                "--dir", "/sys", "--dir", "/sys/fs", "--dir", "/sys/fs/cgroup"]
        sources: list[Path] = []
        path_tokens: list[str] = []
        writable_specs: list[tuple[str, int, str]] = []
        destination_dirs = {Path("/tmp")}
        mounted: dict[Path, tuple[str, Path, str, int | None]] = {}
        proofs: dict[tuple[Path, Path, Path], _ValidatedBindingProof] = {}
        raw_proofs: dict[tuple[Path, Path, Path], ImmutableBindingProof] = {}
        for proof in immutable_binding_proofs:
            try:
                if type(proof) is not ImmutableBindingProof:
                    raise ValueError("invalid proof type")
                path_type = type(Path())
                if any(type(value) is not path_type for value in (
                    proof.copied_source, proof.protected_source, proof.destination
                )):
                    raise ValueError("invalid proof path type")
                raw_key = (
                    proof.copied_source.resolve(strict=True),
                    proof.protected_source.resolve(strict=True),
                    proof.destination,
                )
            except (AttributeError, OSError, TypeError, ValueError) as exc:
                raise RuntimeError(
                    "protected sandbox immutable binding proof is malformed"
                ) from exc
            if raw_key in raw_proofs:
                kind = "duplicate" if raw_proofs[raw_key] == proof else "ambiguous"
                raise RuntimeError(
                    f"protected sandbox has {kind} immutable binding proofs"
                )
            raw_proofs[raw_key] = proof
            validated = _validate_immutable_binding_proof(proof)
            key = (
                validated.copied_source,
                validated.protected_source,
                validated.destination,
            )
            proofs[key] = validated
        consumed_proofs: set[tuple[Path, Path, Path]] = set()
        accepted_records: list[str] = []

        def stage_source(source: Path, writable: bool = False) -> tuple[str, int | None]:
            token = f"@PDD-PATH-{uuid.uuid4().hex}@"
            if writable:
                for index, root in enumerate(storage_roots):
                    if source == root or source.is_relative_to(root):
                        relative = source.relative_to(root).as_posix() or "."
                        writable_specs.append((token, index, relative))
                        return token, None
                raise RuntimeError("writable source is outside bounded storage")
            source_index = len(sources)
            sources.append(source)
            path_tokens.append(token)
            return token, source_index

        def ensure_destination_parent(destination: Path) -> None:
            missing = []
            parent = destination.parent
            while parent != Path("/") and parent not in destination_dirs:
                missing.append(parent)
                parent = parent.parent
            for directory in reversed(missing):
                argv.extend(("--dir", str(directory)))
                destination_dirs.add(directory)

        def bind(
            option: str, source: Path, destination: Path | None = None, *,
            category: str,
        ) -> None:
            destination = destination or source
            resolved_source = source.resolve()
            previous = mounted.get(destination)
            if previous is not None and previous[:2] == (option, resolved_source):
                return
            if previous is not None and previous[1] != resolved_source:
                key = (previous[1], resolved_source, destination)
                proof = proofs.get(key)
                if (
                    option == "--ro-bind"
                    and previous[0] == "--ro-bind"
                    and previous[2] == "declared_readable"
                    and category == "inferred_runtime"
                    and proof is not None
                ):
                    if key in consumed_proofs:
                        raise RuntimeError(
                            "protected sandbox immutable binding proof was multiply consumed"
                        )
                    if previous[3] is None:
                        raise RuntimeError(
                            "protected sandbox immutable binding proof has no source"
                        )
                    consumed_proofs.add(key)
                    accepted_records.append(_canonical_json({
                        "schema": _BINDING_RECORD_SCHEMA,
                        "source_index": previous[3],
                        "copied_source": str(proof.copied_source),
                        "protected_source": str(proof.protected_source),
                        "destination": str(proof.destination),
                        "descriptor_attestation": proof.descriptor_attestation,
                        "descriptor_identity": proof.descriptor_identity,
                        "member_role": proof.member_role,
                        "member_path": proof.member_path,
                        "collision_category": proof.collision_category,
                    }))
                    return
                raise RuntimeError(
                    f"protected sandbox has conflicting bindings for {destination}"
                )
            token, source_index = stage_source(source, option == "--bind")
            mounted[destination] = (
                option, resolved_source, category, source_index
            )
            ensure_destination_parent(destination)
            argv.extend((option, token, str(destination)))
            if destination.is_dir():
                destination_dirs.add(destination)

        for source, destination in writable_bindings:
            bind("--bind", source.resolve(), destination, category="writable")
        for source, destination in readable_bindings:
            bind(
                "--ro-bind", source.resolve(), destination,
                category="declared_readable",
            )
        for item in _runtime_roots(command, workdir):
            # A host bind follows symlinks, but the process command and ELF
            # loader retain their original spellings in the new namespace.
            bind(
                "--ro-bind", item.resolve(), item, category="inferred_runtime"
            )
        # The helper replaces this placeholder with only its systemd scope.
        argv.extend(("--ro-bind", "@PDD-CGROUP@", "/sys/fs/cgroup"))
        # ``setpriv`` executes after the namespace root is installed, so bind
        # it and its ELF closure directly even when PATH resolution differs.
        if tools.setpriv:
            for item in (tools.setpriv, *_linked_libraries(tools.setpriv)):
                bind("--ro-bind", item.resolve(), item, category="trusted_runtime")
        for item in readable_roots:
            bind("--ro-bind", item.resolve(), category="readable_root")
        if result_fifo is not None:
            observation_source = result_fifo.resolve(strict=True)
            if not stat.S_ISFIFO(observation_source.lstat().st_mode):
                raise RuntimeError("framework observation channel must be a FIFO")
            if _FRAMEWORK_OBSERVATION_PATH in mounted:
                raise RuntimeError("framework observation destination conflicts")
            mounted[_FRAMEWORK_OBSERVATION_PATH] = (
                "--bind", observation_source, "observation", len(sources)
            )
            ensure_destination_parent(_FRAMEWORK_OBSERVATION_PATH)
            argv.extend(
                (
                    "--bind",
                    stage_source(observation_source)[0],
                    str(_FRAMEWORK_OBSERVATION_PATH),
                )
            )
        argv.extend(("--dev", "/dev"))
        for item in writable_roots:
            bind("--bind", item.resolve(), category="writable")
        argv.extend(("--chdir", str(workdir)))
        drop = (
            [str(tools.setpriv), "--reuid", str(candidate_uid),
             "--regid", str(candidate_gid),
             "--clear-groups", "--"]
        )
        sandboxed = _limited_command(command, limits)
        if result_fifo is not None:
            sandboxed = _framework_observation_command(
                sandboxed, result_fd, _FRAMEWORK_OBSERVATION_PATH
            )
        argv.extend(("--", *drop, *sandboxed))
        if consumed_proofs != proofs.keys():
            raise RuntimeError("protected sandbox has unused immutable binding proof")
        return _staged_bwrap(
            argv, sources, path_tokens, writable_roots=storage_roots,
            writable_specs=writable_specs,
            immutable_binding_proofs=tuple(accepted_records),
            candidate_identity=candidate_identity,
            unit_name=unit_name or _scope_unit_name(),
            control_directory=control_directory or (
                Path(tempfile.gettempdir()) / f"pdd-scope-{uuid.uuid4().hex}"
            ),
            limits=limits, candidate_timeout=candidate_timeout, tools=tools,
        )
    raise RuntimeError("unsupported sandbox platform or mechanism")


def run_supervised(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...],
    limits: SupervisorLimits = SupervisorLimits(),
    readable_roots: tuple[Path, ...] = (),
    readable_bindings: tuple[tuple[Path, Path], ...] = (),
    immutable_binding_proofs: tuple[ImmutableBindingProof, ...] = (),
    writable_bindings: tuple[tuple[Path, Path], ...] = (),
    temp_directory: Path | None = None,
    result_fifo: Path | None = None,
    result_fd: int = 198,
) -> tuple[subprocess.CompletedProcess[str], bool]:
    """Run after proving one delegated candidate leaf, then remove its scope."""
    # pylint: disable=consider-using-with,too-many-locals,too-many-branches,too-many-statements
    token = uuid.uuid4().hex
    unit_name = _scope_unit_name()
    stdout_buffer = bytearray()
    stderr_buffer = bytearray()
    diagnostics = bytearray()
    output_lock = threading.Lock()
    output_size = 0
    output_overflow = False
    output_threads: list[threading.Thread] = []
    candidate_timed_out = False
    failed_closed = False
    surviving = False
    candidate_returncode: int | None = None
    candidate_record: _CandidateRecord | None = None
    process: subprocess.Popen[bytes] | None = None
    plan: _ScopePlan | None = None
    cgroup: Path | None = None
    memory_before: dict[str, int] = {}
    pids_before: dict[str, int] = {}
    tracked: dict[int, str | None] = {}
    phase = "construction"

    def add_diagnostic(value: str) -> None:
        data = value.encode("utf-8", errors="replace")
        remaining = max(0, limits.max_output_bytes - len(diagnostics))
        diagnostics.extend(data[:remaining])

    def drain_output(stream, buffer: bytearray) -> None:
        nonlocal output_size, output_overflow
        while chunk := stream.read(65536):
            with output_lock:
                remaining = max(0, limits.max_output_bytes - output_size)
                buffer.extend(chunk[:remaining])
                output_size += len(chunk)
                if len(chunk) > remaining:
                    output_overflow = True

    def limit_error() -> str | None:
        with output_lock:
            exceeded = output_overflow
            observed = output_size
        if exceeded:
            return (
                "protected supervisor output quota exceeded: "
                f"{observed}>{limits.max_output_bytes}"
            )
        return None

    def fail_for_limit() -> bool:
        nonlocal failed_closed
        error = limit_error()
        if error is None:
            return False
        failed_closed = True
        add_diagnostic(f"protected supervisor phase={phase}: {error}\n")
        return True

    def record_events() -> None:
        if cgroup is None:
            return
        memory_after = _cgroup_events(cgroup, "memory.events")
        pids_after = _cgroup_events(cgroup, "pids.events")
        oom_delta = max(
            memory_after["oom"] - memory_before["oom"],
            memory_after["oom_kill"] - memory_before["oom_kill"],
        )
        pids_delta = pids_after["max"] - pids_before["max"]
        if oom_delta > 0:
            add_diagnostic(f"cgroup memory.events oom delta={oom_delta}\n")
        if pids_delta > 0:
            add_diagnostic(f"cgroup pids.events max delta={pids_delta}\n")

    try:
        with tempfile.TemporaryDirectory(prefix="pdd-scope-") as control_value:
            control = Path(control_value)
            try:
                argv, plan = _sandbox_command(
                    command, writable_roots, cwd=cwd,
                    limits=limits, readable_roots=readable_roots,
                    readable_bindings=readable_bindings,
                    immutable_binding_proofs=immutable_binding_proofs,
                    writable_bindings=writable_bindings,
                    result_fifo=result_fifo, result_fd=result_fd,
                    candidate_timeout=timeout,
                    unit_name=unit_name, control_directory=control,
                )
                _prepare_staging(plan)
            except (OSError, RuntimeError) as exc:
                return subprocess.CompletedProcess(
                    command, 125, "", f"protected supervisor phase=construction: {exc}"
                ), False
            sandbox_environment = env | {
                "PATH": _TRUSTED_ROOT_PATH,
                "PYTHONDONTWRITEBYTECODE": "1",
                "PDD_SUPERVISION_TOKEN": token,
                "TMPDIR": str(temp_directory or writable_roots[0].resolve()),
                "TEMP": str(temp_directory or writable_roots[0].resolve()),
                "TMP": str(temp_directory or writable_roots[0].resolve()),
            }
            library_path = _sandbox_library_path(env)
            if library_path:
                sandbox_environment["LD_LIBRARY_PATH"] = library_path
            try:
                process = subprocess.Popen(
                    argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    env=sandbox_environment, start_new_session=True,
                )
            except OSError as exc:
                try:
                    _cleanup_staging(plan)
                except RuntimeError as cleanup_exc:
                    return subprocess.CompletedProcess(
                        command, 125, "",
                        "protected supervisor phase=launch: "
                        f"{exc}; cleanup failed: {cleanup_exc}",
                    ), False
                return subprocess.CompletedProcess(
                    command, 125, "", f"protected supervisor phase=launch: {exc}"
                ), False

            assert process.stdout is not None and process.stderr is not None
            output_threads = [
                threading.Thread(
                    target=drain_output, args=(process.stdout, stdout_buffer), daemon=True
                ),
                threading.Thread(
                    target=drain_output, args=(process.stderr, stderr_buffer), daemon=True
                ),
            ]
            for output_thread in output_threads:
                output_thread.start()

            setup_deadline = time.monotonic() + _TRUSTED_SETUP_SECONDS
            phase = "scope-setup"
            try:
                while not (control / "ready").exists():
                    if process.poll() is not None:
                        raise RuntimeError("protected scope exited before verification")
                    if time.monotonic() >= setup_deadline:
                        failed_closed = True
                        add_diagnostic(
                            "protected supervisor phase=scope-setup: "
                            "scope construction did not finish\n"
                        )
                        break
                    if fail_for_limit():
                        break
                    time.sleep(.01)
                if not failed_closed:
                    cgroup, memory_before, pids_before = _probe_scope(plan, limits)
                    (control / "start").write_text("start", encoding="ascii")
                    phase = "candidate-execution"
                    helper_deadline = (
                        time.monotonic() + timeout + _TRUSTED_POSTPROCESS_SECONDS
                    )
                    while not (control / "candidate.json").exists():
                        if failed_closed:
                            break
                        if process.poll() is not None:
                            break
                        if time.monotonic() >= helper_deadline:
                            failed_closed = True
                            add_diagnostic(
                                "protected supervisor phase=candidate-execution: "
                                "protected candidate record did not arrive\n"
                            )
                            break
                        if fail_for_limit():
                            break
                        time.sleep(.01)
                    if (control / "candidate.json").exists():
                        candidate_record = _load_candidate_record(
                            control / "candidate.json"
                        )
                        phase = "trusted-postprocessing"
                        postprocess_deadline = min(
                            helper_deadline,
                            time.monotonic() + _TRUSTED_POSTPROCESS_SECONDS,
                        )
                        while not (control / "result.json").exists():
                            if process.poll() is not None:
                                break
                            if time.monotonic() >= postprocess_deadline:
                                failed_closed = True
                                add_diagnostic(
                                    "protected supervisor trusted postprocessing "
                                    "did not finish\n"
                                )
                                break
                            if fail_for_limit():
                                break
                            time.sleep(.01)
                    if (control / "result.json").exists():
                        phase = "result-handoff"
                        result_record = _load_candidate_record(control / "result.json")
                        if result_record != candidate_record:
                            raise RuntimeError("candidate result changed during handoff")
                        candidate_returncode = result_record.returncode
                        candidate_timed_out = result_record.timed_out
                        fail_for_limit()
                        record_events()
                    if (
                        candidate_record is None
                        and not failed_closed
                    ):
                        failed_closed = True
                        add_diagnostic(
                            "protected supervisor phase=candidate-execution: "
                            "scope produced no protected candidate record\n"
                        )
                    elif (
                        not (control / "result.json").exists()
                        and not failed_closed
                    ):
                        failed_closed = True
                        add_diagnostic(
                            "protected supervisor phase=trusted-postprocessing: "
                            "scope produced no validated result\n"
                        )
                    if (
                        candidate_returncode == 124
                        and not candidate_timed_out
                        and (control / "result.json").exists()
                        and not failed_closed
                    ):
                        failed_closed = True
                        add_diagnostic(
                            "protected supervisor phase=result-handoff: "
                            "candidate used reserved exit status 124\n"
                        )
                    if process.poll() is None and not failed_closed:
                        (control / "finish").write_text("finish", encoding="ascii")
                        try:
                            remaining = max(0, postprocess_deadline - time.monotonic())
                            process.wait(timeout=remaining)
                        except subprocess.TimeoutExpired:
                            failed_closed = True
                            add_diagnostic(
                                "protected supervisor result-handoff did not finish\n"
                            )
                    if (
                        candidate_returncode is not None
                        and process.poll() is not None
                        and not failed_closed
                    ):
                        expected_helper_exit = (
                            candidate_returncode
                            if candidate_returncode >= 0
                            else 128 - candidate_returncode
                        )
                        if process.returncode != expected_helper_exit:
                            failed_closed = True
                            add_diagnostic(
                                "protected supervisor phase=result-handoff: "
                                "helper exit status mismatch\n"
                            )
                    if (control / "cleanup-error").exists():
                        failed_closed = True
                        add_diagnostic(
                            "protected supervisor phase=mount-cleanup: "
                            "privileged helper cleanup failed\n"
                        )
            except (OSError, ValueError, KeyError, RuntimeError) as exc:
                failed_closed = True
                add_diagnostic(f"protected supervisor phase={phase}: {exc}\n")
            finally:
                if candidate_timed_out:
                    add_diagnostic(
                        "protected supervisor timeout phase=candidate-execution\n"
                    )
                if cgroup is None and process.poll() is None:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    try:
                        process.wait(timeout=_TRUSTED_COMMAND_SECONDS)
                    except subprocess.TimeoutExpired:
                        failed_closed = True
                        add_diagnostic(
                            "protected supervisor phase=scope-cleanup: "
                            "helper did not terminate\n"
                        )
                try:
                    _stop_scope(plan.unit_name, plan.tools)
                except RuntimeError as exc:
                    failed_closed = True
                    add_diagnostic(f"protected supervisor phase=scope-cleanup: {exc}\n")
                if process.poll() is None:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                try:
                    process.wait(timeout=_TRUSTED_COMMAND_SECONDS)
                except subprocess.TimeoutExpired:
                    failed_closed = True
                    add_diagnostic(
                        "protected supervisor phase=scope-cleanup: "
                        "helper did not terminate after scope stop\n"
                    )
                try:
                    _cleanup_staging(plan)
                except RuntimeError as exc:
                    failed_closed = True
                    add_diagnostic(f"protected supervisor phase=mount-cleanup: {exc}\n")
    finally:
        for output_thread in output_threads:
            output_thread.join(timeout=1)
            if output_thread.is_alive():
                failed_closed = True
                add_diagnostic("protected supervisor output drain did not finish\n")
        observed = set()
        if process is not None:
            try:
                observed = _supervised_descendants(token)
                observed.discard(process.pid)
            except RuntimeError as exc:
                failed_closed = True
                add_diagnostic(f"protected supervisor process cleanup failed: {exc}\n")
        for pid in observed:
            tracked.setdefault(pid, _process_identity(pid))
        descendants = _live_processes(tracked)
        if descendants:
            surviving = True
            failed_closed = True
            for pid in descendants:
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

    stdout_bytes = bytes(stdout_buffer)
    remaining = max(0, limits.max_output_bytes - len(stdout_bytes))
    stderr_bytes = bytes(stderr_buffer[:remaining])
    remaining -= len(stderr_bytes)
    stderr_bytes += bytes(diagnostics[:remaining])
    if output_overflow:
        failed_closed = True
    return subprocess.CompletedProcess(
        command,
        125 if failed_closed else (124 if candidate_timed_out else candidate_returncode),
        stdout_bytes.decode("utf-8", errors="replace"),
        stderr_bytes.decode("utf-8", errors="replace"),
    ), surviving
