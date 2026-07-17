"""Fail-closed OS sandbox and complete process-group supervision."""
# pylint: disable=too-many-arguments,too-many-lines,line-too-long

from __future__ import annotations

import hashlib
import base64
import json
import math
import os
import re
import select
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
from enum import Enum
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
_SNAPSHOT_BINDING_SCHEMA = "pdd-snapshot-binding-v1"
_PLAYWRIGHT_AGGREGATE_SCHEMA = "pdd-playwright-snapshot-aggregate-v1"
_PLAYWRIGHT_AGGREGATE_RECORD_SCHEMA = "pdd-playwright-snapshot-aggregate-record-v1"
_CANDIDATE_IDENTITY_SCHEMA = "pdd-candidate-identity-v1"
_DESCRIPTOR_PROTOCOL_MAX_CONTROL_BYTES = 4096
_DESCRIPTOR_PROTOCOL_MAX_RESULT_BYTES = 48 * 1024 * 1024
_DESCRIPTOR_PROTOCOL_MAX_LAUNCH_BYTES = 48 * 1024 * 1024
_STANDARD_ANONYMOUS_AGGREGATE_DIGEST = hashlib.sha256(
    b"pdd-standard-anonymous-observation-v1"
).hexdigest()
_MAX_CANDIDATE_ENVIRONMENT_BYTES = 128 * 1024
_MAX_CANDIDATE_ENVIRONMENT_ENTRIES = 128
_MAX_CANDIDATE_ENVIRONMENT_KEY_BYTES = 128
_MAX_CANDIDATE_ENVIRONMENT_VALUE_BYTES = 32 * 1024
_SNAPSHOT_STAGING_HEADROOM_BYTES = 1024 * 1024
_SNAPSHOT_MEMBER_METADATA_BYTES = 4096
_IMMUTABLE_STAGING_METADATA_BYTES = 4096
_MAX_SNAPSHOT_MEMBER_BYTES = 2 * 1024 * 1024 * 1024
_MAX_STAGING_BYTES = 4 * 1024 * 1024 * 1024
_TERMINATION_HEADER_BYTES = 256
_TERMINATION_HEADER_PREFIX = b"PDD-TERMINATION-V1 "
_VITEST_MEMBER_ROLES = frozenset({
    "launcher", "entrypoint", "dependencies", "native_runtime", "lockfile",
})
_BLOCKED_CANDIDATE_ENV_MARKERS = (
    "API_KEY", "ATTESTATION", "CERTIFICATE", "CREDENTIAL", "PASSWORD",
    "RELEASED_CHECKER", "SECRET", "SIGNER", "SIGNING_KEY", "TOKEN",
)
_CANDIDATE_ENV_KEY = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

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


class TerminationKind(str, Enum):
    """Trusted reason the supervised process stopped."""

    EXIT = "exit"
    SIGNAL = "signal"
    TIMEOUT = "timeout"
    RESOURCE_LIMIT = "resource-limit"
    SANDBOX_ERROR = "sandbox-error"


class InfrastructureFailurePhase(str, Enum):
    """Allowlisted trusted phase in which sandbox infrastructure failed."""

    UNKNOWN = "unknown"
    CONSTRUCTION = "construction"
    LAUNCH = "launch"
    SCOPE_SETUP = "scope-setup"
    CANDIDATE_EXECUTION = "candidate-execution"
    TRUSTED_POSTPROCESSING = "trusted-postprocessing"
    RESULT_HANDOFF = "result-handoff"
    SCOPE_CLEANUP = "scope-cleanup"
    MOUNT_CLEANUP = "mount-cleanup"
    OUTPUT_DRAIN = "output-drain"
    PROCESS_CLEANUP = "process-cleanup"


class ScopeSetupFailureReason(str, Enum):
    """Bounded trusted subreason for a failure before descriptor READY."""

    LAUNCH_EXIT = "launch-exit"
    STAGING_TMPFS = "staging-tmpfs"
    AUTHORITY_TMPFS = "authority-tmpfs"
    STAGING_LAYOUT = "staging-layout"
    WRITABLE_TMPFS = "writable-tmpfs"
    WRITABLE_COPY = "writable-copy"
    BIND_STAGING = "bind-staging"
    CGROUP_CONFIGURE = "cgroup-configure"
    CGROUP_BIND = "cgroup-bind"
    READY_HANDOFF = "ready-handoff"


@dataclass(frozen=True)
class CgroupResourceTelemetry:
    """Trusted deltas from the candidate leaf's kernel event counters."""

    memory_oom_delta: int
    memory_oom_kill_delta: int
    pids_max_delta: int


@dataclass(frozen=True)
class SupervisorTermination:  # pylint: disable=too-many-instance-attributes
    """Typed termination evidence retained outside candidate-controlled output."""

    kind: TerminationKind
    exit_code: int | None = None
    signal_number: int | None = None
    timeout_seconds: int | None = None
    resource_limit: str | None = None
    resource_telemetry: CgroupResourceTelemetry | None = None
    failure_phases: tuple[InfrastructureFailurePhase, ...] = ()
    scope_setup_subreason: ScopeSetupFailureReason | None = None


class SupervisedCompletedProcess(subprocess.CompletedProcess[str]):  # pylint: disable=too-few-public-methods
    """Completed process carrying trusted supervisor termination evidence."""

    termination: SupervisorTermination

    def __init__(
        self,
        args: list[str],
        returncode: int,
        stdout: str,
        stderr: str,
        *,
        termination: SupervisorTermination,
    ) -> None:
        super().__init__(args, returncode, stdout, stderr)
        self.termination = termination


def _supervised_result(
    command: list[str],
    returncode: int,
    stdout: str,
    stderr: str,
    termination: SupervisorTermination,
) -> SupervisedCompletedProcess:
    """Construct one subprocess-compatible result with trusted termination data."""
    return SupervisedCompletedProcess(
        command, returncode, stdout, stderr, termination=termination
    )


def _sandbox_termination(
    failure_phases: tuple[object, ...],
    *,
    resource_telemetry: CgroupResourceTelemetry | None,
    scope_setup_subreason: object = None,
) -> SupervisorTermination:
    """Return fail-closed evidence containing only trusted phase values."""
    phases: list[InfrastructureFailurePhase] = []
    for value in failure_phases[:len(InfrastructureFailurePhase)]:
        phase = (
            value
            if isinstance(value, InfrastructureFailurePhase)
            else InfrastructureFailurePhase.UNKNOWN
        )
        if phase not in phases:
            phases.append(phase)
    if not phases:
        phases.append(InfrastructureFailurePhase.UNKNOWN)
    subreason = (
        scope_setup_subreason
        if (
            isinstance(scope_setup_subreason, ScopeSetupFailureReason)
            and InfrastructureFailurePhase.SCOPE_SETUP in phases
        )
        else None
    )
    return SupervisorTermination(
        TerminationKind.SANDBOX_ERROR,
        exit_code=125,
        resource_telemetry=resource_telemetry,
        failure_phases=tuple(phases),
        scope_setup_subreason=subreason,
    )


def _sandbox_error(
    command: list[str],
    detail: str,
    *,
    failure_phases: tuple[InfrastructureFailurePhase, ...] = (
        InfrastructureFailurePhase.UNKNOWN,
    ),
) -> tuple[SupervisedCompletedProcess, bool]:
    """Return one typed infrastructure failure for trusted supervisor faults."""
    return _supervised_result(
        command, 125, "", detail,
        _sandbox_termination(failure_phases, resource_telemetry=None),
    ), False


def _termination_evidence(
    returncode: int,
    *,
    timed_out: bool,
    timeout_seconds: int,
    resource_limit: str | None,
    resource_telemetry: CgroupResourceTelemetry | None = None,
) -> SupervisorTermination:
    """Classify only termination causes observed by the trusted supervisor."""
    if resource_limit is not None:
        return SupervisorTermination(
            TerminationKind.RESOURCE_LIMIT,
            resource_limit=resource_limit,
            resource_telemetry=resource_telemetry,
        )
    if timed_out:
        return SupervisorTermination(
            TerminationKind.TIMEOUT,
            timeout_seconds=timeout_seconds,
            resource_telemetry=resource_telemetry,
        )
    if returncode < 0:
        return SupervisorTermination(
            TerminationKind.SIGNAL,
            signal_number=-returncode,
            resource_telemetry=resource_telemetry,
        )
    return SupervisorTermination(
        TerminationKind.EXIT,
        exit_code=returncode,
        resource_telemetry=resource_telemetry,
    )


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
class SnapshotBindingProof:
    """Complete no-follow tree identity for one read-only helper snapshot."""

    source: Path
    destination: Path
    attestation: str


@dataclass(frozen=True)
class PlaywrightSnapshotAggregate:
    """Canonical Playwright-only snapshot and observation authority."""

    attestation: str
    digest: str
    accepted_toolchain_identity: str
    result_fd: int


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
    member_size: int


@dataclass(frozen=True)
# pylint: disable-next=too-many-instance-attributes
class _ExecutableIdentity:
    """Immutable identity for one executable crossing the root boundary."""

    path: Path
    stat_identity: tuple[int, int, int, int, int, int]
    sha256: str
    require_root: bool = True

    def payload(self) -> dict[str, object]:
        """Serialize the exact root-side revalidation authority."""
        device, inode, mode, uid, size, mtime_ns = self.stat_identity
        return {
            "path": str(self.path), "device": device, "inode": inode,
            "mode": mode, "uid": uid, "size": size, "mtime_ns": mtime_ns,
            "sha256": self.sha256,
        }


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
    helper_python: Path
    identities: tuple[_ExecutableIdentity, ...]


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
    launch_payload: dict[str, object] | None = None


@dataclass(frozen=True)
class _CandidateRecord:
    """Validated terminal status emitted by the privileged direct-child helper."""

    returncode: int
    timed_out: bool


@dataclass(frozen=True)
class _RootObservationResult:
    """Nonce-bound observation metadata released from the root authority."""

    candidate: _CandidateRecord
    observation_digest: str
    observation_size: int


@dataclass(frozen=True)
class _DescriptorResult:
    """One validated terminal Playwright result carried only by helper descriptors."""

    candidate: _CandidateRecord
    stdout: bytes
    stderr: bytes
    observation: bytes


def _descriptor_frame(payload: dict[str, object], maximum: int) -> bytes:
    """Encode one canonical bounded protocol frame."""
    encoded = _canonical_json(payload).encode("utf-8")
    if len(encoded) > maximum:
        raise RuntimeError("protected descriptor frame exceeded limit")
    return len(encoded).to_bytes(4, "big") + encoded


def _read_descriptor_frame(stream, maximum: int) -> dict[str, object]:
    """Read exactly one canonical bounded JSON frame from a helper descriptor."""
    # Exact built-in objects prevent protocol type subclasses from carrying authority.
    # pylint: disable=unidiomatic-typecheck
    header = stream.read(4)
    if len(header) != 4:
        raise RuntimeError("protected descriptor transport closed")
    size = int.from_bytes(header, "big")
    if not 0 < size <= maximum:
        raise RuntimeError("protected descriptor frame has invalid size")
    encoded = stream.read(size)
    if len(encoded) != size:
        raise RuntimeError("protected descriptor frame is partial")
    try:
        payload = json.loads(encoded)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise RuntimeError("protected descriptor frame is invalid") from exc
    if type(payload) is not dict or _canonical_json(payload).encode("utf-8") != encoded:
        raise RuntimeError("protected descriptor frame is not canonical")
    return payload


def _write_descriptor_frame(stream, payload: dict[str, object], maximum: int) -> None:
    """Write one canonical protocol frame, failing on a short parent handoff."""
    frame = _descriptor_frame(payload, maximum)
    stream.write(frame)
    stream.flush()


def _descriptor_poll(descriptor: int, event: int, deadline: float) -> None:
    """Wait boundedly for one descriptor event."""
    poller = select.poll()
    poller.register(descriptor, event | select.POLLERR | select.POLLHUP)
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise RuntimeError("protected descriptor transport timed out")
        events = poller.poll(max(1, math.ceil(remaining * 1000)))
        if not events:
            continue
        mask = events[0][1]
        if mask & event:
            return
        raise RuntimeError("protected descriptor transport closed")


def _read_descriptor_bytes(descriptor: int, size: int, deadline: float) -> bytes:
    """Read an exact bounded byte count without an indefinite blocking call."""
    chunks: list[bytes] = []
    remaining = size
    while remaining:
        _descriptor_poll(descriptor, select.POLLIN, deadline)
        chunk = os.read(descriptor, remaining)
        if not chunk:
            raise RuntimeError("protected descriptor transport closed")
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)


def _read_descriptor_frame_fd(
    descriptor: int, maximum: int, deadline: float,
) -> dict[str, object]:
    """Read one canonical frame directly from a non-buffered descriptor."""
    header = _read_descriptor_bytes(descriptor, 4, deadline)
    size = int.from_bytes(header, "big")
    if not 0 < size <= maximum:
        raise RuntimeError("protected descriptor frame has invalid size")
    encoded = _read_descriptor_bytes(descriptor, size, deadline)
    try:
        payload = json.loads(encoded)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise RuntimeError("protected descriptor frame is invalid") from exc
    if type(payload) is not dict or _canonical_json(payload).encode() != encoded:  # pylint: disable=unidiomatic-typecheck
        raise RuntimeError("protected descriptor frame is not canonical")
    return payload


def _write_descriptor_bytes(descriptor: int, data: bytes, deadline: float) -> None:
    """Write all bytes with polling and a monotonic deadline."""
    blocking = os.get_blocking(descriptor)
    os.set_blocking(descriptor, False)
    try:
        offset = 0
        while offset < len(data):
            _descriptor_poll(descriptor, select.POLLOUT, deadline)
            try:
                written = os.write(descriptor, data[offset:offset + 65536])
            except BlockingIOError:
                continue
            if written <= 0:
                raise RuntimeError("protected descriptor short write")
            offset += written
    finally:
        os.set_blocking(descriptor, blocking)


def _write_descriptor_frame_fd(
    descriptor: int, payload: dict[str, object], maximum: int, deadline: float,
) -> None:
    """Write one canonical frame without trusting buffered stream progress."""
    _write_descriptor_bytes(descriptor, _descriptor_frame(payload, maximum), deadline)


def _expect_descriptor_eof(descriptor: int, deadline: float) -> None:
    """Require terminal EOF and reject every trailing protocol byte."""
    poller = select.poll()
    poller.register(descriptor, select.POLLIN | select.POLLHUP | select.POLLERR)
    while time.monotonic() < deadline:
        events = poller.poll(max(1, math.ceil((deadline - time.monotonic()) * 1000)))
        if not events:
            continue
        value = os.read(descriptor, 1)
        if value:
            raise RuntimeError("protected descriptor transport has trailing data")
        return
    raise RuntimeError("protected descriptor terminal EOF timed out")


def _descriptor_result(
    payload: object, nonce: str, aggregate_digest: str, maximum: int,
) -> _DescriptorResult:
    """Validate the complete helper result before forwarding any observation bytes."""
    # Exact built-in types and all result bindings are part of the authority grammar.
    # pylint: disable=too-many-boolean-expressions,unidiomatic-typecheck
    expected = {
        "kind", "nonce", "aggregate_digest", "candidate", "stdout", "stderr",
        "observation", "observation_sha256", "observation_size",
    }
    if type(payload) is not dict or set(payload) != expected:
        raise RuntimeError("protected descriptor result is invalid")
    if (
        payload["kind"] != "result"
        or payload["nonce"] != nonce
        or payload["aggregate_digest"] != aggregate_digest
        or type(payload["stdout"]) is not str
        or type(payload["stderr"]) is not str
        or type(payload["observation"]) is not str
        or type(payload["observation_sha256"]) is not str
        or type(payload["observation_size"]) is not int
    ):
        raise RuntimeError("protected descriptor result is invalid")
    try:
        stdout = base64.b64decode(payload["stdout"], validate=True)
        stderr = base64.b64decode(payload["stderr"], validate=True)
        observation = base64.b64decode(payload["observation"], validate=True)
    except (ValueError, TypeError) as exc:
        raise RuntimeError("protected descriptor result is invalid") from exc
    if (
        len(stdout) + len(stderr) > maximum
        or len(observation) > maximum
        or payload["observation_size"] != len(observation)
        or hashlib.sha256(observation).hexdigest() != payload["observation_sha256"]
    ):
        raise RuntimeError("protected descriptor result is invalid")
    return _DescriptorResult(_load_candidate_record_payload(payload["candidate"]), stdout, stderr, observation)


def _scope_setup_error_reason(
    payload: object, nonce: str,
) -> ScopeSetupFailureReason | None:
    """Return one exact helper-authenticated pre-READY failure category."""
    if type(payload) is not dict or set(payload) != {  # pylint: disable=unidiomatic-typecheck
        "kind", "nonce", "reason",
    }:
        return None
    if payload.get("kind") != "setup-error" or payload.get("nonce") != nonce:
        return None
    try:
        return ScopeSetupFailureReason(payload.get("reason"))
    except (TypeError, ValueError):
        return None


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


def _validated_regular_file_size(path: Path, digest: str, mode: int) -> int | None:
    """Return a no-follow validated file size, or ``None`` on identity failure."""
    try:
        descriptor = os.open(
            path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | os.O_CLOEXEC
        )
    except OSError:
        return None
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or stat.S_IMODE(before.st_mode) != mode
        ):
            return None
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
        if not stable or actual.hexdigest() != digest:
            return None
        return before.st_size
    except OSError:
        return None
    finally:
        os.close(descriptor)


def _validate_immutable_binding_proof(
    proof: ImmutableBindingProof,
) -> _ValidatedBindingProof:
    """Validate exact proof authority, topology, member, and live identities."""
    # pylint: disable=too-many-locals,unidiomatic-typecheck
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
        copied_size = _validated_regular_file_size(copied, digest, mode)
        protected_size = _validated_regular_file_size(protected, digest, mode)
        if (
            copied_size is None
            or protected_size is None
            or copied_size != protected_size
            or copied_size > _MAX_STAGING_BYTES
        ):
            raise ValueError("proof member identity mismatch")
        return _ValidatedBindingProof(
            copied, protected, destination,
            proof.descriptor_attestation, descriptor_identity,
            proof.member_role, proof.member_path, proof.collision_category,
            digest, mode, copied_size,
        )
    except (AttributeError, json.JSONDecodeError, OSError, TypeError, ValueError) as exc:
        raise RuntimeError("protected sandbox immutable binding proof is malformed") from exc


def _validate_snapshot_binding_proof(proof: SnapshotBindingProof) -> None:
    """Validate canonical source/destination authority before helper handoff."""
    # Exact built-in types keep the serialized authority unambiguous.
    # pylint: disable=unidiomatic-typecheck,too-many-boolean-expressions
    try:
        if type(proof) is not SnapshotBindingProof:
            raise ValueError("invalid snapshot proof type")
        if type(proof.source) is not type(Path()) or type(proof.destination) is not type(Path()):
            raise ValueError("invalid snapshot proof paths")
        if type(proof.attestation) is not str or len(proof.attestation.encode()) > _MAX_BINDING_ATTESTATION_BYTES:
            raise ValueError("invalid snapshot proof attestation")
        payload = json.loads(proof.attestation)
        if (
            type(payload) is not dict
            or set(payload) != {"schema", "source", "destination", "members"}
            or payload["schema"] != _SNAPSHOT_BINDING_SCHEMA
            or payload["source"] != str(proof.source.resolve(strict=True))
            or payload["destination"] != str(proof.destination)
            or proof.attestation != _canonical_json(payload)
            or type(payload["members"]) is not list
            or not payload["members"]
        ):
            raise ValueError("invalid snapshot proof authority")
        members = payload["members"]
        paths = []
        for member in members:
            if type(member) is not dict or set(member) != {"path", "kind", "mode", "digest", "size", "target"}:
                raise ValueError("invalid snapshot member")
            path = member["path"]
            if type(path) is not str or not path or len(path) > 4096:
                raise ValueError("invalid snapshot member path")
            parsed = PurePosixPath(path)
            if parsed.is_absolute() or ".." in parsed.parts or parsed.as_posix() != path:
                raise ValueError("invalid snapshot member path")
            if member["kind"] not in {"file", "directory", "symlink"} or type(member["mode"]) is not int:
                raise ValueError("invalid snapshot member type")
            size = member["size"]
            if (
                member["kind"] == "file"
                and (type(size) is not int or not 0 <= size <= _MAX_SNAPSHOT_MEMBER_BYTES)
            ) or (member["kind"] != "file" and size is not None):
                raise ValueError("invalid snapshot member size")
            paths.append(path)
        if paths != sorted(paths) or paths[0] != "." or len(paths) != len(set(paths)):
            raise ValueError("non-canonical snapshot members")
    except (AttributeError, OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError("protected sandbox snapshot binding proof is malformed") from exc


def _validate_playwright_snapshot_aggregate(
    aggregate: PlaywrightSnapshotAggregate,
) -> dict[str, object]:
    """Validate Playwright-only aggregate authority before privileged handoff."""
    # pylint: disable=unidiomatic-typecheck,too-many-locals
    try:
        if type(aggregate) is not PlaywrightSnapshotAggregate:
            raise ValueError("invalid aggregate type")
        valid_attestation = (
            type(aggregate.attestation) is str
            and len(aggregate.attestation.encode()) <= _MAX_BINDING_ATTESTATION_BYTES
        )
        valid_identities = (
            type(aggregate.digest) is str
            and re.fullmatch(r"[0-9a-f]{64}", aggregate.digest) is not None
            and type(aggregate.accepted_toolchain_identity) is str
            and re.fullmatch(
                r"[0-9a-f]{64}", aggregate.accepted_toolchain_identity
            ) is not None
        )
        valid_descriptor = (
            type(aggregate.result_fd) is int and 3 <= aggregate.result_fd <= 255
        )
        if not (valid_attestation and valid_identities and valid_descriptor):
            raise ValueError("invalid aggregate scalar")
        payload = json.loads(aggregate.attestation)
        valid_payload = type(payload) is dict and set(payload) == {
            "schema", "toolchain_identity", "checker_identity", "observation", "members",
        }
        valid_authority = valid_payload and (
            payload["schema"] == _PLAYWRIGHT_AGGREGATE_SCHEMA
            and payload["checker_identity"] == aggregate.accepted_toolchain_identity
        )
        valid_encoding = (
            aggregate.attestation == _canonical_json(payload)
            and hashlib.sha256(aggregate.attestation.encode()).hexdigest()
            == aggregate.digest
        )
        if not (valid_authority and valid_encoding):
            raise ValueError("invalid aggregate identity")
        observation = payload["observation"]
        if (
            type(observation) is not dict
            or set(observation) != {
                "role", "transport", "result_fd", "reporter_sha256",
            }
        ):
            raise ValueError("invalid observation authority")
        if (
            observation["role"] != "reporter"
            or observation["transport"] != "anonymous-pipe-v1"
            or observation["result_fd"] != aggregate.result_fd
            or type(observation["reporter_sha256"]) is not str
            or re.fullmatch(r"[0-9a-f]{64}", observation["reporter_sha256"]) is None
        ):
            raise ValueError("invalid observation authority")
        expected_checker = hashlib.sha256(_canonical_json({
            "reporter_sha256": observation["reporter_sha256"],
            "toolchain_identity": payload["toolchain_identity"],
        }).encode()).hexdigest()
        if expected_checker != payload["checker_identity"]:
            raise ValueError("invalid checker identity")
        members = payload["members"]
        if type(members) is not list or not members:
            raise ValueError("invalid aggregate members")
        labels = []
        attestations = []
        for member in members:
            if type(member) is not dict or set(member) != {"role", "attestation"}:
                raise ValueError("invalid aggregate member")
            role = member["role"]
            attestation = member["attestation"]
            native_match = (
                re.fullmatch(r"native_runtime/(0|[1-9][0-9]*)", role)
                if type(role) is str else None
            )
            allowed_role = role in {
                "reporter", "launcher", "browser_runtime", "lockfile",
                "dependencies", "entrypoint",
            } if type(role) is str else False
            if (
                type(role) is not str
                or not (allowed_role or native_match is not None)
                or type(attestation) is not str
            ):
                raise ValueError("invalid aggregate member authority")
            labels.append(role)
            attestations.append(attestation)
        required = {"reporter", "launcher", "browser_runtime", "lockfile", "dependencies"}
        native_labels = sorted(
            int(label.split("/", 1)[1]) for label in labels
            if label.startswith("native_runtime/")
        )
        if (
            len(labels) != len(set(labels))
            or not required <= set(labels)
            or native_labels != list(range(len(native_labels)))
            or not native_labels
            or len(attestations) != len(set(attestations))
        ):
            raise ValueError("incomplete aggregate roles")
        return payload
    except (AttributeError, TypeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError("protected Playwright snapshot aggregate is malformed") from exc


def _snapshot_staging_bytes(
    sources: list[Path], snapshot_records: list[str],
    immutable_records: tuple[tuple[int, _ValidatedBindingProof], ...] = (),
) -> int:
    """Return one bounded tmpfs quota for all validated copied sources."""
    # pylint: disable=too-many-branches,too-many-locals
    # Exact built-in types keep a privileged accounting record unambiguous.
    # pylint: disable=too-many-boolean-expressions,unidiomatic-typecheck
    total = _SNAPSHOT_STAGING_HEADROOM_BYTES
    snapshot_indices: set[int] = set()
    immutable_indices: set[int] = set()
    try:
        for encoded in snapshot_records:
            record = json.loads(encoded)
            payload = json.loads(record["attestation"])
            index = record["source_index"]
            if (  # pylint: disable=unidiomatic-typecheck
                type(index) is not int
                or not 0 <= index < len(sources)
                or index in snapshot_indices
            ):
                raise ValueError("invalid snapshot source index")
            snapshot_indices.add(index)
            members = payload["members"]
            if type(members) is not list:
                raise ValueError("invalid snapshot members")
            total += len(members) * _SNAPSHOT_MEMBER_METADATA_BYTES
            for member in members:
                if type(member) is not dict or member.get("kind") not in {
                    "file", "directory", "symlink"
                }:
                    raise ValueError("invalid snapshot member")
                size = member.get("size")
                if member["kind"] == "file":
                    if type(size) is not int or not 0 <= size <= _MAX_SNAPSHOT_MEMBER_BYTES:
                        raise ValueError("invalid snapshot member size")
                    total += size
                elif size is not None:
                    raise ValueError("invalid snapshot member size")
        for index, proof in immutable_records:
            if (
                type(index) is not int
                or not 0 <= index < len(sources)
                or index in immutable_indices
                or type(proof) is not _ValidatedBindingProof
                or type(proof.member_size) is not int
                or not 0 <= proof.member_size <= _MAX_STAGING_BYTES
            ):
                raise ValueError("invalid immutable staging record")
            immutable_indices.add(index)
            if index not in snapshot_indices:
                total += _IMMUTABLE_STAGING_METADATA_BYTES + proof.member_size
    except (KeyError, OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError("protected snapshot staging quota is invalid") from exc
    if total > _MAX_STAGING_BYTES:
        raise RuntimeError("protected snapshot staging quota exceeds maximum")
    page = os.sysconf("SC_PAGE_SIZE")
    required = ((total + page - 1) // page) * page
    if not 0 < required <= _MAX_STAGING_BYTES:
        raise RuntimeError("protected snapshot staging quota exceeds maximum")
    return required


_SNAPSHOT_STAGING_SOURCE = r'''
def _snapshot_failure():
    raise RuntimeError("protected sandbox snapshot attestation failed at staging")

def _snapshot_canonical_json(value):
    return json.dumps(value,sort_keys=True,separators=(",",":"))

def _snapshot_member_fd(root_fd,relative,directory=False):
    parts=pathlib.PurePosixPath(relative).parts
    descriptor=os.dup(root_fd)
    try:
        for part in parts:
            if part==".": continue
            next_fd=os.open(part,os.O_RDONLY|os.O_CLOEXEC|getattr(os,"O_NOFOLLOW",0)|(os.O_DIRECTORY if directory or part!=parts[-1] else 0),dir_fd=descriptor)
            os.close(descriptor); descriptor=next_fd
        return descriptor
    except BaseException:
        os.close(descriptor); raise

def _snapshot_parent_fd(root_fd,relative):
    parts=pathlib.PurePosixPath(relative).parts
    descriptor=os.dup(root_fd)
    try:
        for part in parts[:-1]:
            if part==".": continue
            next_fd=os.open(part,os.O_RDONLY|os.O_CLOEXEC|os.O_DIRECTORY|getattr(os,"O_NOFOLLOW",0),dir_fd=descriptor)
            os.close(descriptor); descriptor=next_fd
        return descriptor,parts[-1]
    except BaseException:
        os.close(descriptor); raise

def _snapshot_link_is_contained(relative,target):
    if pathlib.PurePosixPath(target).is_absolute(): return False
    parts=[]
    for part in (*pathlib.PurePosixPath(relative).parent.parts,*pathlib.PurePosixPath(target).parts):
        if part in {"","."}: continue
        if part=="..":
            if not parts: return False
            parts.pop()
        else: parts.append(part)
    return True

def _stage_snapshot(encoded,source,target):
    try: record=json.loads(encoded); payload=json.loads(record["attestation"]); payload["source_index"]=record["source_index"]
    except (TypeError,ValueError): _snapshot_failure()
    if type(payload) is not dict or set(payload)!={"schema","source","destination","members","source_index"} or payload["schema"]!="pdd-snapshot-binding-v1" or encoded!=_snapshot_canonical_json(record): _snapshot_failure()
    if payload["source"]!=str(source) or type(payload["members"]) is not list or not payload["members"]: _snapshot_failure()
    members=payload["members"]; names=[]
    for member in members:
        if type(member) is not dict or set(member)!={"path","kind","mode","digest","size","target"}: _snapshot_failure()
        relative=member["path"]; kind=member["kind"]
        parsed=pathlib.PurePosixPath(relative) if type(relative) is str else None
        if not relative or parsed.is_absolute() or ".." in parsed.parts or parsed.as_posix()!=relative or kind not in {"file","directory","symlink"} or type(member["mode"]) is not int: _snapshot_failure()
        if kind=="file" and (type(member["digest"]) is not str or type(member["size"]) is not int or not 0<=member["size"]<=2147483648 or member["target"] is not None): _snapshot_failure()
        if kind=="directory" and (member["digest"] is not None or member["size"] is not None or member["target"] is not None): _snapshot_failure()
        if kind=="symlink" and (member["digest"] is not None or member["size"] is not None or type(member["target"]) is not str or not member["target"] or not _snapshot_link_is_contained(relative,member["target"])): _snapshot_failure()
        names.append(relative)
    if names!=sorted(names) or names[0]!="." or len(names)!=len(set(names)): _snapshot_failure()
    root_fd=os.open(source,os.O_RDONLY|os.O_CLOEXEC|getattr(os,"O_NOFOLLOW",0)|(os.O_DIRECTORY if members[0]["kind"]=="directory" else 0))
    try:
        for member in members:
            relative=member["path"]; kind=member["kind"]; descriptor=None
            if relative==".": metadata=os.fstat(root_fd); descriptor=os.dup(root_fd)
            elif kind=="symlink":
                descriptor,name=_snapshot_parent_fd(root_fd,relative)
                try: metadata=os.stat(name,dir_fd=descriptor,follow_symlinks=False); target_text=os.readlink(name,dir_fd=descriptor)
                finally: os.close(descriptor)
            else:
                descriptor=_snapshot_member_fd(root_fd,relative,directory=kind=="directory")
                metadata=os.fstat(descriptor)
            if stat.S_IMODE(metadata.st_mode)!=member["mode"]: _snapshot_failure()
            destination=pathlib.Path(target) if relative=="." else pathlib.Path(target)/relative
            if kind=="directory":
                if not stat.S_ISDIR(metadata.st_mode): _snapshot_failure()
                if relative==".": os.chmod(destination,member["mode"],follow_symlinks=False)
                else: destination.mkdir(mode=member["mode"])
                if descriptor is not None: os.close(descriptor)
            elif kind=="symlink":
                if not stat.S_ISLNK(metadata.st_mode) or target_text!=member["target"]: _snapshot_failure()
                os.symlink(member["target"],destination)
            else:
                if not stat.S_ISREG(metadata.st_mode): _snapshot_failure()
                source_fd=descriptor
                try:
                    digest=hashlib.sha256(); destination_fd=os.open(destination,os.O_WRONLY|os.O_CREAT|os.O_TRUNC|getattr(os,"O_NOFOLLOW",0),member["mode"])
                    try:
                        while True:
                            chunk=os.read(source_fd,1048576)
                            if not chunk: break
                            digest.update(chunk); os.write(destination_fd,chunk)
                        os.fchmod(destination_fd,member["mode"])
                    finally: os.close(destination_fd)
                finally: os.close(source_fd)
                if digest.hexdigest()!=member["digest"] or metadata.st_size!=member["size"]: _snapshot_failure()
    except OSError: _snapshot_failure()
    finally: os.close(root_fd)

def _verify_staged_snapshot(encoded,target):
    try: record=json.loads(encoded); payload=json.loads(record["attestation"]); members=payload["members"]
    except (KeyError,TypeError,ValueError): _snapshot_failure()
    actual=[]
    for path in (pathlib.Path(target),*pathlib.Path(target).rglob("*")):
        actual.append("." if path==pathlib.Path(target) else path.relative_to(target).as_posix())
    if sorted(actual)!=[member["path"] for member in members]: _snapshot_failure()
    root_fd=os.open(target,os.O_RDONLY|os.O_CLOEXEC|getattr(os,"O_NOFOLLOW",0)|(os.O_DIRECTORY if members[0]["kind"]=="directory" else 0))
    try:
        for member in members:
            relative=member["path"]; kind=member["kind"]; descriptor=None
            if relative==".": metadata=os.fstat(root_fd); descriptor=os.dup(root_fd)
            elif kind=="symlink":
                descriptor,name=_snapshot_parent_fd(root_fd,relative)
                try: metadata=os.stat(name,dir_fd=descriptor,follow_symlinks=False); target_text=os.readlink(name,dir_fd=descriptor)
                finally: os.close(descriptor); descriptor=None
            else:
                descriptor=_snapshot_member_fd(root_fd,relative,directory=kind=="directory"); metadata=os.fstat(descriptor)
            if stat.S_IMODE(metadata.st_mode)!=member["mode"]: _snapshot_failure()
            if kind=="directory":
                if not stat.S_ISDIR(metadata.st_mode): _snapshot_failure()
            elif kind=="symlink":
                if not stat.S_ISLNK(metadata.st_mode) or target_text!=member["target"]: _snapshot_failure()
            else:
                if not stat.S_ISREG(metadata.st_mode): _snapshot_failure()
                digest=hashlib.sha256()
                while True:
                    chunk=os.read(descriptor,1048576)
                    if not chunk: break
                    digest.update(chunk)
                if digest.hexdigest()!=member["digest"] or metadata.st_size!=member["size"]: _snapshot_failure()
            if descriptor is not None: os.close(descriptor)
    except OSError: _snapshot_failure()
    finally: os.close(root_fd)
'''.strip()


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
    expected=["--reuid",str(uid),"--regid",str(gid),"--clear-groups","--"]
    matches=[index for index in range(len(argv)-5) if argv[index:index+6]==expected]
    if len(matches)!=1:
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


def _fresh_supervision_token() -> str:
    """Return authority bytes independently of staging and unit identifiers."""
    return os.urandom(16).hex()


def _validated_scope_unit(unit_name: str) -> str:
    """Reject any unit spelling that could target another systemd object."""
    if _SCOPE_PATTERN.fullmatch(unit_name) is None:
        raise RuntimeError("invalid protected scope unit name")
    return unit_name


def _validate_trusted_executable_chain(path: Path) -> None:
    """Reject executable ancestors writable by an unprivileged caller."""
    if not path.is_absolute():
        raise RuntimeError("protected executable path is not absolute")
    for directory in reversed(path.parents):
        try:
            metadata = directory.lstat()
        except OSError as exc:
            raise RuntimeError("protected executable ancestor is unavailable") from exc
        if (
            not stat.S_ISDIR(metadata.st_mode)
            or stat.S_ISLNK(metadata.st_mode)
            or metadata.st_uid != 0
            or metadata.st_mode & 0o022
        ):
            raise RuntimeError("protected executable ancestor is attacker-writable")


def _executable_identity(path: Path, *, require_root: bool = True) -> _ExecutableIdentity:
    """Measure one root-owned executable using a no-follow descriptor."""
    descriptor = None
    try:
        resolved = path.resolve(strict=True)
        if require_root:
            _validate_trusted_executable_chain(resolved)
        descriptor = os.open(
            resolved, os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0)
        )
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or not metadata.st_mode & 0o111
            or (require_root and metadata.st_uid != 0)
            or metadata.st_mode & 0o022
        ):
            raise RuntimeError("protected sandbox requires a trusted root-owned executable")
        digest = hashlib.sha256()
        while chunk := os.read(descriptor, 1024 * 1024):
            digest.update(chunk)
        final_metadata = os.fstat(descriptor)
        if require_root:
            _validate_trusted_executable_chain(resolved)
    except OSError as exc:
        raise RuntimeError("protected sandbox requires a trusted root-owned executable") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
    measured = (
        metadata.st_dev, metadata.st_ino, stat.S_IMODE(metadata.st_mode),
        metadata.st_uid, metadata.st_size, metadata.st_mtime_ns,
    )
    final = (
        final_metadata.st_dev, final_metadata.st_ino,
        stat.S_IMODE(final_metadata.st_mode), final_metadata.st_uid,
        final_metadata.st_size, final_metadata.st_mtime_ns,
    )
    if measured != final:
        raise RuntimeError("protected executable identity changed during measurement")
    return _ExecutableIdentity(resolved, measured, digest.hexdigest(), require_root)


def _revalidate_executable(expected: _ExecutableIdentity) -> None:
    """Fail closed when a privileged executable or an ancestor changed."""
    try:
        current = _executable_identity(expected.path, require_root=expected.require_root)
    except RuntimeError as exc:
        raise RuntimeError("protected executable identity changed") from exc
    if current != expected:
        raise RuntimeError("protected executable identity changed")


def _trusted_executable(name: str) -> _ExecutableIdentity:
    """Resolve one root-owned executable from the fixed trusted PATH."""
    value = shutil.which(name, path=_TRUSTED_ROOT_PATH)
    if value is None:
        raise RuntimeError(f"protected sandbox requires trusted {name}")
    return _executable_identity(Path(value))


def _trusted_helper_python() -> _ExecutableIdentity:
    """Select an independently root-owned interpreter for the root helper."""
    for candidate in (Path("/usr/bin/python3"), Path("/bin/python3")):
        try:
            return _executable_identity(candidate)
        except RuntimeError:
            continue
    return _trusted_executable("python3")


def _trusted_tools() -> _TrustedTools:
    """Resolve the complete privileged toolchain once for probe and execution."""
    identities = {
        name.replace("-", "_"): _trusted_executable(name)
        for name in (
            "bwrap", "mount", "setpriv", "sudo", "systemctl", "systemd-run",
            "umount", "unshare",
        )
    }
    helper = _trusted_helper_python()
    return _TrustedTools(
        **{name: identity.path for name, identity in identities.items()},
        helper_python=helper.path,
        identities=tuple((*identities.values(), helper)),
    )


def _revalidate_trusted_tools(tools: _TrustedTools) -> None:
    """Revalidate every executable immediately before a privileged transition."""
    for identity in getattr(tools, "identities", ()):
        _revalidate_executable(identity)


def _privileged_helper_environment() -> dict[str, str]:
    """Return a constant root helper environment with no Python startup hooks."""
    return {"HOME": "/root", "LANG": "C", "LC_ALL": "C", "PATH": _TRUSTED_ROOT_PATH}


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


def _python_version(value: str) -> str | None:
    """Return a validated major.minor prefix from a Python version spelling."""
    parts = value.strip().split(".")
    if len(parts) < 2 or not all(
        1 <= len(part) <= 3
        and all("0" <= character <= "9" for character in part)
        for part in parts[:2]
    ):
        return None
    return f"{int(parts[0])}.{int(parts[1])}"


def _configured_python_runtime(executable: Path) -> tuple[Path, str] | None:
    """Read a bounded native prefix/version pair from adjacent venv metadata."""
    configuration = executable.parent.parent / "pyvenv.cfg"
    try:
        with configuration.open("r", encoding="utf-8") as stream:
            payload = stream.read(64 * 1024 + 1)
        if len(payload) > 64 * 1024:
            return None
        values = {
            key.strip().lower(): value.strip()
            for line in payload.splitlines()
            if "=" in line
            for key, value in (line.split("=", 1),)
        }
        home = Path(values.get("home", ""))
        version = _python_version(values.get("version", ""))
        if home.is_absolute() and home.name in {"bin", "Scripts"} and version:
            return home.parent, version
    except (OSError, UnicodeError):
        return None
    return None


def _discovered_python_version(
    prefix: Path, library_names: tuple[str, ...],
) -> str | None:
    """Return one unambiguous bounded version from native stdlib directories."""
    discovered = set()
    matching_entries = 0
    for library_name in library_names:
        library_root = prefix / library_name
        if not library_root.is_dir():
            continue
        try:
            entries = library_root.iterdir()
        except OSError:
            continue
        try:
            for entry in entries:
                version = _python_version(entry.name.removeprefix("python"))
                if not version or not entry.name.startswith("python"):
                    continue
                if not entry.is_dir():
                    continue
                matching_entries += 1
                if matching_entries > 64:
                    return None
                discovered.add(version)
        except OSError:
            return None
    return discovered.pop() if len(discovered) == 1 else None


def _native_stdlib_root(
    prefix: Path, version: str, library_names: tuple[str, ...],
    preferred_library_name: str | None = None,
) -> Path | None:
    """Select one unambiguous exact stdlib root for a native runtime."""
    roots: dict[str, Path] = {}
    for library_name in library_names:
        try:
            root = (
                prefix / library_name / f"python{version}"
            ).resolve(strict=True)
            if root.is_dir() and (root / "linecache.py").is_file():
                roots[library_name] = root
        except (OSError, RuntimeError):
            continue
    unique_roots = set(roots.values())
    if len(unique_roots) == 1:
        return unique_roots.pop()
    if preferred_library_name and preferred_library_name in roots:
        return roots[preferred_library_name]
    return None


def _native_python_runtime_roots(executable: Path) -> tuple[Path, ...]:
    """Derive only the native stdlib root selected by a Python executable."""
    try:
        resolved = executable.resolve(strict=True)
    except (OSError, RuntimeError):
        return ()
    try:
        current_executable = _SUPERVISOR_EXECUTABLE.resolve(strict=True)
    except (OSError, RuntimeError):
        current_executable = None
    versions: list[tuple[Path, str, str | None]] = []
    configured = _configured_python_runtime(executable)
    if configured:
        versions.append((*configured, None))
    resolved_version = _python_version(resolved.name.removeprefix("python"))
    if resolved_version:
        preference = sys.platlibdir if resolved == current_executable else None
        versions.append((resolved.parent.parent, resolved_version, preference))
    if not resolved_version and resolved == current_executable:
        current_version = f"{sys.version_info.major}.{sys.version_info.minor}"
        versions.append((resolved.parent.parent, current_version, sys.platlibdir))
    library_names = tuple(dict.fromkeys((sys.platlibdir, "lib", "lib64")))
    unversioned_python_names = {"python", "python3"}
    if (
        not versions
        and executable.name in unversioned_python_names
        and resolved.name in unversioned_python_names
    ):
        discovered = _discovered_python_version(
            resolved.parent.parent, library_names,
        )
        if discovered:
            versions.append((resolved.parent.parent, discovered, None))
    roots = []
    for prefix, version, preference in versions:
        root = _native_stdlib_root(
            prefix, version, library_names, preference,
        )
        if root is not None and root not in roots:
            roots.append(root)
    return tuple(roots)


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
                sandbox_commands[name] = _trusted_executable(name).path
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
        roots.update(_native_python_runtime_roots(executable))
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


def _parse_candidate_environment_record(encoded: str) -> dict[str, str]:
    """Parse one canonical bounded credential-free candidate environment."""
    # Exact built-in types make duplicate and authority checks unambiguous.
    # pylint: disable=unidiomatic-typecheck,too-many-boolean-expressions
    try:
        if (
            type(encoded) is not str
            or not encoded
            or len(encoded.encode("utf-8")) > _MAX_CANDIDATE_ENVIRONMENT_BYTES
        ):
            raise ValueError("invalid environment encoding")
        payload = json.loads(encoded)
        if (
            type(payload) is not list
            or len(payload) > _MAX_CANDIDATE_ENVIRONMENT_ENTRIES
            or encoded != _canonical_json(payload)
        ):
            raise ValueError("invalid environment shape")
        environment: dict[str, str] = {}
        for item in payload:
            if type(item) is not list or len(item) != 2:
                raise ValueError("invalid environment entry")
            key, value = item
            upper = key.upper() if type(key) is str else ""
            if (
                type(key) is not str
                or type(value) is not str
                or _CANDIDATE_ENV_KEY.fullmatch(key) is None
                or len(key.encode("utf-8")) > _MAX_CANDIDATE_ENVIRONMENT_KEY_BYTES
                or len(value.encode("utf-8")) > _MAX_CANDIDATE_ENVIRONMENT_VALUE_BYTES
                or "\0" in value
                or key in environment
                or (
                    key != "PDD_SUPERVISION_TOKEN"
                    and any(marker in upper for marker in _BLOCKED_CANDIDATE_ENV_MARKERS)
                )
            ):
                raise ValueError("invalid environment entry")
            environment[key] = value
        if list(environment) != sorted(environment):
            raise ValueError("non-canonical environment order")
        return environment
    except (AttributeError, TypeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError("protected candidate environment is invalid") from exc


def _candidate_environment_record(
    environment: dict[str, str], *, temp_directory: Path,
    supervision_token: str,
) -> str:
    """Build the exact environment installed only by the unprivileged wrapper."""
    # pylint: disable=unidiomatic-typecheck
    if type(environment) is not dict or any(
        type(key) is not str or type(value) is not str
        for key, value in environment.items()
    ):
        raise RuntimeError("protected candidate environment is invalid")
    if (
        type(temp_directory) is not type(Path())
        or type(supervision_token) is not str
        or re.fullmatch(r"[0-9a-f]{32}", supervision_token) is None
    ):
        raise RuntimeError("protected candidate environment is invalid")
    candidate = dict(environment)
    candidate.update({
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": _TRUSTED_ROOT_PATH,
        "PDD_SUPERVISION_TOKEN": supervision_token,
        "PYTHONDONTWRITEBYTECODE": "1",
        "TEMP": str(temp_directory),
        "TMP": str(temp_directory),
        "TMPDIR": str(temp_directory),
    })
    library_path = _sandbox_library_path(environment)
    if library_path:
        candidate["LD_LIBRARY_PATH"] = library_path
    encoded = _canonical_json([[key, candidate[key]] for key in sorted(candidate)])
    _parse_candidate_environment_record(encoded)
    return encoded


def _limited_command(
    command: list[str], limits: SupervisorLimits,
    candidate_environment: str = "[]",
) -> list[str]:
    """Apply non-raiseable POSIX limits after the namespace uid drop."""
    _validate_limits(limits)
    _parse_candidate_environment_record(candidate_environment)
    script = (
        "import json,os,re,resource,sys;"
        "v=[int(x) for x in sys.argv[1:5]];"
        "resource.setrlimit(resource.RLIMIT_AS,(v[0],v[0]));"
        "resource.setrlimit(resource.RLIMIT_CPU,(v[1],v[1]));"
        "resource.setrlimit(resource.RLIMIT_FSIZE,(v[2],v[2]));"
        "resource.setrlimit(resource.RLIMIT_NOFILE,(v[3],v[3]));"
        "encoded=sys.argv[5];payload=json.loads(encoded);"
        "valid=isinstance(payload,list) and len(payload)<=128 and len(encoded.encode())<=131072 and encoded==json.dumps(payload,sort_keys=True,separators=(',',':'));"
        "keys=[];environment={};"
        "valid=valid and all(isinstance(x,list) and len(x)==2 and isinstance(x[0],str) and isinstance(x[1],str) and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',x[0]) and len(x[0].encode())<=128 and len(x[1].encode())<=32768 and '\\0' not in x[1] and not (x[0]!='PDD_SUPERVISION_TOKEN' and any(m in x[0].upper() for m in ('API_KEY','ATTESTATION','CERTIFICATE','CREDENTIAL','PASSWORD','RELEASED_CHECKER','SECRET','SIGNER','SIGNING_KEY','TOKEN'))) and not (x[0] in environment or environment.setdefault(x[0],x[1]) is None) for x in payload);"
        "valid=valid and list(environment)==sorted(environment);"
        "valid or (_ for _ in ()).throw(RuntimeError('invalid candidate environment'));"
        "os.environ.clear();os.environ.update(environment);"
        "os.execvpe(sys.argv[6],sys.argv[6:],os.environ)"
    )
    return [str(_SUPERVISOR_EXECUTABLE), "-c", script, str(limits.max_virtual_memory_bytes),
            str(limits.max_cpu_seconds), str(limits.max_writable_bytes), "256",
            candidate_environment, *command]


# Playwright's aggregate protocol predates and is independent from the
# standard-anonymous coordinator seal. Keep its inner process topology exact;
# even a disabled seal handshake changes descriptor/process lifetime behavior.
_UNSEALED_INNER_STATUS_SUPERVISOR_SOURCE = "\n".join((
    "import json,os,pathlib,signal,sys",
    "fd=int(sys.argv[1]);token=sys.argv[2];cgroup=pathlib.Path(sys.argv[3]);command=sys.argv[4:]",
    "if not command or not cgroup.is_absolute() or '..' in cgroup.parts or len(token)!=32 or any(c not in '0123456789abcdef' for c in token): raise RuntimeError('invalid nested termination protocol')",
    "os.set_inheritable(fd,False)",
    "pid=os.fork()",
    "if pid==0:",
    " try: (cgroup/'cgroup.procs').write_text(str(os.getpid()),encoding='ascii'); os.setsid(); os.execv(command[0],command)",
    " except OSError: os._exit(127)",
    "pid,status=os.waitpid(pid,os.WUNTRACED)",
    "if os.WIFSTOPPED(status):",
    " result=-os.WSTOPSIG(status);os.killpg(pid,signal.SIGKILL);os.waitpid(pid,0)",
    "elif os.WIFSIGNALED(status): result=-os.WTERMSIG(status)",
    "elif os.WIFEXITED(status): result=os.WEXITSTATUS(status)",
    "else: raise RuntimeError('invalid nested wait status')",
    "payload=json.dumps({'returncode':result,'token':token},sort_keys=True,separators=(',',':')).encode('ascii')",
    f"record={_TERMINATION_HEADER_PREFIX!r}+payload+b'\\n'",
    f"if len(record)>{_TERMINATION_HEADER_BYTES}: raise RuntimeError('nested termination record exceeded limit')",
    f"record=record.ljust({_TERMINATION_HEADER_BYTES},b' ')",
    "remaining=memoryview(record)",
    "while remaining: remaining=remaining[os.write(fd,remaining):]",
    "os.close(fd)",
    "raise SystemExit(result if result>=0 else 128-result)",
))


_INNER_STATUS_SUPERVISOR_SOURCE = "\n".join((
    "import json,os,pathlib,signal,stat,subprocess,sys",
    "fd=int(sys.argv[1]);token=sys.argv[2];cgroup=pathlib.Path(sys.argv[3])",
    "sealed_launch=len(sys.argv)>5 and sys.argv[4] in {'0','1'}",
    "seal_coordinator=sys.argv[4] if sealed_launch else '0'",
    "mount_tool=sys.argv[5] if sealed_launch else ''",
    "command=sys.argv[6:] if sealed_launch else sys.argv[4:]",
    "if not command or not cgroup.is_absolute() or '..' in cgroup.parts or len(token)!=32 or any(c not in '0123456789abcdef' for c in token): raise RuntimeError('invalid nested termination protocol')",
    "os.set_inheritable(fd,False)",
    "seal_read,seal_write=os.pipe()",
    "pid=os.fork()",
    "if pid==0:",
    " os.close(seal_write)",
    " try:",
    "  (cgroup/'cgroup.procs').write_text(str(os.getpid()),encoding='ascii'); os.setsid()",
    "  if os.read(seal_read,1)!=b'1': os._exit(125)",
    "  os.close(seal_read); os.execv(command[0],command)",
    " except OSError: os._exit(127)",
    "os.close(seal_read)",
    "if seal_coordinator=='1':",
    " coordinator_fd_target=pathlib.Path('/proc')/str(pid)/'fd'",
    " coordinator_fd_seal=pathlib.Path('/tmp')/('pdd-proc-fd-seal-'+token)",
    " coordinator_fd_seal.mkdir(mode=0o000)",
    " MS_BIND='--bind'",
    " def mount(coordinator_fd_target):",
    "  if not pathlib.Path(mount_tool).is_absolute(): raise RuntimeError('protected coordinator proc descriptor seal failed')",
    "  operation=subprocess.run([mount_tool,MS_BIND,str(coordinator_fd_seal),str(coordinator_fd_target)],capture_output=True,check=False,timeout=10)",
    "  if operation.returncode!=0: raise RuntimeError('protected coordinator proc descriptor seal failed')",
    " before=coordinator_fd_target.stat(); source=coordinator_fd_seal.stat()",
    " if source.st_uid!=0 or stat.S_IMODE(source.st_mode)!=0 or (source.st_dev,source.st_ino)==(before.st_dev,before.st_ino): raise RuntimeError('protected coordinator proc descriptor seal failed')",
    " mount(coordinator_fd_target)",
    " target=coordinator_fd_target.stat()",
    " if (source.st_dev,source.st_ino)!=(target.st_dev,target.st_ino) or list(coordinator_fd_target.iterdir()): raise RuntimeError('protected coordinator proc descriptor seal failed')",
    "os.write(seal_write,b'1'); os.close(seal_write)",
    "pid,status=os.waitpid(pid,os.WUNTRACED)",
    "if os.WIFSTOPPED(status):",
    " result=-os.WSTOPSIG(status);os.killpg(pid,signal.SIGKILL);os.waitpid(pid,0)",
    "elif os.WIFSIGNALED(status): result=-os.WTERMSIG(status)",
    "elif os.WIFEXITED(status): result=os.WEXITSTATUS(status)",
    "else: raise RuntimeError('invalid nested wait status')",
    "payload=json.dumps({'returncode':result,'token':token},sort_keys=True,separators=(',',':')).encode('ascii')",
    f"record={_TERMINATION_HEADER_PREFIX!r}+payload+b'\\n'",
    f"if len(record)>{_TERMINATION_HEADER_BYTES}: raise RuntimeError('nested termination record exceeded limit')",
    f"record=record.ljust({_TERMINATION_HEADER_BYTES},b' ')",
    "remaining=memoryview(record)",
    "while remaining: remaining=remaining[os.write(fd,remaining):]",
    "os.close(fd)",
    "raise SystemExit(result if result>=0 else 128-result)",
))


def _staged_bwrap(
    argv: list[str], sources: list[Path], path_tokens: list[str], *,
    writable_roots: tuple[Path, ...], writable_specs: list[tuple[str, int, str]],
    immutable_binding_proofs: tuple[str, ...],
    snapshot_binding_proofs: tuple[str, ...],
    playwright_aggregate_record: str | None,
    candidate_identity: str,
    unit_name: str, control_directory: Path, limits: SupervisorLimits,
    candidate_timeout: float, tools: _TrustedTools,
    observation_nonce: str | None,
    staging_bytes: int,
) -> tuple[list[str], _ScopePlan]:
    """Build one scope-held helper that releases Bubblewrap after verification."""
    # pylint: disable=too-many-locals
    unit_name = _validated_scope_unit(unit_name)
    tool_manifest = _canonical_json({
        name: identity.payload() for name, identity in zip(
            ("bwrap", "mount", "setpriv", "sudo", "systemctl", "systemd-run", "umount", "unshare", "python"),
            tools.identities,
            strict=True,
        )
    })
    staging_root = control_directory / "binds"
    authority_root = control_directory / "authority"
    anonymous_observation = observation_nonce is not None
    descriptor_protocol = anonymous_observation
    standard_anonymous = (
        anonymous_observation and playwright_aggregate_record is None
    )
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
        "import base64,hashlib,json,math,os,pathlib,select,shutil,stat,subprocess,sys,threading,time",
        "if len(sys.argv)!=1: raise RuntimeError('invalid protected helper protocol')",
        "protocol_in=sys.stdin.buffer; protocol_in_fd=sys.stdin.fileno(); protocol_out_fd=sys.stdout.fileno()",
        "def protocol_send(payload,maximum,deadline):",
        " encoded=json.dumps(payload,sort_keys=True,separators=(',',':')).encode('utf-8')",
        " if len(encoded)>maximum: raise RuntimeError('protected descriptor frame exceeded limit')",
        " frame=memoryview(len(encoded).to_bytes(4,'big')+encoded); blocking=os.get_blocking(protocol_out_fd); os.set_blocking(protocol_out_fd,False)",
        " try:",
        "  poller=select.poll(); poller.register(protocol_out_fd,select.POLLOUT|select.POLLERR|select.POLLHUP)",
        "  while frame:",
        "   remaining=deadline-time.monotonic()",
        "   if remaining<=0: raise RuntimeError('protected descriptor write timed out')",
        "   events=poller.poll(max(1,math.ceil(remaining*1000)))",
        "   if not events: raise RuntimeError('protected descriptor write timed out')",
        "   if any(mask&(select.POLLERR|select.POLLHUP) for _fd,mask in events): raise RuntimeError('protected descriptor parent disappeared')",
        "   if not any(mask&select.POLLOUT for _fd,mask in events): raise RuntimeError('protected descriptor write failed')",
        "   try: written=os.write(protocol_out_fd,frame)",
        "   except BlockingIOError: continue",
        "   if written<=0: raise RuntimeError('protected descriptor short write')",
        "   frame=frame[written:]",
        " finally: os.set_blocking(protocol_out_fd,blocking)",
        "def protocol_read(size,deadline):",
        " chunks=[]",
        " while size:",
        "  remaining=deadline-time.monotonic()",
        "  if remaining<=0: raise RuntimeError('protected descriptor control timed out')",
        "  ready,_,_=select.select((protocol_in,),(),(),remaining)",
        "  if not ready: raise RuntimeError('protected descriptor control timed out')",
        "  chunk=os.read(protocol_in_fd,size)",
        "  if not chunk: raise RuntimeError('protected descriptor parent disappeared')",
        "  chunks.append(chunk); size-=len(chunk)",
        " return b''.join(chunks)",
        "def protocol_receive(maximum,deadline):",
        " header=protocol_read(4,deadline)",
        " if len(header)!=4: raise RuntimeError('protected descriptor parent disappeared')",
        " size=int.from_bytes(header,'big')",
        " if not 0<size<=maximum: raise RuntimeError('protected descriptor frame has invalid size')",
        " encoded=protocol_read(size,deadline)",
        " try: payload=json.loads(encoded)",
        " except (UnicodeError,ValueError): raise RuntimeError('protected descriptor frame is invalid') from None",
        " if type(payload) is not dict or json.dumps(payload,sort_keys=True,separators=(',',':')).encode('utf-8')!=encoded: raise RuntimeError('protected descriptor frame is not canonical')",
        " return payload",
        "def protocol_expect_eof(deadline):",
        " remaining=deadline-time.monotonic()",
        " if remaining<=0: raise RuntimeError('protected descriptor terminal EOF timed out')",
        " ready,_,_=select.select((protocol_in_fd,),(),(),remaining)",
        " if not ready: raise RuntimeError('protected descriptor terminal EOF timed out')",
        " if os.read(protocol_in_fd,1)!=b'': raise RuntimeError('protected descriptor control has trailing data')",
        "launch=protocol_receive(" + str(_DESCRIPTOR_PROTOCOL_MAX_LAUNCH_BYTES) + ",time.monotonic()+" + str(_TRUSTED_SETUP_SECONDS) + ")",
        "expected_launch={'schema','control','candidate_identity','proof_records','writable_roots','writable_specs','path_tokens','argv','paths','fifo_indices','limits'}",
        "if type(launch) is not dict or set(launch)!=expected_launch or launch.get('schema')!='pdd-sandbox-launch-v1': raise RuntimeError('protected launch descriptor is invalid')",
        "control_value=launch['control']; candidate_identity=launch['candidate_identity']; proof_records=launch['proof_records']; writable_root_values=launch['writable_roots']; writable_specs=launch['writable_specs']; path_tokens=launch['path_tokens']; argv=launch['argv']; paths=launch['paths']; fifo_indices=launch['fifo_indices']; limits=launch['limits']",
        "if type(control_value) is not str or not control_value or type(candidate_identity) is not str or type(proof_records) is not list or type(writable_root_values) is not list or type(writable_specs) is not list or type(path_tokens) is not list or type(argv) is not list or type(paths) is not list or type(fifo_indices) is not list or type(limits) is not dict: raise RuntimeError('protected launch descriptor is invalid')",
        "if any(type(value) is not str for value in proof_records+writable_root_values+path_tokens+argv+paths) or any(type(value) is not int or type(value) is bool for value in fifo_indices): raise RuntimeError('protected launch descriptor is invalid')",
        "if any(type(value) is not list or len(value)!=3 or type(value[0]) is not str or type(value[1]) is not int or type(value[1]) is bool or type(value[2]) is not str for value in writable_specs): raise RuntimeError('protected launch descriptor is invalid')",
        "expected_limits={'memory','pids','writable','observation','staging','timeout','trusted_timeout','observation_nonce','termination_token','descriptor_protocol','protocol','output'}",
        "if set(limits)!=expected_limits or any(type(limits[key]) is not int or type(limits[key]) is bool or limits[key]<=0 for key in {'memory','pids','writable','observation','staging','trusted_timeout','protocol','output'}) or type(limits['timeout']) not in {int,float} or isinstance(limits['timeout'],bool) or not math.isfinite(limits['timeout']) or limits['timeout']<=0: raise RuntimeError('protected launch descriptor is invalid')",
        "control=pathlib.Path(control_value); writable_roots=[pathlib.Path(value) for value in writable_root_values]",
        "observation_nonce=limits.get('observation_nonce'); descriptor_protocol=limits.get('descriptor_protocol'); termination_token=limits.get('termination_token')",
        "if type(descriptor_protocol) is not bool: raise RuntimeError('invalid descriptor transport mode')",
        "if type(termination_token) is not str or len(termination_token)!=32 or any(value not in '0123456789abcdef' for value in termination_token): raise RuntimeError('invalid nested termination token')",
        "if descriptor_protocol and (type(observation_nonce) is not str or len(observation_nonce)!=64 or any(value not in '0123456789abcdef' for value in observation_nonce)): raise RuntimeError('invalid descriptor protocol nonce')",
        "if not descriptor_protocol: protocol_expect_eof(time.monotonic()+limits['trusted_timeout'])",
        "authority=control/'authority'",
        "playwright_record=''; anonymous_observation=" + repr(anonymous_observation)
        + "; standard_anonymous=" + repr(standard_anonymous),
        "tool_manifest=json.loads(" + repr(tool_manifest) + ")",
        "def verify_tool(name):",
        " expected=tool_manifest[name]; path=pathlib.Path(expected['path'])",
        " for parent in reversed(path.parents):",
        "  metadata=parent.lstat()",
        "  if not stat.S_ISDIR(metadata.st_mode) or stat.S_ISLNK(metadata.st_mode) or metadata.st_uid!=0 or metadata.st_mode&0o022: raise RuntimeError('protected executable ancestor changed')",
        " fd=os.open(path,os.O_RDONLY|os.O_CLOEXEC|getattr(os,'O_NOFOLLOW',0))",
        " try:",
        "  before=os.fstat(fd); digest=hashlib.sha256()",
        "  while True:",
        "   chunk=os.read(fd,1048576)",
        "   if not chunk: break",
        "   digest.update(chunk)",
        "  after=os.fstat(fd)",
        " finally: os.close(fd)",
        " actual={'path':str(path.resolve(strict=True)),'device':before.st_dev,'inode':before.st_ino,'mode':stat.S_IMODE(before.st_mode),'uid':before.st_uid,'size':before.st_size,'mtime_ns':before.st_mtime_ns,'sha256':digest.hexdigest()}",
        " if actual!=expected or before.st_uid!=0 or before.st_mode&0o022 or not stat.S_ISREG(before.st_mode) or not before.st_mode&0o111 or (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns)!=(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns): raise RuntimeError('protected executable identity changed')",
        " return str(path)",
        "_subprocess_run=subprocess.run",
        "def trusted_run(arguments,**kwargs):",
        " if arguments and arguments[0] in {mount,umount}: verify_tool('mount' if arguments[0]==mount else 'umount')",
        " return _subprocess_run(arguments,**kwargs)",
        "subprocess.run=trusted_run",
        "if set(tool_manifest)!={'bwrap','mount','setpriv','sudo','systemctl','systemd-run','umount','unshare','python'}: raise RuntimeError('invalid protected executable manifest')",
        "for tool_name in tool_manifest: verify_tool(tool_name)",
        "mount=verify_tool('mount'); umount=verify_tool('umount')",
        "targets=[control/'binds'/str(index) for index in range(len(paths))]",
        "staged=[]; result=None; timed_out=False; cleanup_error=None; pid=None",
        "setup_stage='staging-tmpfs'; setup_failure=False; ready_sent=False",
        "observation_read=None; observation_write=None; observation_thread=None",
        "observation_chunks=[]; observation_size=0; observation_overflow=False",
        "candidate_stdout_read=None; candidate_stdout_write=None; candidate_stderr_read=None; candidate_stderr_write=None; candidate_stdout=[]; candidate_stderr=[]; candidate_output_size=0; candidate_output_overflow=False; candidate_output_threads=[]; candidate_output_lock=threading.Lock()",
        "status_read=None; status_write=None",
        "scope_cgroup=None; monitor_cgroup=None; candidate_cgroup=None",
        _PIDFD_PROTOCOL_SOURCE.strip(),
        _IMMUTABLE_STAGING_SOURCE,
        _SNAPSHOT_STAGING_SOURCE,
        "candidate_uid,candidate_gid="
        "_validated_candidate_identity(candidate_identity,argv)",
        "def validated_playwright_record():",
        " if type(anonymous_observation) is not bool: _snapshot_failure()",
        " if playwright_record=='': return None",
        " if not anonymous_observation: _snapshot_failure()",
        " try: record=json.loads(playwright_record); aggregate=json.loads(record['aggregate_attestation'])",
        " except (KeyError,TypeError,ValueError): _snapshot_failure()",
        " if type(record) is not dict or set(record)!={'schema','aggregate_attestation','expected_digest','accepted_toolchain_identity','result_fd','members'} or record['schema']!='pdd-playwright-snapshot-aggregate-record-v1' or playwright_record!=_snapshot_canonical_json(record): _snapshot_failure()",
        " if type(aggregate) is not dict or set(aggregate)!={'schema','toolchain_identity','checker_identity','observation','members'} or aggregate['schema']!='pdd-playwright-snapshot-aggregate-v1' or record['aggregate_attestation']!=_snapshot_canonical_json(aggregate): _snapshot_failure()",
        " if type(record['expected_digest']) is not str or len(record['expected_digest'])!=64 or hashlib.sha256(record['aggregate_attestation'].encode()).hexdigest()!=record['expected_digest']: _snapshot_failure()",
        " if type(record['accepted_toolchain_identity']) is not str or aggregate['checker_identity']!=record['accepted_toolchain_identity']: _snapshot_failure()",
        " observation=aggregate['observation']",
        " if type(observation) is not dict or set(observation)!={'role','transport','result_fd','reporter_sha256'} or observation['role']!='reporter' or observation['transport']!='anonymous-pipe-v1' or observation['result_fd']!=record['result_fd'] or type(observation['reporter_sha256']) is not str or len(observation['reporter_sha256'])!=64 or any(value not in '0123456789abcdef' for value in observation['reporter_sha256']) or type(record['result_fd']) is not int or not 3<=record['result_fd']<=255: _snapshot_failure()",
        " checker=hashlib.sha256(_snapshot_canonical_json({'reporter_sha256':observation['reporter_sha256'],'toolchain_identity':aggregate['toolchain_identity']}).encode()).hexdigest()",
        " if checker!=aggregate['checker_identity']: _snapshot_failure()",
        " members=record['members']",
        " if type(members) is not list or type(aggregate['members']) is not list or len(members)!=len(aggregate['members']): _snapshot_failure()",
        " labels=[]; logical=[]",
        " for member,authority in zip(members,aggregate['members']):",
        "  if type(member) is not dict or set(member)!={'role','source_index','destination','attestation'} or type(authority) is not dict or set(authority)!={'role','attestation'}: _snapshot_failure()",
        "  role=member['role']; index=member['source_index']; destination=member['destination']; attestation=member['attestation']",
        "  if authority!={'role':role,'attestation':attestation} or type(role) is not str or type(index) is not int or not 0<=index<len(paths) or type(destination) is not str or not destination or type(attestation) is not str: _snapshot_failure()",
        "  allowed=role in {'reporter','launcher','browser_runtime','lockfile','dependencies','entrypoint'} or (role.startswith('native_runtime/') and role[15:].isdigit() and str(int(role[15:]))==role[15:])",
        "  if not allowed or index not in snapshot_by_index or json.loads(snapshot_by_index[index])['attestation']!=attestation: _snapshot_failure()",
        "  try: snapshot_payload=json.loads(attestation)",
        "  except (TypeError,ValueError): _snapshot_failure()",
        "  if type(snapshot_payload) is not dict or set(snapshot_payload)!={'schema','source','destination','members'} or snapshot_payload['schema']!='pdd-snapshot-binding-v1' or attestation!=_snapshot_canonical_json(snapshot_payload) or snapshot_payload['source']!=paths[index] or snapshot_payload['destination']!=destination: _snapshot_failure()",
        "  token=path_tokens[index]",
        "  if sum(1 for offset in range(len(argv)-2) if argv[offset:offset+3]==['--ro-bind',token,destination])!=1: _snapshot_failure()",
        "  labels.append(role); logical.append(authority)",
        " if len(labels)!=len(set(labels)) or 'reporter' not in labels or not {'launcher','browser_runtime','lockfile','dependencies'}<=set(labels) or not any(label.startswith('native_runtime/') for label in labels): _snapshot_failure()",
        " reporter_member=next((member for member in members if member['role']=='reporter'),None)",
        " try: reporter_payload=json.loads(reporter_member['attestation']); reporter_members=reporter_payload['members']",
        " except (KeyError,TypeError,ValueError): _snapshot_failure()",
        " if type(reporter_payload) is not dict or set(reporter_payload)!={'schema','source','destination','members'} or type(reporter_members) is not list or len(reporter_members)!=1: _snapshot_failure()",
        " reporter_leaf=reporter_members[0]",
        " if type(reporter_leaf) is not dict or set(reporter_leaf)!={'path','kind','mode','digest','size','target'} or reporter_leaf['path']!='.' or reporter_leaf['kind']!='file' or reporter_leaf['digest']!=observation['reporter_sha256']: _snapshot_failure()",
        " rebuilt={'schema':'pdd-playwright-snapshot-aggregate-v1','toolchain_identity':aggregate['toolchain_identity'],'checker_identity':aggregate['checker_identity'],'observation':aggregate['observation'],'members':logical}",
        " if _snapshot_canonical_json(rebuilt)!=record['aggregate_attestation'] or hashlib.sha256(_snapshot_canonical_json(rebuilt).encode()).hexdigest()!=record['expected_digest']: _snapshot_failure()",
        " return record",
        "def verify_playwright_aggregate(record,mapped=False):",
        " if record is None: return",
        " for member in record['members']:",
        "  index=member['source_index']; expected_source=str(targets[index]) if mapped else path_tokens[index]",
        "  if sum(1 for offset in range(len(argv)-2) if argv[offset:offset+3]==['--ro-bind',expected_source,member['destination']])!=1: _snapshot_failure()",
        "  _verify_staged_snapshot(snapshot_by_index[index],targets[index])",
        " if hashlib.sha256(record['aggregate_attestation'].encode()).hexdigest()!=record['expected_digest']: _snapshot_failure()",
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
        " setup_stage='staging-tmpfs'",
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
        " setup_stage='authority-tmpfs'",
        " subprocess.run([mount,'-t','tmpfs','-o',"
        "'size=17825792,mode=0700,nosuid,nodev','tmpfs',str(authority)],"
        "check=True,timeout=limits['trusted_timeout'])",
        " staged.append(authority)",
        " authority_lines=pathlib.Path('/proc/self/mountinfo').read_text("
        "encoding='utf-8').splitlines()",
        " authority_fields=[line.split() for line in authority_lines]",
        " authority_mount=next((fields for fields in authority_fields if len(fields)>6 and "
        "pathlib.Path(fields[4])==authority),None)",
        " if authority_mount is None or '-' not in authority_mount or "
        "authority_mount[authority_mount.index('-')+1]!='tmpfs': "
        "raise RuntimeError('protected observation authority mount probe failed')",
        " authority_metadata=authority.lstat()",
        " if not stat.S_ISDIR(authority_metadata.st_mode) or authority_metadata.st_uid!=0 or stat.S_IMODE(authority_metadata.st_mode)!=0o700: "
        "raise RuntimeError('protected observation authority ownership probe failed')",
        " setup_stage='staging-layout'",
        " if type(proof_records) is not list or "
        "any(type(value) is not str for value in proof_records): "
        "raise RuntimeError('invalid immutable binding proof protocol')",
        " proof_by_index={}; snapshot_by_index={}",
        " for encoded in proof_records:",
        "  try: preliminary=json.loads(encoded); schema=preliminary['schema']",
        "  except (TypeError,ValueError,KeyError): _immutable_failure()",
        "  if schema=='pdd-playwright-snapshot-aggregate-record-v1':",
        "   if playwright_record!='': _snapshot_failure()",
        "   playwright_record=encoded; anonymous_observation=True; continue",
        "  try: source_index=preliminary['source_index']",
        "  except (TypeError,KeyError): _immutable_failure()",
        "  if type(source_index) is not int or source_index<0 or "
        "source_index>=len(paths) or source_index in proof_by_index or source_index in snapshot_by_index: "
        "_immutable_failure()",
        "  if schema=='pdd-immutable-binding-record-v1': proof_by_index[source_index]=encoded",
        "  elif schema=='pdd-snapshot-binding-record-v1': snapshot_by_index[source_index]=encoded",
        "  else: _immutable_failure()",
        " playwright=validated_playwright_record()",
        " if type(fifo_indices) is not list or len(fifo_indices)>1 or "
        "any(type(value) is not int or value<0 or value>=len(paths) "
        "for value in fifo_indices): "
        "raise RuntimeError('invalid protected FIFO staging protocol')",
        " for index,(source,target) in enumerate(zip(paths,targets)):",
        "  metadata=pathlib.Path(source).lstat()",
        "  if index in snapshot_by_index:",
        "   try: root_member=json.loads(json.loads(snapshot_by_index[index])['attestation'])['members'][0]",
        "   except (KeyError,TypeError,ValueError,IndexError): _snapshot_failure()",
        "   target.mkdir(mode=0o700) if root_member.get('kind')=='directory' else target.touch(mode=0o600)",
        "  elif index in proof_by_index or stat.S_ISREG(metadata.st_mode): target.touch(mode=0o600)",
        "  elif stat.S_ISDIR(metadata.st_mode): target.mkdir(mode=0o700)",
        "  elif index in fifo_indices and stat.S_ISFIFO(metadata.st_mode): "
        "os.mkfifo(target,mode=0o600)",
        "  else: raise RuntimeError('protected staging source type is invalid')",
        " writable_target=control/'binds'/'writable'",
        " writable_target.mkdir(mode=0o700)",
        " cgroup_target=control/'binds'/'cgroup'",
        " cgroup_target.mkdir(mode=0o700)",
        " setup_stage='writable-tmpfs'",
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
        " setup_stage='writable-copy'",
        " writable_paths=[]",
        " for index,source in enumerate(writable_roots):",
        "  target=writable_target/str(index); copy_owned(source,target); "
        "writable_paths.append(target)",
        " if sum(validate_tree(path) for path in writable_paths) > "
        "limits['writable']: raise RuntimeError('initial writable quota exceeded')",
        " setup_stage='bind-staging'",
        " for index,(source,target) in enumerate(zip(paths,targets)):",
        "  if index in snapshot_by_index:",
        "   _stage_snapshot(snapshot_by_index[index],source,target)",
        "  elif index in proof_by_index:",
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
        " argv=[termination_token if value=='@PDD-TERMINATION-TOKEN@' else value for value in argv]",
        " argv=[('1' if standard_anonymous else '0') if value=='@PDD-SEAL-COORDINATOR-PROC-FD@' else value for value in argv]",
        " verify_playwright_aggregate(playwright,mapped=True)",
        " if anonymous_observation:",
        "  observation_read,observation_write=os.pipe()",
        "  def drain_observation():",
        "   global observation_size,observation_overflow",
        "   while True:",
        "    chunk=os.read(observation_read,1048576)",
        "    if not chunk: break",
        "    observation_size+=len(chunk)",
        "    if observation_size>limits['observation']: observation_overflow=True",
        "    elif not observation_overflow: observation_chunks.append(chunk)",
        "  observation_thread=threading.Thread(target=drain_observation,daemon=True)",
        " setup_stage='cgroup-configure'",
        " configure_candidate_leaf()",
        " setup_stage='cgroup-bind'",
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
        " setup_stage='ready-handoff'",
        " if descriptor_protocol:",
        "  protocol_send({'kind':'ready','nonce':observation_nonce},4096,time.monotonic()+limits['trusted_timeout'])",
        "  ready_sent=True",
        "  start=protocol_receive(4096,time.monotonic()+limits['trusted_timeout'])",
        "  if start!={'kind':'start','nonce':observation_nonce}: raise RuntimeError('protected descriptor start is invalid')",
        " else:",
        "  (control/'ready').write_text('ready',encoding='ascii')",
        "  wait_for('start')",
        " release_read,release_write=os.pipe()",
        " status_read,status_write=os.pipe()",
        " os.set_blocking(status_read,False)",
        " verify_tool('bwrap'); verify_tool('setpriv')",
        " if descriptor_protocol:",
        "  candidate_stdout_read,candidate_stdout_write=os.pipe(); candidate_stderr_read,candidate_stderr_write=os.pipe()",
        "  def drain_candidate(fd,chunks):",
        "   global candidate_output_size,candidate_output_overflow",
        "   while True:",
        "    chunk=os.read(fd,1048576)",
        "    if not chunk: break",
        "    with candidate_output_lock:",
        "     candidate_output_size+=len(chunk)",
        "     if candidate_output_size>limits['output']: candidate_output_overflow=True",
        "     elif not candidate_output_overflow: chunks.append(chunk)",
        "   os.close(fd)",
        "  candidate_output_threads=[threading.Thread(target=drain_candidate,args=(candidate_stdout_read,candidate_stdout),daemon=True),threading.Thread(target=drain_candidate,args=(candidate_stderr_read,candidate_stderr),daemon=True)]",
        " pid=os.fork()",
        " if pid == 0:",
        "  os.close(release_write)",
        "  try:",
        "   os.close(status_read)",
        "   if anonymous_observation:",
        "    os.close(observation_read); os.dup2(observation_write,3) if observation_write!=3 else None",
        "    os.close(observation_write) if observation_write!=3 else None",
        "   if descriptor_protocol:",
        "    os.close(candidate_stdout_read); os.close(candidate_stderr_read)",
        "    null=os.open('/dev/null',os.O_RDONLY); os.dup2(null,0); os.close(null) if null!=0 else None",
        "    os.dup2(candidate_stdout_write,1); os.dup2(candidate_stderr_write,2)",
        "    os.close(candidate_stdout_write) if candidate_stdout_write not in {1,2,3} else None; os.close(candidate_stderr_write) if candidate_stderr_write not in {1,2,3} else None",
        "   if os.read(release_read,1)!=b'1': os._exit(125)",
        "   os.close(release_read)",
        "   status_fd=4 if anonymous_observation else 3",
        "   os.dup2(status_write,status_fd) if status_write!=status_fd else None",
        "   os.close(status_write) if status_write!=status_fd else None",
        "   os.execvpe(argv[0],argv,os.environ)",
        "  except OSError: os._exit(125)",
        " os.close(release_read)",
        " os.close(status_write)",
        " if anonymous_observation: os.close(observation_write)",
        " if descriptor_protocol: os.close(candidate_stdout_write); os.close(candidate_stderr_write)",
        " if anonymous_observation: observation_thread.start()",
        " if descriptor_protocol: [thread.start() for thread in candidate_output_threads]",
        " parent_watch_done=threading.Event(); parent_watch=None",
        " if descriptor_protocol:",
        "  def watch_parent():",
        "   poller=select.poll(); poller.register(protocol_in.fileno(),select.POLLHUP|select.POLLERR)",
        "   while not parent_watch_done.is_set():",
        "    if any(mask&(select.POLLHUP|select.POLLERR) for _fd,mask in poller.poll(100)):",
        "     kill_candidate_leaf(); return",
        "  parent_watch=threading.Thread(target=watch_parent,daemon=True); parent_watch.start()",
        " os.write(release_write,b'1'); os.close(release_write)",
        " result,timed_out=_supervise_candidate(pid,limits['timeout'])",
        " def nested_status(deadline):",
        "  record=b''",
        "  while len(record)<256:",
        "   remaining=deadline-time.monotonic()",
        "   if remaining<=0: raise RuntimeError('nested termination status timed out')",
        "   ready,_,_=select.select((status_read,),(),(),remaining)",
        "   if not ready: raise RuntimeError('nested termination status timed out')",
        "   try: chunk=os.read(status_read,256-len(record))",
        "   except BlockingIOError: continue",
        "   if not chunk: break",
        "   record+=chunk",
        "  os.close(status_read)",
        "  prefix=b'PDD-TERMINATION-V1 '",
        "  if len(record)!=256 or not record.startswith(prefix): raise RuntimeError('nested termination status is invalid')",
        "  try: payload=json.loads(record[len(prefix):].rstrip(b' \\n').decode('ascii'))",
        "  except (UnicodeError,ValueError): raise RuntimeError('nested termination status is invalid') from None",
        "  if type(payload) is not dict or set(payload)!={'returncode','token'} or payload['token']!=termination_token or type(payload['returncode']) is not int or type(payload['returncode']) is bool or not -255<=payload['returncode']<=255: raise RuntimeError('nested termination status is invalid')",
        "  return payload['returncode']",
        " if timed_out: os.close(status_read)",
        " else: result=nested_status(time.monotonic()+limits['trusted_timeout'])",
        " kill_candidate_leaf()",
        " if descriptor_protocol:",
        "  [thread.join(timeout=limits['trusted_timeout']) for thread in candidate_output_threads]",
        "  if any(thread.is_alive() for thread in candidate_output_threads) or candidate_output_overflow: raise RuntimeError('protected candidate output relay failed')",
        " if anonymous_observation:",
        "  observation_thread.join(timeout=limits['trusted_timeout'])",
        "  os.close(observation_read)",
        "  if observation_thread.is_alive() or observation_overflow: raise RuntimeError('protected observation relay failed')",
        " verify_playwright_aggregate(playwright,mapped=True)",
        " if descriptor_protocol:",
        "  if sum(validate_tree(path) for path in writable_paths) > limits['writable']: raise RuntimeError('final writable quota exceeded')",
        "  aggregate_digest=playwright['expected_digest'] if playwright is not None else "
        + repr(_STANDARD_ANONYMOUS_AGGREGATE_DIGEST),
        "  payload={'kind':'result','nonce':observation_nonce,'aggregate_digest':aggregate_digest,'candidate':{'version':1,'state':'terminal','returncode':result,'timed_out':timed_out},'stdout':base64.b64encode(b''.join(candidate_stdout)).decode('ascii'),'stderr':base64.b64encode(b''.join(candidate_stderr)).decode('ascii'),'observation':base64.b64encode(b''.join(observation_chunks)).decode('ascii'),'observation_sha256':hashlib.sha256(b''.join(observation_chunks)).hexdigest(),'observation_size':observation_size}",
        "  protocol_send(payload,limits['protocol'],time.monotonic()+limits['trusted_timeout'])",
        "  acknowledgement=protocol_receive(4096,time.monotonic()+limits['trusted_timeout'])",
        "  expected_ack={'kind':'ack','nonce':observation_nonce,'digest':hashlib.sha256(json.dumps(payload,sort_keys=True,separators=(',',':')).encode('utf-8')).hexdigest()}",
        "  if acknowledgement!=expected_ack: raise RuntimeError('protected descriptor acknowledgement is invalid')",
        "  protocol_expect_eof(time.monotonic()+limits['trusted_timeout'])",
        "  parent_watch_done.set(); parent_watch.join(timeout=limits['trusted_timeout'])",
        "  if parent_watch.is_alive(): raise RuntimeError('protected descriptor parent watcher did not stop')",
        " elif anonymous_observation:",
        "  observation_path=authority/'observation.bin'",
        "  observation_fd=os.open(observation_path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,'O_NOFOLLOW',0),0o444)",
        "  try:",
        "   for chunk in observation_chunks: os.write(observation_fd,chunk)",
        "   os.fsync(observation_fd)",
        "   os.fchmod(observation_fd,0o444)",
        "  finally: os.close(observation_fd)",
        " if not descriptor_protocol:",
        "  record={'version':1,'state':'terminal','returncode':result,"
        "'timed_out':timed_out}",
        "  candidate=control/'candidate.tmp'",
        "  candidate.write_text(json.dumps(record),encoding='ascii')",
        "  os.replace(candidate,control/'candidate.json')",
        "  if sum(validate_tree(path) for path in writable_paths) > "
        "limits['writable']: raise RuntimeError('final writable quota exceeded')",
        "  if anonymous_observation:",
        "   if type(observation_nonce) is not str or len(observation_nonce)!=64 or any(value not in '0123456789abcdef' for value in observation_nonce): raise RuntimeError('invalid protected observation nonce')",
        "   record=record|{'observation_nonce':observation_nonce,'observation_sha256':hashlib.sha256(b''.join(observation_chunks)).hexdigest(),'observation_size':observation_size}",
        "   temporary=authority/'result.tmp'",
        "   temporary.write_text(json.dumps(record),encoding='ascii')",
        "   os.chmod(temporary,0o444); os.replace(temporary,authority/'result.json'); os.chmod(authority,0o711)",
        "   authority_metadata=authority.lstat()",
        "   if authority_metadata.st_uid!=0 or stat.S_IMODE(authority_metadata.st_mode)!=0o711: raise RuntimeError('protected observation authority release probe failed')",
        "  else:",
        "   temporary=control/'result.tmp'",
        "   temporary.write_text(json.dumps(record),encoding='ascii')",
        "   os.replace(temporary,control/'result.json')",
        "  wait_for('finish')",
        "except Exception:",
        " if descriptor_protocol and not ready_sent:",
        "  try: protocol_send({'kind':'setup-error','nonce':observation_nonce,'reason':setup_stage},4096,time.monotonic()+limits['trusted_timeout'])",
        "  except Exception: pass",
        "  setup_failure=True",
        " else: raise",
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
        "if setup_failure: raise SystemExit(125)",
        "raise SystemExit(result if result is not None and result >= 0 else "
        "(128-result if result is not None else 125))",
    ))
    launch_payload = {
        "schema": "pdd-sandbox-launch-v1",
        "control": str(control_directory),
        "candidate_identity": candidate_identity,
        "proof_records": list((*immutable_binding_proofs, *snapshot_binding_proofs, *(
            (playwright_aggregate_record,) if playwright_aggregate_record else ()
        ))),
        "writable_roots": [str(path) for path in writable_roots],
        "writable_specs": [list(spec) for spec in writable_specs],
        "path_tokens": list(path_tokens),
        "argv": list(argv),
        "paths": [str(path) for path in sources],
        "fifo_indices": list(fifo_source_indices),
        "limits": {
            "memory": limits.max_memory_bytes, "pids": limits.max_processes,
            "writable": limits.max_writable_bytes,
            "observation": 16 * 1024 * 1024,
            "staging": staging_bytes,
            "timeout": candidate_timeout,
            "trusted_timeout": _TRUSTED_COMMAND_SECONDS,
            "observation_nonce": observation_nonce,
            "termination_token": os.urandom(16).hex(),
            "descriptor_protocol": descriptor_protocol,
            "protocol": _DESCRIPTOR_PROTOCOL_MAX_RESULT_BYTES,
            "output": limits.max_output_bytes,
        },
    }
    _descriptor_frame(launch_payload, _DESCRIPTOR_PROTOCOL_MAX_LAUNCH_BYTES)
    plan = _ScopePlan(
        unit_name, control_directory, helper, tuple(argv), tuple(sources),
        (authority_root, staging_root, *source_targets, control_directory / "binds" / "writable",
         control_directory / "binds" / "cgroup"), tools,
        immutable_binding_proofs, launch_payload,
    )
    command = [
        str(tools.sudo), "-n", str(tools.systemd_run), "--scope", "--quiet",
        f"--unit={unit_name}", "--property=Delegate=yes",
        "--property=MemoryMax=infinity", "--property=MemorySwapMax=infinity",
        "--property=TasksMax=infinity", "--property=OOMPolicy=continue",
        "--property=KillMode=control-group", "--",
        str(tools.unshare), "--mount", "--propagation", "private", "--wd", "/",
        str(tools.helper_python), "-I", "-S", "-c", helper,
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


def _anonymous_framework_observation_command(
    command: list[str], result_fd: int, *, seal_cross_process: bool = False,
) -> list[str]:
    """Move the single helper-created candidate pipe from fd 3 to its reporter fd."""
    policy = ()
    if seal_cross_process:
        policy = (
            "PR_SET_PTRACER=0x59616d61",
            "libc=ctypes.CDLL(None,use_errno=True)",
            "prctl=libc.prctl; prctl.restype=ctypes.c_int; prctl.argtypes=[ctypes.c_int,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_ulong]",
            "ctypes.set_errno(0)",
            "if prctl(PR_SET_PTRACER,0,0,0,0)!=0: raise RuntimeError('protected coordinator ptrace policy setup failed')",
            "scope=pathlib.Path('/proc/sys/kernel/yama/ptrace_scope')",
            "try: scope_value=int(scope.read_text(encoding='ascii').strip(),10)",
            "except (OSError,ValueError) as exc: raise RuntimeError('protected coordinator ptrace policy is unavailable') from exc",
            "if scope_value not in {1,2,3}: raise RuntimeError('protected coordinator ptrace policy is unavailable')",
            "probe_read,probe_write=os.pipe(); probe_pid=os.fork()",
            "if probe_pid==0:",
            " os.close(probe_read)",
            " failure=''",
            " try:",
            "  os.close(target); parent=os.getppid(); leader=str(parent)",
            "  task_root=pathlib.Path('/proc')/leader/'task'",
            "  tids=sorted(entry.name for entry in task_root.iterdir() if entry.name.isdigit())",
            "  if leader not in tids: raise RuntimeError('leader task is absent')",
            "  probes=[(pathlib.Path('/proc')/leader/'fd'/str(target),True)]",
            "  probes.extend((pathlib.Path('/proc')/leader/'task'/tid/'fd'/str(target),False) for tid in tids)",
            "  probes.extend((pathlib.Path('/proc')/tid/'fd'/str(target),False) for tid in tids)",
            "  for candidate,direct in probes:",
            "   try: opened=os.open(candidate,os.O_WRONLY|os.O_CLOEXEC)",
            "   except OSError as exc:",
            "    accepted={errno.EACCES,errno.EPERM}|({errno.ENOENT} if direct else set())",
            "    if exc.errno not in accepted: raise",
            "   else: os.close(opened); raise RuntimeError('proc descriptor alias reopened')",
            "  if hasattr(os,'pidfd_open') and platform.machine() in {'x86_64','AMD64','aarch64','arm64'}:",
            "   pidfd=os.pidfd_open(parent,0)",
            "   try:",
            "    syscall=libc.syscall; syscall.restype=ctypes.c_long",
            "    duplicate=syscall(438,pidfd,target,0); observed=ctypes.get_errno()",
            "    if duplicate>=0: os.close(duplicate); raise RuntimeError('pidfd_getfd reopened descriptor')",
            "    if observed not in {errno.EACCES,errno.EPERM}: raise OSError(observed,'pidfd_getfd denial failed')",
            "   finally: os.close(pidfd)",
            " except (OSError,RuntimeError) as exc: failure=type(exc).__name__+':'+str(exc)",
            " payload=('ok' if not failure else failure).encode('utf-8')[:1024]",
            " try: os.write(probe_write,payload)",
            " finally: os.close(probe_write)",
            " os._exit(0 if not failure else 125)",
            "os.close(probe_write); probe_payload=os.read(probe_read,1024); os.close(probe_read)",
            "waited,status=os.waitpid(probe_pid,0)",
            "if waited!=probe_pid or status!=0 or probe_payload!=b'ok': raise RuntimeError('protected coordinator ptrace policy probe failed: '+probe_payload.decode('utf-8',errors='replace'))",
            "os.write(target,b'PDD-VITEST-PROGRESS-V1 post-drop-probes\\n')",
        )
    script = "\n".join((
        "import ctypes,errno,os,pathlib,platform,stat,sys",
        "source=3;target=int(sys.argv[1])",
        "os.dup2(source,target)",
        "os.close(source) if source!=target else None",
        "metadata=os.fstat(target)",
        "if not stat.S_ISFIFO(metadata.st_mode): raise RuntimeError('anonymous observation endpoint is not a pipe')",
        "os.environ['PDD_FRAMEWORK_OBSERVATION_DEVICE']=str(metadata.st_dev)",
        "os.environ['PDD_FRAMEWORK_OBSERVATION_INODE']=str(metadata.st_ino)",
        *policy,
        *(
            ("os.write(target,b'PDD-VITEST-PROGRESS-V1 candidate-exec\\n')",)
            if seal_cross_process else ()
        ),
        "os.execvpe(sys.argv[2],sys.argv[2:],os.environ)",
    ))
    return [str(_SUPERVISOR_EXECUTABLE), "-c", script, str(result_fd), *command]

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
    if not isinstance(payload, dict) or set(payload) != {
        "version", "state", "returncode", "timed_out",
    }:
        raise RuntimeError("protected candidate record is invalid")
    return _load_candidate_record_payload(payload)


def _load_candidate_record_payload(payload: object) -> _CandidateRecord:
    """Validate the terminal fields shared by candidate and authority records."""
    expected_keys = {"version", "state", "returncode", "timed_out"}
    if type(payload) is not dict or set(payload) != expected_keys:  # pylint: disable=unidiomatic-typecheck
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


def _read_root_artifact(path: Path, maximum: int) -> bytes:
    """Read one bounded immutable root-owned authority artifact."""
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0))
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_uid != 0
            or before.st_mode & 0o222
            or before.st_size > maximum
        ):
            raise RuntimeError("protected observation artifact is invalid")
        chunks = []
        size = 0
        while chunk := os.read(descriptor, 1024 * 1024):
            size += len(chunk)
            if size > maximum:
                raise RuntimeError("protected observation artifact exceeded limit")
            chunks.append(chunk)
        after = os.fstat(descriptor)
        if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
            after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns
        ):
            raise RuntimeError("protected observation artifact changed")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def _load_root_observation_result(
    path: Path, nonce: str, maximum: int,
) -> _RootObservationResult:
    """Read the exact nonce-bound observation metadata from root authority."""
    # Exact built-in types keep the trusted result record unambiguous.
    # pylint: disable=unidiomatic-typecheck
    try:
        payload = json.loads(_read_root_artifact(path, 4096))
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise RuntimeError("protected observation result is invalid") from exc
    expected_keys = {
        "version", "state", "returncode", "timed_out", "observation_nonce",
        "observation_sha256", "observation_size",
    }
    if not isinstance(payload, dict) or set(payload) != expected_keys:
        raise RuntimeError("protected observation result is invalid")
    candidate = _load_candidate_record_payload({
        key: payload[key]
        for key in ("version", "state", "returncode", "timed_out")
    })
    digest = payload["observation_sha256"]
    size = payload["observation_size"]
    if (
        payload["observation_nonce"] != nonce
        or type(digest) is not str
        or re.fullmatch(r"[0-9a-f]{64}", digest) is None
        or type(size) is not int
        or not 0 <= size <= maximum
    ):
        raise RuntimeError("protected observation result is invalid")
    return _RootObservationResult(candidate, digest, size)


def _load_root_observation(
    path: Path, maximum: int, expected_digest: str, expected_size: int,
) -> bytes:
    """Read a root authority artifact only when its result binding matches."""
    observation = _read_root_artifact(path, maximum)
    if (
        len(observation) != expected_size
        or hashlib.sha256(observation).hexdigest() != expected_digest
    ):
        raise RuntimeError("protected observation artifact does not match result")
    return observation


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
    _revalidate_trusted_tools(tools)
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


def _cgroup_resource_telemetry(
    memory_before: dict[str, int],
    memory_after: dict[str, int],
    pids_before: dict[str, int],
    pids_after: dict[str, int],
) -> CgroupResourceTelemetry:
    """Return monotonic kernel-event deltas for one proven candidate leaf."""
    values = {
        "memory.events oom": memory_after["oom"] - memory_before["oom"],
        "memory.events oom_kill": (
            memory_after["oom_kill"] - memory_before["oom_kill"]
        ),
        "pids.events max": pids_after["max"] - pids_before["max"],
    }
    regressed = [name for name, value in values.items() if value < 0]
    if regressed:
        raise RuntimeError(
            "protected cgroup event counter regressed: " + ",".join(regressed)
        )
    return CgroupResourceTelemetry(
        memory_oom_delta=values["memory.events oom"],
        memory_oom_kill_delta=values["memory.events oom_kill"],
        pids_max_delta=values["pids.events max"],
    )


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
    """Create only root-helper mountpoints inside the caller control directory."""
    binds = plan.control_directory / "binds"
    binds.mkdir(mode=0o700)
    (plan.control_directory / "authority").mkdir(mode=0o700)


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
    snapshot_binding_proofs: tuple[SnapshotBindingProof, ...] = (),
    playwright_snapshot_aggregate: PlaywrightSnapshotAggregate | None = None,
    writable_bindings: tuple[tuple[Path, Path], ...] = (),
    result_fifo: Path | None = None,
    result_write_fd: int | None = None,
    result_fd: int = 198,
    candidate_environment: str = "[]",
    candidate_environment_values: dict[str, str] | None = None,
    candidate_temp_directory: Path | None = None,
    supervision_token: str | None = None,
    observation_nonce: str | None = None,
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
                [str(tools.sudo), "-n", str(tools.helper_python), "-I", "-S", "-c", "pass"],
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
        # Keep the host cgroup namespace while exposing only the candidate leaf
        # below. A namespace rooted at the monitor cannot migrate the child into
        # its sibling candidate leaf; the read-only candidate uid still cannot
        # change membership or limits after the root supervisor performs it.
        argv = [str(tools.bwrap), "--unshare-ipc", "--unshare-pid", "--unshare-net",
                "--unshare-uts", "--die-with-parent", "--new-session",
                "--tmpfs", "/", "--proc", "/proc", "--dir", "/tmp",
                "--dir", "/sys", "--dir", "/sys/fs", "--dir", "/sys/fs/cgroup"]
        sources: list[Path] = []
        path_tokens: list[str] = []
        writable_specs: list[tuple[str, int, str]] = []
        deferred_readable_mounts: list[str] = []
        destination_dirs = {Path("/tmp")}
        mounted: dict[Path, tuple[str, Path, str, int | None]] = {}
        proofs: dict[tuple[Path, Path, Path], _ValidatedBindingProof] = {}
        raw_proofs: dict[tuple[Path, Path, Path], ImmutableBindingProof] = {}
        snapshots: dict[tuple[Path, Path], SnapshotBindingProof] = {}
        aggregate_payload = (
            _validate_playwright_snapshot_aggregate(playwright_snapshot_aggregate)
            if playwright_snapshot_aggregate is not None else None
        )
        standard_anonymous = (
            result_write_fd is not None and playwright_snapshot_aggregate is None
        )
        playwright_aggregate = playwright_snapshot_aggregate is not None
        if aggregate_payload is not None and result_write_fd is None:
            raise RuntimeError("Playwright aggregate requires anonymous observation")
        if result_write_fd is not None and (
            type(observation_nonce) is not str
            or re.fullmatch(r"[0-9a-f]{64}", observation_nonce) is None
        ):
            raise RuntimeError("anonymous observation requires a fresh parent nonce")
        if result_write_fd is None and observation_nonce is not None:
            raise RuntimeError("observation nonce requires an anonymous endpoint")
        if result_fifo is not None and result_write_fd is not None:
            raise RuntimeError("framework observation transports conflict")
        for proof in snapshot_binding_proofs:
            _validate_snapshot_binding_proof(proof)
            key = (proof.source.resolve(strict=True), proof.destination)
            if key in snapshots:
                raise RuntimeError("protected sandbox has duplicate snapshot binding proofs")
            snapshots[key] = proof
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
        accepted_immutable_records: list[tuple[int, _ValidatedBindingProof]] = []
        accepted_snapshots: list[str] = []
        accepted_snapshot_details: dict[str, tuple[int, Path]] = {}

        def copied_binding_proof(
            source: Path, destination: Path,
        ) -> tuple[tuple[Path, Path, Path], _ValidatedBindingProof] | None:
            """Return one exact descriptor authority for a copied native bind."""
            matches = [
                (key, proof) for key, proof in proofs.items()
                if key[0] == source and key[2] == destination
            ]
            if len(matches) > 1:
                raise RuntimeError("protected sandbox has ambiguous immutable binding proof")
            return matches[0] if matches else None

        def equivalent_native_authority(
            first: _ValidatedBindingProof, second: _ValidatedBindingProof,
        ) -> bool:
            """Allow only duplicate copied aliases of one descriptor-native member."""
            return (
                first.protected_source == second.protected_source
                and first.destination == second.destination
                and first.descriptor_attestation == second.descriptor_attestation
                and first.descriptor_identity == second.descriptor_identity
                and first.member_role == second.member_role == "native_runtime"
                and first.collision_category == second.collision_category
                and first.member_digest == second.member_digest
                and first.member_mode == second.member_mode
            )

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
            category: str, defer_mount: bool = False,
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
                    accepted_immutable_records.append((previous[3], proof))
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
                previous_authority = copied_binding_proof(previous[1], destination)
                redundant_trusted_runtime = (
                    option == "--ro-bind"
                    and previous[0] == "--ro-bind"
                    and previous[2] == "declared_readable"
                    and category == "trusted_runtime"
                    and previous_authority is not None
                    and previous_authority[0] in consumed_proofs
                    and previous_authority[1].protected_source == resolved_source
                    and previous_authority[1].destination == destination
                )
                if redundant_trusted_runtime:
                    # Inference already retained and recorded the immutable
                    # descriptor copy. The trusted ELF closure names the exact
                    # same protected bytes and therefore adds no new mount.
                    return
                current_authority = copied_binding_proof(resolved_source, destination)
                duplicate_declared_read_only = (
                    option == "--ro-bind"
                    and previous[0] == "--ro-bind"
                    and previous[2] == "declared_readable"
                    and category == "declared_readable"
                )
                if (
                    duplicate_declared_read_only
                    and previous_authority is not None
                    and current_authority is not None
                    and equivalent_native_authority(
                        previous_authority[1], current_authority[1]
                    )
                ):
                    if current_authority[0] in consumed_proofs:
                        raise RuntimeError(
                            "protected sandbox immutable binding proof was multiply consumed"
                        )
                    # Keep the first descriptor-proven copy.  The later alias
                    # never mounts, but is consumed so proof accounting stays exact.
                    consumed_proofs.add(current_authority[0])
                    return
                raise RuntimeError(
                    f"protected sandbox has conflicting bindings for {destination}"
                )
            token, source_index = stage_source(source, option == "--bind")
            snapshot = snapshots.get((resolved_source, destination))
            if snapshot is not None:
                if option != "--ro-bind":
                    raise RuntimeError("snapshot binding must be read-only")
                accepted_snapshots.append(_canonical_json({
                    "schema": "pdd-snapshot-binding-record-v1",
                    "source_index": source_index,
                    "attestation": snapshot.attestation,
                }))
                accepted_snapshot_details[snapshot.attestation] = (
                    source_index, destination
                )
            mounted[destination] = (
                option, resolved_source, category, source_index
            )
            ensure_destination_parent(destination)
            mount_argv = deferred_readable_mounts if defer_mount else argv
            mount_argv.extend((option, token, str(destination)))
            if destination.is_dir():
                destination_dirs.add(destination)

        for source, destination in writable_bindings:
            bind("--bind", source.resolve(), destination, category="writable")
        for source, destination in readable_bindings:
            bind(
                "--ro-bind", source.resolve(), destination,
                category="declared_readable", defer_mount=True,
            )
        for item in _runtime_roots(command, workdir):
            # A host bind follows symlinks, but the process command and ELF
            # loader retain their original spellings in the new namespace.
            bind(
                "--ro-bind", item.resolve(), item, category="inferred_runtime"
            )
        # Nested declared toolchain mounts must be installed after broader
        # inferred roots or Bubblewrap would hide them with the later root bind.
        argv.extend(deferred_readable_mounts)
        # The root status supervisor moves only its forked child into this leaf
        # before ``setpriv`` drops the candidate's authority to alter cgroups.
        argv.extend(("--bind", "@PDD-CGROUP@", "/sys/fs/cgroup"))
        # ``setpriv`` and the root helper interpreter execute after the
        # namespace root is installed. Bind each exact invoked spelling with
        # only its ELF closure and selected native Python stdlib root.
        trusted_runtime_executables = (
            *((tools.mount,) if not playwright_aggregate else ()),
            tools.setpriv, tools.helper_python,
        )
        for executable in trusted_runtime_executables:
            for item in (
                executable, *_linked_libraries(executable),
                *_native_python_runtime_roots(executable),
            ):
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
        drop = [
            str(tools.setpriv), "--reuid", str(candidate_uid),
            "--regid", str(candidate_gid), "--clear-groups", "--",
        ]
        if candidate_environment_values is not None:
            if candidate_temp_directory is None or supervision_token is None:
                raise RuntimeError("protected candidate environment is invalid")
            candidate_environment = _candidate_environment_record(
                candidate_environment_values,
                temp_directory=candidate_temp_directory,
                supervision_token=supervision_token,
            )
        sandboxed = _limited_command(command, limits, candidate_environment)
        if result_fifo is not None:
            sandboxed = _framework_observation_command(
                sandboxed, result_fd, _FRAMEWORK_OBSERVATION_PATH
            )
        elif result_write_fd is not None:
            if (
                playwright_snapshot_aggregate is not None
                and playwright_snapshot_aggregate.result_fd != result_fd
            ):
                raise RuntimeError("Playwright observation descriptor mismatch")
            sandboxed = _anonymous_framework_observation_command(
                sandboxed, result_fd,
                seal_cross_process=standard_anonymous,
            )
        status_fd = 4 if result_write_fd is not None else 3
        inner_source = (
            _UNSEALED_INNER_STATUS_SUPERVISOR_SOURCE
            if playwright_aggregate else _INNER_STATUS_SUPERVISOR_SOURCE
        )
        seal_arguments = (
            ("@PDD-SEAL-COORDINATOR-PROC-FD@", str(tools.mount))
            if not playwright_aggregate else ()
        )
        argv.extend((
            "--", str(tools.helper_python), "-I", "-S", "-c",
            inner_source, str(status_fd),
            "@PDD-TERMINATION-TOKEN@", "/sys/fs/cgroup",
            *seal_arguments, *drop, *sandboxed,
        ))
        if consumed_proofs != proofs.keys():
            raise RuntimeError("protected sandbox has unused immutable binding proof")
        if len(accepted_snapshots) != len(snapshots):
            raise RuntimeError("protected sandbox has unused snapshot binding proof")
        aggregate_record = None
        if aggregate_payload is not None:
            protocol_members = []
            for member in aggregate_payload["members"]:
                detail = accepted_snapshot_details.get(member["attestation"])
                if detail is None:
                    raise RuntimeError("Playwright aggregate snapshot is not mounted")
                source_index, destination = detail
                protocol_members.append({
                    "role": member["role"], "source_index": source_index,
                    "destination": str(destination),
                    "attestation": member["attestation"],
                })
            aggregate_record = _canonical_json({
                "schema": _PLAYWRIGHT_AGGREGATE_RECORD_SCHEMA,
                "aggregate_attestation": playwright_snapshot_aggregate.attestation,
                "expected_digest": playwright_snapshot_aggregate.digest,
                "accepted_toolchain_identity": (
                    playwright_snapshot_aggregate.accepted_toolchain_identity
                ),
                "result_fd": playwright_snapshot_aggregate.result_fd,
                "members": protocol_members,
            })
        return _staged_bwrap(
            argv, sources, path_tokens, writable_roots=storage_roots,
            writable_specs=writable_specs,
            immutable_binding_proofs=tuple(accepted_records),
            snapshot_binding_proofs=tuple(accepted_snapshots),
            playwright_aggregate_record=aggregate_record,
            candidate_identity=candidate_identity,
            unit_name=unit_name or _scope_unit_name(),
            control_directory=control_directory or (
                Path(tempfile.gettempdir()) / f"pdd-scope-{uuid.uuid4().hex}"
            ),
            limits=limits, candidate_timeout=candidate_timeout, tools=tools,
            observation_nonce=observation_nonce,
            staging_bytes=_snapshot_staging_bytes(
                sources, accepted_snapshots, tuple(accepted_immutable_records)
            ),
        )
    raise RuntimeError("unsupported sandbox platform or mechanism")


def _write_all_descriptor_bytes(
    descriptor: int, data: bytes, deadline: float,
) -> None:
    """Forward one validated observation without accepting partial writes."""
    _write_descriptor_bytes(descriptor, data, deadline)


def _run_playwright_descriptor_supervised(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...], limits: SupervisorLimits,
    readable_roots: tuple[Path, ...],
    readable_bindings: tuple[tuple[Path, Path], ...],
    immutable_binding_proofs: tuple[ImmutableBindingProof, ...],
    snapshot_binding_proofs: tuple[SnapshotBindingProof, ...],
    playwright_snapshot_aggregate: PlaywrightSnapshotAggregate | None,
    writable_bindings: tuple[tuple[Path, Path], ...],
    temp_directory: Path | None, result_write_fd: int, result_fd: int,
) -> tuple[SupervisedCompletedProcess, bool]:
    """Run anonymous framework evidence over bounded inherited descriptors."""
    # pylint: disable=too-many-locals,too-many-arguments,too-many-branches
    # pylint: disable=too-many-statements,consider-using-with
    supervision_token = _fresh_supervision_token()
    nonce = os.urandom(32).hex()
    diagnostics = bytearray()
    helper_stderr = bytearray()
    process: subprocess.Popen[bytes] | None = None
    stderr_reader: threading.Thread | None = None
    plan: _ScopePlan | None = None
    cgroup: Path | None = None
    memory_before: dict[str, int] = {}
    pids_before: dict[str, int] = {}
    timed_out = False
    candidate_returncode = 125
    failed_closed = False
    resource_limit: str | None = None
    resource_telemetry: CgroupResourceTelemetry | None = None
    phase = "construction"
    failure_phases: list[InfrastructureFailurePhase] = []
    scope_setup_subreason: ScopeSetupFailureReason | None = None
    candidate_stdout = b""
    candidate_stderr = b""

    phase_values = {
        "construction": InfrastructureFailurePhase.CONSTRUCTION,
        "launch": InfrastructureFailurePhase.LAUNCH,
        "scope-setup": InfrastructureFailurePhase.SCOPE_SETUP,
        "candidate-execution": InfrastructureFailurePhase.CANDIDATE_EXECUTION,
        "trusted-postprocessing": InfrastructureFailurePhase.TRUSTED_POSTPROCESSING,
        "result-handoff": InfrastructureFailurePhase.RESULT_HANDOFF,
    }

    def mark_failure(value: InfrastructureFailurePhase | None = None) -> None:
        trusted = value or phase_values.get(
            phase, InfrastructureFailurePhase.UNKNOWN
        )
        if trusted not in failure_phases:
            failure_phases.append(trusted)

    def add_diagnostic(value: str) -> None:
        remaining = max(0, limits.max_output_bytes - len(diagnostics))
        diagnostics.extend(value.encode("utf-8", errors="replace")[:remaining])

    def read_stderr(stream) -> None:
        while chunk := stream.read(65536):
            remaining = max(0, limits.max_output_bytes - len(helper_stderr))
            helper_stderr.extend(chunk[:remaining])

    try:
        endpoint = os.fstat(result_write_fd)
        if not stat.S_ISFIFO(endpoint.st_mode) or os.get_inheritable(result_write_fd):
            raise RuntimeError("invalid anonymous observation endpoint")
        with tempfile.TemporaryDirectory(prefix="pdd-scope-") as control_value:
            control = Path(control_value)
            argv, plan = _sandbox_command(
                command, writable_roots, cwd=cwd, limits=limits,
                readable_roots=readable_roots, readable_bindings=readable_bindings,
                immutable_binding_proofs=immutable_binding_proofs,
                snapshot_binding_proofs=snapshot_binding_proofs,
                playwright_snapshot_aggregate=playwright_snapshot_aggregate,
                writable_bindings=writable_bindings, result_write_fd=result_write_fd,
                result_fd=result_fd, observation_nonce=nonce, candidate_timeout=timeout,
                unit_name=_scope_unit_name(), control_directory=control,
                candidate_environment_values=env,
                candidate_temp_directory=(
                    temp_directory or writable_roots[0].resolve()
                ),
                supervision_token=supervision_token,
            )
            _prepare_staging(plan)
            _revalidate_trusted_tools(plan.tools)
            phase = "launch"
            process = subprocess.Popen(
                argv, cwd=Path("/"), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, env=_privileged_helper_environment(),
                start_new_session=True,
            )
            assert process.stdin is not None and process.stdout is not None and process.stderr is not None
            stderr_reader = threading.Thread(target=read_stderr, args=(process.stderr,), daemon=True)
            stderr_reader.start()
            phase = "scope-setup"
            _write_descriptor_frame_fd(
                process.stdin.fileno(), plan.launch_payload or {},
                _DESCRIPTOR_PROTOCOL_MAX_LAUNCH_BYTES,
                time.monotonic() + _TRUSTED_SETUP_SECONDS,
            )
            ready = _read_descriptor_frame_fd(
                process.stdout.fileno(), _DESCRIPTOR_PROTOCOL_MAX_CONTROL_BYTES,
                time.monotonic() + _TRUSTED_SETUP_SECONDS,
            )
            if ready != {"kind": "ready", "nonce": nonce}:
                setup_reason = _scope_setup_error_reason(ready, nonce)
                if setup_reason is None:
                    raise RuntimeError("protected descriptor ready frame is invalid")
                scope_setup_subreason = setup_reason
                raise RuntimeError("protected scope setup failed")
            cgroup, memory_before, pids_before = _probe_scope(plan, limits)
            _write_descriptor_frame_fd(
                process.stdin.fileno(), {"kind": "start", "nonce": nonce},
                _DESCRIPTOR_PROTOCOL_MAX_CONTROL_BYTES,
                time.monotonic() + _TRUSTED_COMMAND_SECONDS,
            )
            phase = "candidate-execution"
            payload = _read_descriptor_frame_fd(
                process.stdout.fileno(), _DESCRIPTOR_PROTOCOL_MAX_RESULT_BYTES,
                time.monotonic() + timeout + _TRUSTED_POSTPROCESS_SECONDS,
            )
            phase = "result-handoff"
            expected_aggregate = (
                playwright_snapshot_aggregate.digest
                if playwright_snapshot_aggregate is not None
                else _STANDARD_ANONYMOUS_AGGREGATE_DIGEST
            )
            result = _descriptor_result(
                payload, nonce, expected_aggregate, limits.max_output_bytes,
            )
            candidate_returncode = result.candidate.returncode
            timed_out = result.candidate.timed_out
            candidate_stdout = result.stdout
            candidate_stderr = result.stderr
            if candidate_returncode == 124 and not timed_out:
                raise RuntimeError("candidate used reserved exit status 124")
            # The helper holds the candidate leaf until this acknowledgement.
            # Capture authoritative kernel deltas before permitting that cleanup.
            resource_telemetry = _cgroup_resource_telemetry(
                memory_before,
                _cgroup_events(cgroup, "memory.events"),
                pids_before,
                _cgroup_events(cgroup, "pids.events"),
            )
            if max(
                resource_telemetry.memory_oom_delta,
                resource_telemetry.memory_oom_kill_delta,
            ) > 0:
                resource_limit = "memory"
            elif resource_telemetry.pids_max_delta > 0:
                resource_limit = "pids"
            handoff_deadline = time.monotonic() + _TRUSTED_POSTPROCESS_SECONDS
            _write_all_descriptor_bytes(
                result_write_fd, result.observation, handoff_deadline
            )
            _write_descriptor_frame_fd(
                process.stdin.fileno(),
                {
                    "kind": "ack", "nonce": nonce,
                    "digest": hashlib.sha256(
                        _canonical_json(payload).encode("utf-8")
                    ).hexdigest(),
                },
                _DESCRIPTOR_PROTOCOL_MAX_CONTROL_BYTES,
                handoff_deadline,
            )
            process.stdin.close()
            process.wait(timeout=_TRUSTED_POSTPROCESS_SECONDS)
            _expect_descriptor_eof(
                process.stdout.fileno(), time.monotonic() + _TRUSTED_COMMAND_SECONDS
            )
            expected_helper_exit = (
                candidate_returncode if candidate_returncode >= 0
                else 128 - candidate_returncode
            )
            if process.returncode != expected_helper_exit:
                raise RuntimeError("protected descriptor helper exit status mismatch")
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as exc:
        failed_closed = True
        if (
            phase == "scope-setup"
            and scope_setup_subreason is None
            and process is not None
            and process.poll() is not None
        ):
            scope_setup_subreason = ScopeSetupFailureReason.LAUNCH_EXIT
        mark_failure()
        add_diagnostic(f"protected supervisor phase={phase}: {exc}\n")
    finally:
        if process is not None and process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        if plan is not None:
            try:
                _stop_scope(plan.unit_name, plan.tools)
            except RuntimeError as exc:
                failed_closed = True
                mark_failure(InfrastructureFailurePhase.SCOPE_CLEANUP)
                add_diagnostic(f"protected supervisor phase=scope-cleanup: {exc}\n")
        if process is not None:
            try:
                process.wait(timeout=_TRUSTED_COMMAND_SECONDS)
            except subprocess.TimeoutExpired:
                failed_closed = True
                mark_failure(InfrastructureFailurePhase.SCOPE_CLEANUP)
                mark_failure(InfrastructureFailurePhase.PROCESS_CLEANUP)
                add_diagnostic("protected supervisor phase=scope-cleanup: helper did not terminate\n")
        if plan is not None:
            try:
                _cleanup_staging(plan)
            except RuntimeError as exc:
                failed_closed = True
                mark_failure(InfrastructureFailurePhase.MOUNT_CLEANUP)
                add_diagnostic(f"protected supervisor phase=mount-cleanup: {exc}\n")
        for thread in (stderr_reader,):
            if thread is not None:
                thread.join(timeout=1)
                if thread.is_alive():
                    failed_closed = True
                    mark_failure(InfrastructureFailurePhase.OUTPUT_DRAIN)
                    add_diagnostic("protected descriptor transport did not close\n")
    return _supervised_result(
        command,
        125 if failed_closed else (124 if timed_out else candidate_returncode),
        candidate_stdout[:limits.max_output_bytes].decode("utf-8", errors="replace"),
        (candidate_stderr + bytes(helper_stderr) + bytes(diagnostics))[:limits.max_output_bytes].decode(
            "utf-8", errors="replace"
        ),
        (
            _sandbox_termination(
                tuple(failure_phases),
                resource_telemetry=resource_telemetry,
                scope_setup_subreason=scope_setup_subreason,
            )
            if failed_closed else _termination_evidence(
                124 if timed_out else candidate_returncode,
                timed_out=timed_out, timeout_seconds=timeout,
                resource_limit=resource_limit,
                resource_telemetry=resource_telemetry,
            )
        ),
    ), False


def run_supervised(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...],
    limits: SupervisorLimits = SupervisorLimits(),
    readable_roots: tuple[Path, ...] = (),
    readable_bindings: tuple[tuple[Path, Path], ...] = (),
    immutable_binding_proofs: tuple[ImmutableBindingProof, ...] = (),
    snapshot_binding_proofs: tuple[SnapshotBindingProof, ...] = (),
    playwright_snapshot_aggregate: PlaywrightSnapshotAggregate | None = None,
    writable_bindings: tuple[tuple[Path, Path], ...] = (),
    temp_directory: Path | None = None,
    result_fifo: Path | None = None,
    result_write_fd: int | None = None,
    result_fd: int = 198,
) -> tuple[subprocess.CompletedProcess[str], bool]:
    """Run after proving one delegated candidate leaf, then remove its scope."""
    # pylint: disable=consider-using-with,too-many-locals,too-many-branches,too-many-statements,too-many-return-statements
    if result_write_fd is not None:
        if result_fifo is not None:
            return _sandbox_error(
                command,
                "protected supervisor phase=construction: conflicting descriptor endpoint",
                failure_phases=(InfrastructureFailurePhase.CONSTRUCTION,),
            )
        return _run_playwright_descriptor_supervised(
            command, cwd=cwd, timeout=timeout, env=env, writable_roots=writable_roots,
            limits=limits, readable_roots=readable_roots,
            readable_bindings=readable_bindings,
            immutable_binding_proofs=immutable_binding_proofs,
            snapshot_binding_proofs=snapshot_binding_proofs,
            playwright_snapshot_aggregate=playwright_snapshot_aggregate,
            writable_bindings=writable_bindings, temp_directory=temp_directory,
            result_write_fd=result_write_fd, result_fd=result_fd,
        )
    if playwright_snapshot_aggregate is not None:
        return _sandbox_error(
            command,
            "protected supervisor phase=construction: invalid Playwright descriptor endpoint",
            failure_phases=(InfrastructureFailurePhase.CONSTRUCTION,),
        )
    token = _fresh_supervision_token()
    observation_nonce = os.urandom(32).hex() if result_write_fd is not None else None
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
    resource_limit: str | None = None
    resource_telemetry: CgroupResourceTelemetry | None = None
    process: subprocess.Popen[bytes] | None = None
    plan: _ScopePlan | None = None
    cgroup: Path | None = None
    memory_before: dict[str, int] = {}
    pids_before: dict[str, int] = {}
    tracked: dict[int, str | None] = {}
    phase = "construction"
    failure_phases: list[InfrastructureFailurePhase] = []

    phase_values = {
        "construction": InfrastructureFailurePhase.CONSTRUCTION,
        "launch": InfrastructureFailurePhase.LAUNCH,
        "launch-handoff": InfrastructureFailurePhase.LAUNCH,
        "scope-setup": InfrastructureFailurePhase.SCOPE_SETUP,
        "candidate-execution": InfrastructureFailurePhase.CANDIDATE_EXECUTION,
        "trusted-postprocessing": InfrastructureFailurePhase.TRUSTED_POSTPROCESSING,
        "result-handoff": InfrastructureFailurePhase.RESULT_HANDOFF,
    }

    def mark_failure(value: InfrastructureFailurePhase | None = None) -> None:
        trusted = value or phase_values.get(
            phase, InfrastructureFailurePhase.UNKNOWN
        )
        if trusted not in failure_phases:
            failure_phases.append(trusted)

    if result_write_fd is not None:
        try:
            endpoint = os.fstat(result_write_fd)
        except OSError as exc:
            return _sandbox_error(
                command,
                f"protected supervisor phase=construction: {exc}",
                failure_phases=(InfrastructureFailurePhase.CONSTRUCTION,),
            )
        if not stat.S_ISFIFO(endpoint.st_mode) or os.get_inheritable(result_write_fd):
            return _sandbox_error(
                command,
                "protected supervisor phase=construction: invalid anonymous observation endpoint",
                failure_phases=(InfrastructureFailurePhase.CONSTRUCTION,),
            )

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
        mark_failure()
        add_diagnostic(f"protected supervisor phase={phase}: {error}\n")
        return True

    def record_events() -> None:
        nonlocal resource_limit, resource_telemetry
        if cgroup is None:
            return
        memory_after = _cgroup_events(cgroup, "memory.events")
        pids_after = _cgroup_events(cgroup, "pids.events")
        resource_telemetry = _cgroup_resource_telemetry(
            memory_before, memory_after, pids_before, pids_after,
        )
        oom_delta = max(
            resource_telemetry.memory_oom_delta,
            resource_telemetry.memory_oom_kill_delta,
        )
        pids_delta = resource_telemetry.pids_max_delta
        if oom_delta > 0:
            resource_limit = "memory"
            add_diagnostic(f"cgroup memory.events oom delta={oom_delta}\n")
        if pids_delta > 0:
            resource_limit = "pids"
            add_diagnostic(f"cgroup pids.events max delta={pids_delta}\n")

    try:
        with tempfile.TemporaryDirectory(prefix="pdd-scope-") as control_value:
            control = Path(control_value)
            authority = control / "authority"
            result_path = control / "result.json"
            try:
                argv, plan = _sandbox_command(
                    command, writable_roots, cwd=cwd,
                    limits=limits, readable_roots=readable_roots,
                    readable_bindings=readable_bindings,
                    immutable_binding_proofs=immutable_binding_proofs,
                    snapshot_binding_proofs=snapshot_binding_proofs,
                    playwright_snapshot_aggregate=playwright_snapshot_aggregate,
                    writable_bindings=writable_bindings,
                    result_fifo=result_fifo, result_write_fd=result_write_fd,
                    result_fd=result_fd, observation_nonce=observation_nonce,
                    candidate_timeout=timeout,
                    unit_name=unit_name, control_directory=control,
                    candidate_environment_values=env,
                    candidate_temp_directory=(
                        temp_directory or writable_roots[0].resolve()
                    ),
                    supervision_token=token,
                )
                _prepare_staging(plan)
            except (OSError, RuntimeError) as exc:
                return _sandbox_error(
                    command,
                    f"protected supervisor phase=construction: {exc}",
                    failure_phases=(InfrastructureFailurePhase.CONSTRUCTION,),
                )
            try:
                _revalidate_trusted_tools(plan.tools)
                process = subprocess.Popen(
                    argv, cwd=Path("/"), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    env=_privileged_helper_environment(), start_new_session=True,
                )
            except OSError as exc:
                try:
                    _cleanup_staging(plan)
                except RuntimeError as cleanup_exc:
                    return _sandbox_error(
                        command,
                        "protected supervisor phase=launch: "
                        f"{exc}; cleanup failed: {cleanup_exc}",
                        failure_phases=(
                            InfrastructureFailurePhase.LAUNCH,
                            InfrastructureFailurePhase.MOUNT_CLEANUP,
                        ),
                    )
                return _sandbox_error(
                    command,
                    f"protected supervisor phase=launch: {exc}",
                    failure_phases=(InfrastructureFailurePhase.LAUNCH,),
                )

            assert process.stdin is not None and process.stdout is not None and process.stderr is not None
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

            try:
                phase = "launch-handoff"
                if plan.launch_payload is None:
                    raise RuntimeError("protected launch descriptor is unavailable")
                _write_descriptor_frame_fd(
                    process.stdin.fileno(), plan.launch_payload,
                    _DESCRIPTOR_PROTOCOL_MAX_LAUNCH_BYTES,
                    time.monotonic() + _TRUSTED_SETUP_SECONDS,
                )
                process.stdin.close()
                setup_deadline = time.monotonic() + _TRUSTED_SETUP_SECONDS
                phase = "scope-setup"
                while not (control / "ready").exists():
                    if process.poll() is not None:
                        raise RuntimeError("protected scope exited before verification")
                    if time.monotonic() >= setup_deadline:
                        failed_closed = True
                        mark_failure(InfrastructureFailurePhase.SCOPE_SETUP)
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
                            mark_failure(
                                InfrastructureFailurePhase.CANDIDATE_EXECUTION
                            )
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
                        result_path = (
                            authority / "result.json"
                            if result_write_fd is not None else control / "result.json"
                        )
                        postprocess_deadline = min(
                            helper_deadline,
                            time.monotonic() + _TRUSTED_POSTPROCESS_SECONDS,
                        )
                        while not result_path.exists():
                            if process.poll() is not None:
                                break
                            if time.monotonic() >= postprocess_deadline:
                                failed_closed = True
                                mark_failure(
                                    InfrastructureFailurePhase.TRUSTED_POSTPROCESSING
                                )
                                add_diagnostic(
                                    "protected supervisor trusted postprocessing "
                                    "did not finish\n"
                                )
                                break
                            if fail_for_limit():
                                break
                            time.sleep(.01)
                    if candidate_record is not None and result_path.exists():
                        phase = "result-handoff"
                        if result_write_fd is not None:
                            assert observation_nonce is not None
                            root_result = _load_root_observation_result(
                                result_path, observation_nonce, 16 * 1024 * 1024,
                            )
                            result_record = root_result.candidate
                        else:
                            result_record = _load_candidate_record(result_path)
                        if result_record != candidate_record:
                            raise RuntimeError("candidate result changed during handoff")
                        candidate_returncode = result_record.returncode
                        candidate_timed_out = result_record.timed_out
                        if result_write_fd is not None:
                            observation = _load_root_observation(
                                authority / "observation.bin", 16 * 1024 * 1024,
                                root_result.observation_digest,
                                root_result.observation_size,
                            )
                            _write_all_descriptor_bytes(
                                result_write_fd, observation,
                                min(
                                    postprocess_deadline,
                                    time.monotonic() + _TRUSTED_COMMAND_SECONDS,
                                ),
                            )
                        fail_for_limit()
                        record_events()
                    if (
                        candidate_record is None
                        and not failed_closed
                    ):
                        failed_closed = True
                        mark_failure(
                            InfrastructureFailurePhase.CANDIDATE_EXECUTION
                        )
                        add_diagnostic(
                            "protected supervisor phase=candidate-execution: "
                            "scope produced no protected candidate record\n"
                        )
                    elif (
                        not result_path.exists()
                        and not failed_closed
                    ):
                        failed_closed = True
                        mark_failure(
                            InfrastructureFailurePhase.TRUSTED_POSTPROCESSING
                        )
                        add_diagnostic(
                            "protected supervisor phase=trusted-postprocessing: "
                            "scope produced no validated result\n"
                        )
                    if (
                        candidate_returncode == 124
                        and not candidate_timed_out
                        and result_path.exists()
                        and not failed_closed
                    ):
                        failed_closed = True
                        mark_failure(InfrastructureFailurePhase.RESULT_HANDOFF)
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
                            mark_failure(InfrastructureFailurePhase.RESULT_HANDOFF)
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
                            mark_failure(InfrastructureFailurePhase.RESULT_HANDOFF)
                            add_diagnostic(
                                "protected supervisor phase=result-handoff: "
                                "helper exit status mismatch\n"
                            )
                    if (control / "cleanup-error").exists():
                        failed_closed = True
                        mark_failure(InfrastructureFailurePhase.MOUNT_CLEANUP)
                        add_diagnostic(
                            "protected supervisor phase=mount-cleanup: "
                            "privileged helper cleanup failed\n"
                        )
            except (OSError, ValueError, KeyError, RuntimeError) as exc:
                failed_closed = True
                mark_failure()
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
                        mark_failure(InfrastructureFailurePhase.SCOPE_CLEANUP)
                        add_diagnostic(
                            "protected supervisor phase=scope-cleanup: "
                            "helper did not terminate\n"
                        )
                try:
                    _stop_scope(plan.unit_name, plan.tools)
                except RuntimeError as exc:
                    failed_closed = True
                    mark_failure(InfrastructureFailurePhase.SCOPE_CLEANUP)
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
                    mark_failure(InfrastructureFailurePhase.SCOPE_CLEANUP)
                    add_diagnostic(
                        "protected supervisor phase=scope-cleanup: "
                        "helper did not terminate after scope stop\n"
                    )
                try:
                    _cleanup_staging(plan)
                except RuntimeError as exc:
                    failed_closed = True
                    mark_failure(InfrastructureFailurePhase.MOUNT_CLEANUP)
                    add_diagnostic(f"protected supervisor phase=mount-cleanup: {exc}\n")
    finally:
        for output_thread in output_threads:
            output_thread.join(timeout=1)
            if output_thread.is_alive():
                failed_closed = True
                mark_failure(InfrastructureFailurePhase.OUTPUT_DRAIN)
                add_diagnostic("protected supervisor output drain did not finish\n")
        observed = set()
        if process is not None:
            try:
                observed = _supervised_descendants(token)
                observed.discard(process.pid)
            except RuntimeError as exc:
                failed_closed = True
                mark_failure(InfrastructureFailurePhase.PROCESS_CLEANUP)
                add_diagnostic(f"protected supervisor process cleanup failed: {exc}\n")
        for pid in observed:
            tracked.setdefault(pid, _process_identity(pid))
        descendants = _live_processes(tracked)
        if descendants:
            surviving = True
            failed_closed = True
            mark_failure(InfrastructureFailurePhase.PROCESS_CLEANUP)
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
        mark_failure(InfrastructureFailurePhase.OUTPUT_DRAIN)
    returncode = 125 if failed_closed else (
        124 if candidate_timed_out else candidate_returncode
    )
    if returncode is None:
        returncode = 125
    return _supervised_result(
        command,
        returncode,
        stdout_bytes.decode("utf-8", errors="replace"),
        stderr_bytes.decode("utf-8", errors="replace"),
        (
            _sandbox_termination(
                tuple(failure_phases),
                resource_telemetry=resource_telemetry,
            )
            if failed_closed else _termination_evidence(
                returncode, timed_out=candidate_timed_out, timeout_seconds=timeout,
                resource_limit=resource_limit,
                resource_telemetry=resource_telemetry,
            )
        ),
    ), surviving
