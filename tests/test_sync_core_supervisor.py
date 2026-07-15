"""Adversarial tests for complete protected subprocess supervision."""

import base64
import io
import os
import hashlib
import inspect
import json
import math
import select
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from dataclasses import replace
from pathlib import Path
from pathlib import PurePosixPath
from types import SimpleNamespace

import pytest

from pdd.sync_core import supervisor
from pdd.sync_core.supervisor import (
    ImmutableBindingProof,
    SupervisorLimits,
    _linked_libraries,
    _limited_command,
    _live_processes,
    _framework_observation_command,
    _sandbox_library_path,
    _sandbox_command,
    _runtime_directories,
    run_supervised,
)


def _mock_linux_tools(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> dict[str, str]:
    """Install regular executable identities for trusted-tool construction tests."""
    tools = {}
    directory = tmp_path / "trusted-tools"
    directory.mkdir(exist_ok=True)
    for name in (
        "bwrap", "mount", "setpriv", "sudo", "systemctl", "systemd-run", "umount",
        "unshare",
    ):
        path = directory / name
        path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        path.chmod(0o755)
        tools[name] = str(path)
    monkeypatch.setattr(shutil, "which", lambda name, path=None: tools.get(name))
    # These unit tests inspect command construction on macOS with synthetic
    # paths. Production identity validation is covered separately below.
    def fake_identity(name: str):
        path = Path(tools[name])
        metadata = path.stat()
        return supervisor._ExecutableIdentity(
            path,
            (metadata.st_dev, metadata.st_ino, stat.S_IMODE(metadata.st_mode),
             0, metadata.st_size, metadata.st_mtime_ns),
            hashlib.sha256(path.read_bytes()).hexdigest(),
        )
    monkeypatch.setattr(supervisor, "_trusted_executable", fake_identity)
    monkeypatch.setattr(
        supervisor, "_trusted_helper_python", lambda: fake_identity("bwrap")
    )
    monkeypatch.setattr(supervisor, "_revalidate_trusted_tools", lambda _tools: None)
    return tools


def test_privileged_helper_environment_excludes_hostile_python_startup() -> None:
    """The root helper never inherits candidate Python startup controls."""
    assert supervisor._privileged_helper_environment() == {
        "HOME": "/root", "LANG": "C", "LC_ALL": "C",
        "PATH": supervisor._TRUSTED_ROOT_PATH,
    }


def test_candidate_environment_record_is_canonical_and_complete(tmp_path: Path) -> None:
    """The handoff preserves required values and injects trusted runtime values."""
    environment = {
        "HOME": str(tmp_path / "home"),
        "NODE_ENV": "test",
        "NODE_PATH": "/opt/node_modules",
        "PLAYWRIGHT_BROWSERS_PATH": "/opt/browsers",
        "PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1",
        "PYTHONNOUSERSITE": "1",
        "XDG_CACHE_HOME": str(tmp_path / "cache"),
    }
    encoded = supervisor._candidate_environment_record(
        environment, temp_directory=Path("/tmp"), supervision_token="a" * 32
    )

    parsed = supervisor._parse_candidate_environment_record(encoded)

    assert parsed == environment | {
        "LD_LIBRARY_PATH": supervisor._sandbox_library_path(environment),
        "PATH": supervisor._TRUSTED_ROOT_PATH,
        "PDD_SUPERVISION_TOKEN": "a" * 32,
        "PYTHONDONTWRITEBYTECODE": "1",
        "TEMP": "/tmp", "TMP": "/tmp", "TMPDIR": "/tmp",
    }
    assert list(parsed) == sorted(parsed)


@pytest.mark.parametrize(
    "payload",
    [
        {},
        [["A"]],
        [["A", "1"], ["A", "2"]],
        [["1BAD", "value"]],
        [["GITHUB_TOKEN", "secret"]],
        [["A", "x" * (32 * 1024 + 1)]],
        [[f"K{index}", "v"] for index in range(129)],
    ],
    ids=("shape", "entry-shape", "duplicate", "key", "credential", "value-size", "count"),
)
def test_candidate_environment_parser_rejects_invalid_records(payload) -> None:
    """Malformed, duplicate, credential-bearing, and oversized records fail closed."""
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    with pytest.raises(RuntimeError, match="candidate environment"):
        supervisor._parse_candidate_environment_record(encoded)


@pytest.mark.skipif(not sys.platform.startswith("linux"), reason="requires Linux rlimits")
def test_limited_wrapper_installs_exact_candidate_environment(tmp_path: Path) -> None:
    """The post-drop wrapper clears ambient values before candidate execution."""
    record = supervisor._candidate_environment_record(
        {"HOME": str(tmp_path), "NODE_ENV": "test"},
        temp_directory=tmp_path,
        supervision_token="b" * 32,
    )
    command = supervisor._limited_command(
        [sys.executable, "-c", "import json,os;print(json.dumps(dict(os.environ),sort_keys=True))"],
        replace(SupervisorLimits(), max_virtual_memory_bytes=512 * 1024 * 1024),
        record,
    )

    completed = subprocess.run(
        command, capture_output=True, text=True, check=False, timeout=10,
        env={"HOST_SECRET": "must-not-survive"},
    )

    assert completed.returncode == 0, completed.stderr
    assert json.loads(completed.stdout) == supervisor._parse_candidate_environment_record(record)


@pytest.mark.parametrize("swap", ["content", "mode", "rename", "symlink"])
def test_privileged_helper_rejects_executable_swaps(
    tmp_path: Path, swap: str,
) -> None:
    """Digest, metadata, and path replacement changes all fail closed."""
    executable = tmp_path / "tool"
    executable.write_bytes(b"trusted")
    executable.chmod(0o755)
    measured = supervisor._executable_identity(executable, require_root=False)
    if swap == "content":
        executable.write_bytes(b"replacement")
    elif swap == "mode":
        executable.chmod(0o777)
    else:
        original = tmp_path / "original"
        executable.rename(original)
        if swap == "symlink":
            executable.symlink_to(original)
        else:
            executable.write_bytes(b"replacement")
            executable.chmod(0o755)
    with pytest.raises(RuntimeError, match="identity changed"):
        supervisor._revalidate_executable(measured)


def test_privileged_helper_rejects_user_owned_executable(tmp_path: Path) -> None:
    """A caller-controlled PATH result cannot become a privileged tool."""
    executable = tmp_path / "tool"
    executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    executable.chmod(0o755)
    with pytest.raises(RuntimeError, match="ancestor|root-owned"):
        supervisor._executable_identity(executable)


def test_helper_snapshot_rejects_attested_file_swap(tmp_path: Path) -> None:
    """The helper copies only bytes that still match the runner attestation."""
    from pdd.sync_core.runner import _snapshot_binding_proof  # pylint: disable=import-outside-toplevel

    source = tmp_path / "toolchain"
    source.mkdir()
    member = source / "launcher"
    member.write_bytes(b"measured")
    proof = _snapshot_binding_proof(source, Path("/opt/toolchain"))
    member.write_bytes(b"swapped-and-restored-later")
    target = tmp_path / "snapshot"
    target.mkdir()
    namespace = {
        "hashlib": hashlib, "json": json, "os": os, "pathlib": __import__("pathlib"),
        "stat": stat,
    }
    exec(supervisor._SNAPSHOT_STAGING_SOURCE, namespace)  # pylint: disable=exec-used
    with pytest.raises(RuntimeError, match="snapshot attestation"):
        namespace["_stage_snapshot"](
            json.dumps({
                "schema": "pdd-snapshot-binding-record-v1", "source_index": 0,
                "attestation": proof.attestation,
            }, sort_keys=True, separators=(",", ":")), source, target,
        )


def test_snapshot_staging_applies_attested_directory_root_mode(
    tmp_path: Path,
) -> None:
    """The production helper makes a normal 0755 snapshot root traversable."""
    from pdd.sync_core.runner import _snapshot_binding_proof  # pylint: disable=import-outside-toplevel

    source = tmp_path / "source"
    source.mkdir(mode=0o755)
    (source / "nested").mkdir(mode=0o755)
    (source / "nested/member").write_bytes(b"measured")
    proof = _snapshot_binding_proof(source, Path("/opt/toolchain"))
    target = tmp_path / "snapshot"
    target.mkdir(mode=0o700)
    namespace = {
        "hashlib": hashlib, "json": json, "os": os,
        "pathlib": __import__("pathlib"), "stat": stat,
    }
    exec(supervisor._SNAPSHOT_STAGING_SOURCE, namespace)  # pylint: disable=exec-used
    record = json.dumps({
        "schema": "pdd-snapshot-binding-record-v1", "source_index": 0,
        "attestation": proof.attestation,
    }, sort_keys=True, separators=(",", ":"))

    namespace["_stage_snapshot"](record, source, target)
    namespace["_verify_staged_snapshot"](record, target)

    assert stat.S_IMODE(target.stat().st_mode) == 0o755
    assert (target / "nested/member").read_bytes() == b"measured"


def test_snapshot_staging_copies_attested_root_file(tmp_path: Path) -> None:
    """A file-root snapshot duplicates its verified source descriptor before copy."""
    from pdd.sync_core.runner import _snapshot_binding_proof  # pylint: disable=import-outside-toplevel

    source = tmp_path / "reporter.cjs"
    source.write_bytes(b"module.exports = class Reporter {};\n")
    source.chmod(0o444)
    proof = _snapshot_binding_proof(source, Path("/opt/reporter.cjs"))
    target = tmp_path / "snapshot"
    target.touch(mode=0o600)
    namespace = {
        "hashlib": hashlib, "json": json, "os": os,
        "pathlib": __import__("pathlib"), "stat": stat,
    }
    exec(supervisor._SNAPSHOT_STAGING_SOURCE, namespace)  # pylint: disable=exec-used
    record = json.dumps({
        "schema": "pdd-snapshot-binding-record-v1", "source_index": 0,
        "attestation": proof.attestation,
    }, sort_keys=True, separators=(",", ":"))

    namespace["_stage_snapshot"](record, source, target)
    namespace["_verify_staged_snapshot"](record, target)

    assert target.read_bytes() == source.read_bytes()
    assert stat.S_IMODE(target.stat().st_mode) == 0o444


def test_snapshot_staging_quota_counts_recursive_attested_files(
    tmp_path: Path,
) -> None:
    """Nested regular bytes, metadata, and headroom all contribute to tmpfs size."""
    from pdd.sync_core.runner import _snapshot_binding_proof  # pylint: disable=import-outside-toplevel

    source = tmp_path / "source"
    nested = source / "deep"
    nested.mkdir(parents=True)
    (nested / "large.bin").write_bytes(b"x" * (2 * 1024 * 1024))
    proof = _snapshot_binding_proof(source, Path("/opt/toolchain"))
    record = json.dumps({
        "schema": "pdd-snapshot-binding-record-v1", "source_index": 0,
        "attestation": proof.attestation,
    }, sort_keys=True, separators=(",", ":"))

    required = supervisor._snapshot_staging_bytes([source], [record])

    assert required > 3 * 1024 * 1024
    assert required <= supervisor._MAX_STAGING_BYTES


def test_snapshot_staging_quota_rejects_explicit_global_maximum() -> None:
    """Attested members cannot request an unbounded privileged tmpfs."""
    members = [
        {"path": ".", "kind": "directory", "mode": 0o755,
         "digest": None, "size": None, "target": None},
    ] + [
        {"path": f"large-{index}", "kind": "file", "mode": 0o644,
         "digest": "a" * 64, "size": 2 * 1024 * 1024 * 1024,
         "target": None}
        for index in range(2)
    ]
    record = json.dumps({
        "schema": "pdd-snapshot-binding-record-v1", "source_index": 0,
        "attestation": json.dumps({
            "schema": "pdd-snapshot-binding-v1", "source": "/source",
            "destination": "/target", "members": members,
        }),
    })

    with pytest.raises(RuntimeError, match="exceeds maximum"):
        supervisor._snapshot_staging_bytes([Path("/source")], [record])


def test_snapshot_staging_quota_counts_immutable_records_without_snapshots(
    tmp_path: Path,
) -> None:
    """Copied immutable runtime files reserve tmpfs before the helper starts."""
    protected = []
    records = []
    for index in range(2):
        source = tmp_path / f"native-{index}"
        source.write_bytes(bytes([index]) * (640 * 1024))
        source.chmod(0o644)
        copied = tmp_path / f"copied-{index}"
        copied.write_bytes(source.read_bytes())
        copied.chmod(0o644)
        protected.append(copied)
        records.append((index, supervisor._validate_immutable_binding_proof(
            _descriptor_runtime_proof(copied, source)
        )))

    required = supervisor._snapshot_staging_bytes(protected, [], tuple(records))

    minimum = (
        supervisor._SNAPSHOT_STAGING_HEADROOM_BYTES
        + 2 * supervisor._IMMUTABLE_STAGING_METADATA_BYTES
        + 2 * 640 * 1024
    )
    assert required >= minimum
    assert required > 1024 * 1024


def test_snapshot_staging_quota_deduplicates_snapshot_covered_immutable_source(
    tmp_path: Path,
) -> None:
    """A source represented by a snapshot record consumes its bytes only once."""
    from pdd.sync_core.runner import _snapshot_binding_proof  # pylint: disable=import-outside-toplevel

    source = tmp_path / "native"
    source.write_bytes(b"snapshot-bytes")
    source.chmod(0o644)
    copied = tmp_path / "copied"
    copied.write_bytes(source.read_bytes())
    copied.chmod(0o644)
    immutable = supervisor._validate_immutable_binding_proof(
        _descriptor_runtime_proof(copied, source)
    )
    snapshot = _snapshot_binding_proof(source, Path("/opt/native"))
    snapshot_record = json.dumps({
        "schema": "pdd-snapshot-binding-record-v1", "source_index": 0,
        "attestation": snapshot.attestation,
    }, sort_keys=True, separators=(",", ":"))

    counted = supervisor._snapshot_staging_bytes(
        [copied], [snapshot_record], ((0, replace(
            immutable, member_size=supervisor._MAX_STAGING_BYTES
        )),),
    )
    snapshot_only = supervisor._snapshot_staging_bytes(
        [copied], [snapshot_record],
    )

    assert counted == snapshot_only


@pytest.mark.parametrize(
    "records,match",
    [
        (((0, object()),), "invalid"),
        (((0, None),), "invalid"),
    ],
)
def test_snapshot_staging_quota_rejects_malformed_immutable_records(
    records: tuple[tuple[int, object], ...], match: str,
) -> None:
    """Only validated regular immutable records can affect a privileged quota."""
    with pytest.raises(RuntimeError, match=match):
        supervisor._snapshot_staging_bytes([Path("/source")], [], records)  # type: ignore[arg-type]


def test_snapshot_staging_quota_rejects_duplicate_and_over_cap_immutable_records(
    tmp_path: Path,
) -> None:
    """Duplicate accounting and any global-cap overflow fail closed."""
    source = tmp_path / "native"
    source.write_bytes(b"trusted")
    source.chmod(0o644)
    copied = tmp_path / "copied"
    copied.write_bytes(source.read_bytes())
    copied.chmod(0o644)
    record = supervisor._validate_immutable_binding_proof(
        _descriptor_runtime_proof(copied, source)
    )
    with pytest.raises(RuntimeError, match="invalid"):
        supervisor._snapshot_staging_bytes(
            [copied], [], ((0, record), (0, record))
        )
    with pytest.raises(RuntimeError, match="exceeds maximum"):
        supervisor._snapshot_staging_bytes(
            [copied], [], ((0, replace(
                record, member_size=supervisor._MAX_STAGING_BYTES
            )),),
        )


def test_immutable_quota_uses_validated_size_and_rejects_mutated_identity(
    tmp_path: Path,
) -> None:
    """Quota sizing never trusts a mutable post-validation stat result."""
    source = tmp_path / "native"
    source.write_bytes(b"trusted-size")
    source.chmod(0o644)
    copied = tmp_path / "copied"
    copied.write_bytes(source.read_bytes())
    copied.chmod(0o644)
    proof = _descriptor_runtime_proof(copied, source)
    record = supervisor._validate_immutable_binding_proof(proof)
    required = supervisor._snapshot_staging_bytes([copied], [], ((0, record),))

    copied.write_bytes(b"changed-size-and-identity")

    assert supervisor._snapshot_staging_bytes([copied], [], ((0, record),)) == required
    with pytest.raises(RuntimeError, match="immutable binding proof"):
        supervisor._validate_immutable_binding_proof(proof)


def test_linux_playwright_aggregate_binds_root_snapshot_mount_graph(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The privileged record names every typed snapshot and final destination."""
    from pdd.sync_core.runner import (  # pylint: disable=import-outside-toplevel
        PlaywrightToolchainRoles,
        _playwright_reporter_source,
        _playwright_snapshot_aggregate_identity,
        _playwright_snapshot_binding_proofs,
    )

    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: ()
    )
    toolchain = tmp_path / "toolchain"
    dependencies = toolchain / "node_modules"
    entrypoint = dependencies / "@playwright/test/cli.js"
    entrypoint.parent.mkdir(parents=True)
    entrypoint.write_text("cli", encoding="utf-8")
    launcher = toolchain / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    launcher.chmod(0o755)
    browser = toolchain / "browsers"
    browser.mkdir()
    lockfile = toolchain / "package-lock.json"
    lockfile.write_text("{}", encoding="utf-8")
    native = toolchain / "native.so"
    native.write_bytes(b"native")
    reporter = toolchain / "reporter.cjs"
    reporter.write_text(_playwright_reporter_source(198), encoding="utf-8")
    roles = PlaywrightToolchainRoles(
        launcher, entrypoint, dependencies, browser, (native,), lockfile
    )
    destination = tmp_path / "phase/node_modules"
    proofs = _playwright_snapshot_binding_proofs(
        reporter, roles, launcher, destination, roles.native_bindings
    )
    identity, aggregate = _playwright_snapshot_aggregate_identity(
        proofs, reporter, roles, launcher, destination, roles.native_bindings
    )
    aggregate_payload = json.loads(aggregate.attestation)
    assert aggregate_payload["toolchain_identity"] == identity
    assert aggregate.accepted_toolchain_identity == aggregate_payload["checker_identity"]
    scratch = tmp_path / "scratch"
    scratch.mkdir()
    read_fd, write_fd = os.pipe()
    try:
        _argv, plan = _sandbox_command(
            [str(launcher), str(destination / "@playwright/test/cli.js")],
            (scratch,),
            readable_roots=(reporter, *roles.readable_roots),
            readable_bindings=(*roles.native_bindings, (dependencies, destination)),
            snapshot_binding_proofs=proofs,
            playwright_snapshot_aggregate=aggregate,
            result_write_fd=write_fd,
            result_fd=198,
            observation_nonce="a" * 64,
        )
    finally:
        os.close(read_fd)
        os.close(write_fd)

    assert plan.launch_payload is not None
    records = [json.loads(value) for value in plan.launch_payload["proof_records"]]
    aggregate_record = next(
        record for record in records
        if record["schema"] == "pdd-playwright-snapshot-aggregate-record-v1"
    )
    bwrap = list(plan.bwrap_argv)
    assert aggregate_record["accepted_toolchain_identity"] == aggregate.accepted_toolchain_identity
    assert aggregate_record["expected_digest"] == aggregate.digest
    assert {member["role"] for member in aggregate_record["members"]} >= {
        "reporter", "launcher", "dependencies", "browser_runtime", "lockfile",
        "native_runtime/0",
    }
    for member in aggregate_record["members"]:
        assert ["--ro-bind", bwrap[bwrap.index(member["destination"]) - 1],
                member["destination"]] in [
            bwrap[index:index + 3] for index in range(len(bwrap) - 2)
        ]
    assert "--preserve-fds" not in bwrap
    assert plan.helper_source.count(
        "verify_playwright_aggregate(playwright,mapped=True)"
    ) == 2
    assert plan.control_directory / "authority" in plan.staging_targets
    assert "str(authority)" in plan.helper_source
    assert "os.chmod(authority,0o711)" in plan.helper_source
    assert "control/'observation.bin'" not in plan.helper_source
    compile(plan.helper_source, "<playwright-root-helper>", "exec")


# pylint: disable=too-many-locals,too-many-statements,protected-access
def test_playwright_launch_descriptor_bounds_privileged_argv_for_large_aggregate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Large valid Playwright authority is sent once through a bounded launch frame."""
    from pdd.sync_core.runner import (  # pylint: disable=import-outside-toplevel
        PlaywrightToolchainRoles,
        _playwright_snapshot_aggregate_identity,
        _playwright_snapshot_binding_proofs,
        _playwright_reporter_source,
    )

    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: ()
    )
    toolchain = tmp_path / "toolchain"
    dependencies = toolchain / "node_modules"
    entrypoint = dependencies / "@playwright/test/cli.js"
    entrypoint.parent.mkdir(parents=True)
    entrypoint.write_text("cli", encoding="utf-8")
    launcher = toolchain / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    launcher.chmod(0o755)
    browser = toolchain / "browsers"
    browser.mkdir()
    lockfile = toolchain / "package-lock.json"
    lockfile.write_text("{}", encoding="utf-8")
    native = toolchain / "native.so"
    native.write_bytes(b"native")
    reporter = toolchain / "reporter.cjs"
    reporter.write_text(_playwright_reporter_source(198), encoding="utf-8")
    roles = PlaywrightToolchainRoles(
        launcher, entrypoint, dependencies, browser, (native,), lockfile
    )
    destination = tmp_path / "phase/node_modules"
    proofs = _playwright_snapshot_binding_proofs(
        reporter, roles, launcher, destination, roles.native_bindings
    )
    reporter_proof = proofs[0]
    snapshot = json.loads(reporter_proof.attestation)
    snapshot["members"] = [snapshot["members"][0]] + [
        {
            "path": f"payload/{index:03d}-" + "x" * 4000,
            "kind": "file", "mode": 0o444, "digest": "0" * 64,
            "size": 0, "target": None,
        }
        for index in range(40)
    ]
    enlarged_attestation = supervisor._canonical_json(snapshot)
    assert len(enlarged_attestation.encode("utf-8")) > 131072
    enlarged_proofs = (
        replace(reporter_proof, attestation=enlarged_attestation), *proofs[1:]
    )
    _identity, aggregate = _playwright_snapshot_aggregate_identity(
        proofs, reporter, roles, launcher, destination, roles.native_bindings
    )
    aggregate_payload = json.loads(aggregate.attestation)
    aggregate_payload["members"][0]["attestation"] = enlarged_attestation
    aggregate_attestation = supervisor._canonical_json(aggregate_payload)
    aggregate = replace(
        aggregate, attestation=aggregate_attestation,
        digest=hashlib.sha256(aggregate_attestation.encode("utf-8")).hexdigest(),
    )
    scratch = tmp_path / "scratch"
    scratch.mkdir()
    read_fd, write_fd = os.pipe()
    try:
        argv, plan = _sandbox_command(
            [str(launcher), str(destination / "@playwright/test/cli.js")],
            (scratch,), readable_roots=(reporter, *roles.readable_roots),
            readable_bindings=(*roles.native_bindings, (dependencies, destination)),
            snapshot_binding_proofs=enlarged_proofs,
            playwright_snapshot_aggregate=aggregate, result_write_fd=write_fd,
            result_fd=198, observation_nonce="a" * 64,
        )
    finally:
        os.close(read_fd)
        os.close(write_fd)

    assert max(len(value.encode("utf-8")) for value in argv) < 131072
    assert sum(len(value.encode("utf-8")) + 1 for value in argv) < 131072
    frame = supervisor._descriptor_frame(
        plan.launch_payload, supervisor._DESCRIPTOR_PROTOCOL_MAX_LAUNCH_BYTES
    )
    assert len(frame) > 131072
    assert supervisor._read_descriptor_frame(
        io.BytesIO(frame), supervisor._DESCRIPTOR_PROTOCOL_MAX_LAUNCH_BYTES
    ) == plan.launch_payload


def test_root_authority_rejects_saved_pass_observation_for_current_skip(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A prior root PASS artifact cannot satisfy a current skipped result record."""
    skipped = b'{"tests":[{"status":"skipped"}]}'
    saved_pass = b'{"tests":[{"status":"passed"}]}'
    nonce = "a" * 64
    result = json.dumps({
        "version": 1, "state": "terminal", "returncode": 0,
        "timed_out": False, "observation_nonce": nonce,
        "observation_sha256": hashlib.sha256(skipped).hexdigest(),
        "observation_size": len(skipped),
    }).encode("ascii")
    monkeypatch.setattr(
        supervisor, "_read_root_artifact",
        lambda path, _maximum: result if path.name == "result.json" else saved_pass,
    )

    metadata = supervisor._load_root_observation_result(
        Path("authority/result.json"), nonce, 1024,
    )
    with pytest.raises(RuntimeError, match="does not match result"):
        supervisor._load_root_observation(
            Path("authority/observation.bin"), 1024,
            metadata.observation_digest, metadata.observation_size,
        )


@pytest.mark.parametrize("mutation", ["nonce", "digest", "size"])
def test_root_authority_observation_binding_mismatches_fail_closed(
    monkeypatch: pytest.MonkeyPatch, mutation: str,
) -> None:
    """The parent requires the fresh nonce and exact artifact identity."""
    observation = b'{"tests":[]}'
    nonce = "b" * 64
    result = {
        "version": 1, "state": "terminal", "returncode": 0,
        "timed_out": False, "observation_nonce": nonce,
        "observation_sha256": hashlib.sha256(observation).hexdigest(),
        "observation_size": len(observation),
    }
    if mutation == "nonce":
        result["observation_nonce"] = "c" * 64
    elif mutation == "digest":
        result["observation_sha256"] = "0" * 64
    else:
        result["observation_size"] = len(observation) + 1
    encoded = json.dumps(result).encode("ascii")
    monkeypatch.setattr(
        supervisor, "_read_root_artifact",
        lambda path, _maximum: encoded if path.name == "result.json" else observation,
    )

    if mutation == "nonce":
        with pytest.raises(RuntimeError, match="observation result is invalid"):
            supervisor._load_root_observation_result(
                Path("authority/result.json"), nonce, 1024,
            )
        return
    metadata = supervisor._load_root_observation_result(
        Path("authority/result.json"), nonce, 1024,
    )
    with pytest.raises(RuntimeError, match="does not match result"):
        supervisor._load_root_observation(
            Path("authority/observation.bin"), 1024,
            metadata.observation_digest, metadata.observation_size,
        )


def _descriptor_runtime_proof(
    copied: Path, protected: Path, *, destination: Path | None = None,
    native_mode: int = 0o644,
):
    """Create one proof through the real validated-descriptor adapter path."""
    from pdd.sync_core.runner import (  # pylint: disable=import-outside-toplevel
        VitestToolchainDescriptor,
        VitestToolchainMember,
        _vitest_immutable_binding_proofs,
        _vitest_members_identity,
    )

    digest = hashlib.sha256(protected.read_bytes()).hexdigest()
    members = tuple(sorted((
        VitestToolchainMember(
            "dependencies", PurePosixPath("."), "directory", 0o755
        ),
        VitestToolchainMember(
            "entrypoint", PurePosixPath("."), "file", 0o644, digest
        ),
        VitestToolchainMember(
            "launcher", PurePosixPath("."), "file", 0o644, digest
        ),
        VitestToolchainMember(
            "lockfile", PurePosixPath("."), "file", 0o644, digest
        ),
        VitestToolchainMember(
            "native_runtime", PurePosixPath("0"), "file", native_mode, digest
        ),
    ), key=lambda item: (item.role, item.relative_path.as_posix())))
    identity = hashlib.sha256(json.dumps({
        "members": _vitest_members_identity(members),
        "launch_policy": {
            "linux_wasm_trap_handler_disabled": sys.platform.startswith("linux"),
        },
    }, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    descriptor = VitestToolchainDescriptor(
        protected.parent / "vitest-toolchain.json",
        protected,
        protected,
        protected.parent,
        (protected,),
        protected,
        identity,
        "0" * 64,
        members,
    )
    proof = _vitest_immutable_binding_proofs((copied,), descriptor)[0]
    if destination is not None:
        proof = replace(proof, destination=destination)
    return proof


def _descriptor_runtime_alias_proofs(
    copied: tuple[Path, Path], protected: Path,
) -> tuple[ImmutableBindingProof, ImmutableBindingProof]:
    """Create two descriptor members naming one canonical native authority."""
    from pdd.sync_core.runner import (  # pylint: disable=import-outside-toplevel
        VitestToolchainDescriptor,
        VitestToolchainMember,
        _vitest_descriptor_attestation,
        _vitest_immutable_binding_proofs,
        _vitest_member_payload,
        _vitest_members_identity,
    )

    digest = hashlib.sha256(protected.read_bytes()).hexdigest()
    members = tuple(sorted((
        VitestToolchainMember("dependencies", PurePosixPath("."), "directory", 0o755),
        VitestToolchainMember("entrypoint", PurePosixPath("."), "file", 0o644, digest),
        VitestToolchainMember("launcher", PurePosixPath("."), "file", 0o644, digest),
        VitestToolchainMember("lockfile", PurePosixPath("."), "file", 0o644, digest),
        VitestToolchainMember("native_runtime", PurePosixPath("0"), "file", 0o644, digest),
        VitestToolchainMember("native_runtime", PurePosixPath("1"), "file", 0o644, digest),
    ), key=lambda item: (item.role, item.relative_path.as_posix())))
    _attestation, identity = _vitest_descriptor_attestation(
        tuple(_vitest_member_payload(member) for member in members),
        (protected, protected),
        linux_wasm_trap_handler_disabled=True,
    )
    descriptor = VitestToolchainDescriptor(
        protected.parent / "vitest-toolchain.json", protected, protected,
        protected.parent, (protected, protected), protected, identity,
        _vitest_members_identity(tuple(
            member for member in members if member.role == "dependencies"
        )), members,
    )
    return _vitest_immutable_binding_proofs(copied, descriptor)


def _proof_with_native_member_field(proof, field: str, value):
    """Return a proof whose canonical descriptor member has one altered field."""
    payload = json.loads(proof.descriptor_attestation)
    member = next(
        item for item in payload["members"]
        if item["role"] == "native_runtime" and item["path"] == "0"
    )
    member[field] = value
    return replace(
        proof,
        descriptor_attestation=json.dumps(
            payload, sort_keys=True, separators=(",", ":")
        ),
    )


def _mock_runtime_collision(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, *,
    candidate_uid: int = 1234, candidate_gid: int = 2345,
) -> tuple[Path, Path]:
    """Install one synthetic inferred runtime collision for proof tests."""
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: candidate_uid)
    monkeypatch.setattr(os, "getgid", lambda: candidate_gid)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    protected = tmp_path / "ld-linux-x86-64.so.2"
    protected.write_bytes(b"native-loader")
    copied = tmp_path / "copied-loader"
    copied.write_bytes(protected.read_bytes())
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: (protected,)
    )
    return protected, copied


def test_framework_observation_wrapper_opens_portable_fifo_path(
    tmp_path: Path,
) -> None:
    """Exercise the portable standard-framework handoff without Bubblewrap."""
    channel = tmp_path / "channel"
    channel.mkdir(mode=0o700)
    fifo = channel / "result.fifo"
    os.mkfifo(fifo, mode=0o600)
    read_fd = os.open(fifo, os.O_RDONLY | os.O_NONBLOCK)
    result_fd = 17
    candidate = [
        sys.executable,
        "-c",
        f"import os;os.write({result_fd},b'framework-result')",
    ]

    completed = subprocess.run(
        _framework_observation_command(candidate, result_fd, fifo),
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    try:
        assert completed.returncode == 0, completed.stderr
        assert fifo.exists()
        assert os.read(read_fd, 1024) == b"framework-result"
    finally:
        os.close(read_fd)


def test_runtime_closure_ignores_synthetic_argv_interpreter_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Identity-only argv prefixes must never become measured or mounted paths."""
    actual_executable = Path(sys.executable).resolve()
    supervisor.released_runtime_closure_paths.cache_clear()
    try:
        monkeypatch.setattr(
            "pdd.sync_core.runner.sys.executable", "/venv-a/bin/python"
        )
        closure = dict(supervisor.released_runtime_closure_paths())
        assert closure["interpreter/python"] == actual_executable
        assert closure["interpreter/python"].is_file()
    finally:
        supervisor.released_runtime_closure_paths.cache_clear()


def test_runtime_directories_collapse_nested_but_keep_disjoint_roots(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    stdlib = tmp_path / "python" / "lib"
    purelib = stdlib / "site-packages"
    platlib = tmp_path / "venv" / "site-packages"
    purelib.mkdir(parents=True)
    platlib.mkdir(parents=True)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.sysconfig.get_paths",
        lambda: {
            "stdlib": str(stdlib),
            "platstdlib": str(stdlib),
            "purelib": str(purelib),
            "platlib": str(platlib),
        },
    )

    assert _runtime_directories() == (
        ("python-runtime/stdlib", stdlib),
        ("python-runtime/platlib", platlib),
    )


@pytest.mark.parametrize("version", ("².12", "1234.12", "3.1234"))
def test_python_runtime_version_rejects_non_ascii_or_unbounded_fields(
    version: str,
) -> None:
    assert supervisor._python_version(version) is None


def test_runtime_roots_include_candidate_interpreter_native_stdlib(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A venv command retains the exact native stdlib selected by pyvenv.cfg."""
    workdir = tmp_path / "workdir"
    workdir.mkdir()
    native_bin = tmp_path / "native" / "bin"
    native_bin.mkdir(parents=True)
    native_python = native_bin / "python"
    native_python.write_bytes(b"native-python")
    native_python.chmod(0o755)
    native_stdlib = tmp_path / "native" / "lib" / "python3.12"
    native_stdlib.mkdir(parents=True)
    (native_stdlib / "linecache.py").write_text("cache = {}\n", encoding="utf-8")
    environment = tmp_path / "candidate-venv"
    candidate_bin = environment / "bin"
    candidate_bin.mkdir(parents=True)
    candidate_python = candidate_bin / "python"
    candidate_python.symlink_to(native_python)
    (environment / "pyvenv.cfg").write_text(
        f"home = {native_bin}\n"
        "include-system-site-packages = false\n"
        "version = 3.12.9\n"
        f"executable = {native_python}\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(supervisor, "_runtime_directories", lambda: ())
    monkeypatch.setattr(supervisor, "released_runtime_closure_paths", lambda: ())

    roots = supervisor._runtime_roots(
        [str(candidate_python), "-c", "pass"], workdir,
    )

    assert native_stdlib.resolve() in roots


@pytest.mark.parametrize("failure", ("invalid-version", "resolve-error"))
def test_candidate_runtime_metadata_failures_remain_supervised(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failure: str,
) -> None:
    """Candidate metadata/path errors retain the status-125 failure contract."""
    workdir = tmp_path / "workdir"
    workdir.mkdir()
    native_bin = tmp_path / "native" / "bin"
    native_bin.mkdir(parents=True)
    native_python = native_bin / "python"
    native_python.write_bytes(b"native-python")
    native_python.chmod(0o755)
    environment = tmp_path / "candidate-venv"
    candidate_bin = environment / "bin"
    candidate_bin.mkdir(parents=True)
    candidate_python = candidate_bin / "python"
    candidate_python.symlink_to(native_python)
    version = "².12" if failure == "invalid-version" else "3.12.9"
    (environment / "pyvenv.cfg").write_text(
        f"home = {native_bin}\nversion = {version}\n", encoding="utf-8",
    )
    native_stdlib = tmp_path / "native" / "lib" / "python3.12"
    if failure == "resolve-error":
        native_stdlib.mkdir(parents=True)
        original_resolve = Path.resolve

        def guarded_resolve(path, *args, **kwargs):
            if path == native_stdlib:
                raise OSError("candidate runtime resolution failed")
            return original_resolve(path, *args, **kwargs)

        monkeypatch.setattr(Path, "resolve", guarded_resolve)
    monkeypatch.setattr(supervisor, "_runtime_directories", lambda: ())
    monkeypatch.setattr(supervisor, "released_runtime_closure_paths", lambda: ())

    def fail_closed(command, *_args, **_kwargs):
        supervisor._runtime_roots(command, workdir)
        raise RuntimeError("protected candidate runtime unavailable")

    monkeypatch.setattr(supervisor, "_sandbox_command", fail_closed)
    result, surviving = run_supervised(
        [str(candidate_python), "-c", "pass"], cwd=workdir, timeout=1,
        env={}, writable_roots=(workdir,),
    )

    assert result.returncode == 125
    assert result.stderr == (
        "protected supervisor phase=construction: "
        "protected candidate runtime unavailable"
    )
    assert surviving is False


def test_native_runtime_roots_support_unversioned_lib64_interpreter(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A distinct unversioned Python retains one relocated native stdlib."""
    prefix = tmp_path / "native"
    native_bin = prefix / "bin"
    native_bin.mkdir(parents=True)
    native_python = native_bin / "python"
    native_python.write_bytes(b"native-python")
    native_python.chmod(0o755)
    native_stdlib = prefix / "lib64" / "python3.12"
    native_stdlib.mkdir(parents=True)
    (native_stdlib / "linecache.py").write_text("cache = {}\n", encoding="utf-8")
    unrelated = prefix / "share" / "python3.12"
    unrelated.mkdir(parents=True)
    monkeypatch.setattr(sys, "platlibdir", "lib64")

    roots = supervisor._native_python_runtime_roots(native_python)

    assert roots == (native_stdlib.resolve(),)
    assert unrelated.resolve() not in roots


def test_native_runtime_roots_reject_non_python_unversioned_executable(
    tmp_path: Path,
) -> None:
    """Adjacent Python libraries do not make an arbitrary command Python."""
    prefix = tmp_path / "native"
    native_bin = prefix / "bin"
    native_bin.mkdir(parents=True)
    native_node = native_bin / "node"
    native_node.write_bytes(b"native-node")
    native_node.chmod(0o755)
    native_stdlib = prefix / "lib" / "python3.12"
    native_stdlib.mkdir(parents=True)
    (native_stdlib / "linecache.py").write_text("cache = {}\n", encoding="utf-8")

    assert supervisor._native_python_runtime_roots(native_node) == ()


def test_native_runtime_roots_ignore_unrelated_busy_prefix_entries(
    tmp_path: Path,
) -> None:
    """Only matching Python roots count toward bounded fallback discovery."""
    prefix = tmp_path / "native"
    native_bin = prefix / "bin"
    native_bin.mkdir(parents=True)
    native_python = native_bin / "python"
    native_python.write_bytes(b"native-python")
    native_python.chmod(0o755)
    library = prefix / "lib"
    for index in range(65):
        (library / f"unrelated-{index}").mkdir(parents=True)
    native_stdlib = library / "python3.12"
    native_stdlib.mkdir()
    (native_stdlib / "linecache.py").write_text("cache = {}\n", encoding="utf-8")

    assert supervisor._native_python_runtime_roots(native_python) == (
        native_stdlib.resolve(),
    )


def test_native_runtime_roots_reject_ambiguous_library_roots(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Ambient platlibdir cannot choose between candidate lib and lib64."""
    prefix = tmp_path / "native"
    native_bin = prefix / "bin"
    native_bin.mkdir(parents=True)
    native_python = native_bin / "python"
    native_python.write_bytes(b"native-python")
    native_python.chmod(0o755)
    for library_name in ("lib", "lib64"):
        native_stdlib = prefix / library_name / "python3.12"
        native_stdlib.mkdir(parents=True)
        (native_stdlib / "linecache.py").write_text(
            "cache = {}\n", encoding="utf-8",
        )
    monkeypatch.setattr(sys, "platlibdir", "lib64")

    assert supervisor._native_python_runtime_roots(native_python) == ()


def test_linux_sandbox_uses_privileged_namespace_setup_then_drops_uid(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    argv, plan = _sandbox_command(["/bin/true"], (tmp_path,))
    assert plan.unit_name.startswith("pdd-validator-")
    assert argv[:3] == [str(plan.tools.sudo), "-n", str(plan.tools.systemd_run)]
    bwrap = plan.bwrap_argv
    assert {"--unshare-pid", "--unshare-net", "--unshare-cgroup"} <= set(bwrap)
    assert "--unshare-user" not in bwrap
    separator = bwrap.index("--")
    assert bwrap.index("--bind") < separator < bwrap.index("--reuid")
    assert bwrap[bwrap.index("--reuid") + 1] == "1234"
    assert bwrap[bwrap.index("--regid") + 1] == "2345"
    assert bwrap.index("--proc") < separator
    assert plan.launch_payload is not None
    assert bwrap[bwrap.index("--ro-bind") + 1] in plan.launch_payload["path_tokens"]


def test_linux_sandbox_uses_upstream_bwrap_inherited_descriptor_contract(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Ubuntu Bubblewrap receives no unsupported descriptor-preservation option."""
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: ()
    )

    _argv, plan = _sandbox_command(["/bin/true"], (tmp_path,))

    assert "--preserve-fds" not in plan.bwrap_argv
    separator = plan.bwrap_argv.index("--")
    candidate = plan.bwrap_argv[separator + 1:]
    assert supervisor._INNER_STATUS_SUPERVISOR_SOURCE in candidate
    assert candidate[candidate.index(supervisor._INNER_STATUS_SUPERVISOR_SOURCE) + 1] == "3"


def test_linux_sandbox_binds_inner_helper_python_runtime(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The Bubblewrap-invoked helper retains its exact native Python runtime."""
    helper_prefix = tmp_path.with_name(f"{tmp_path.name}-helper-runtime")
    helper_python = helper_prefix / "bin" / "python3.12"
    helper_python.parent.mkdir(parents=True)
    helper_python.write_bytes(b"helper-python")
    helper_python.chmod(0o755)
    helper_stdlib = helper_prefix / "lib" / "python3.12"
    helper_stdlib.mkdir(parents=True)
    (helper_stdlib / "linecache.py").write_text("cache = {}\n", encoding="utf-8")
    helper_loader = helper_prefix / "lib" / "ld-linux-x86-64.so.2"
    helper_loader.write_bytes(b"loader")

    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    metadata = helper_python.stat()
    helper_identity = supervisor._ExecutableIdentity(
        helper_python,
        (metadata.st_dev, metadata.st_ino, stat.S_IMODE(metadata.st_mode),
         0, metadata.st_size, metadata.st_mtime_ns),
        hashlib.sha256(helper_python.read_bytes()).hexdigest(),
    )
    monkeypatch.setattr(supervisor, "_trusted_helper_python", lambda: helper_identity)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(supervisor, "_runtime_roots", lambda *_args: ())
    monkeypatch.setattr(
        supervisor, "_linked_libraries",
        lambda path: (helper_loader,) if path == helper_python else (),
    )

    _argv, plan = _sandbox_command(["/bin/true"], (tmp_path,))
    bwrap = plan.bwrap_argv

    def bind_source(destination: Path) -> str:
        index = next(
            index for index, value in enumerate(bwrap[2:], 2)
            if value == str(destination) and bwrap[index - 2] == "--ro-bind"
        )
        assert plan.launch_payload is not None
        tokens = plan.launch_payload["path_tokens"]
        return str(plan.sources[tokens.index(bwrap[index - 1])])

    separator = bwrap.index("--")
    assert bwrap[separator + 1] == str(helper_python)
    assert bind_source(helper_python) == str(helper_python)
    assert bind_source(helper_loader) == str(helper_loader)
    assert bind_source(helper_stdlib) == str(helper_stdlib)


def test_linux_sandbox_maps_copied_runtime_to_manifest_destination(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    copied = tmp_path / "copied-native"
    copied.write_bytes(b"descriptor-bound")
    manifest_destination = Path("/opt/node/lib/libnode.so")

    _argv, plan = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_bindings=((copied, manifest_destination),),
    )

    bwrap = plan.bwrap_argv
    sources = [str(path) for path in plan.sources]
    destination_index = bwrap.index(str(manifest_destination))
    assert bwrap[destination_index - 2] == "--ro-bind"
    placeholder = bwrap[destination_index - 1]
    assert plan.launch_payload is not None
    tokens = plan.launch_payload["path_tokens"]
    assert sources[tokens.index(placeholder)] == str(copied.resolve())


def test_linux_sandbox_maps_bounded_scratch_to_writable_tmp(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    scratch = tmp_path / "scratch"
    scratch.mkdir()

    _argv, plan = _sandbox_command(
        ["/bin/true"],
        (scratch,),
        writable_bindings=((scratch, Path("/tmp")),),
    )

    bwrap = plan.bwrap_argv
    sources = [str(path) for path in plan.sources]
    destination_index = len(bwrap) - 1 - bwrap[::-1].index("/tmp")
    assert bwrap[destination_index - 2] == "--bind"
    assert destination_index < bwrap.index("--ro-bind")
    placeholder = bwrap[destination_index - 1]
    assert plan.launch_payload is not None
    writable_roots = plan.launch_payload["writable_roots"]
    writable_specs = plan.launch_payload["writable_specs"]
    token, root_index, relative = next(
        spec for spec in writable_specs if spec[0] == placeholder
    )
    assert token == placeholder
    assert writable_roots[root_index] == str(scratch.resolve())
    assert relative == "."
    assert str(scratch.resolve()) not in sources


def test_linux_sandbox_deduplicates_identical_read_only_bindings(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    native = tmp_path / "native.so"
    native.write_bytes(b"native")

    _argv, plan = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_roots=(native, native),
        readable_bindings=((native, native),),
    )

    bwrap = plan.bwrap_argv
    assert bwrap.count(str(native)) == 1


def test_linux_sandbox_rejects_declared_copied_loader_at_inferred_runtime_without_proof(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A distinct declared source cannot replace an inferred runtime source."""
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    host_loader = tmp_path / "ld-linux-x86-64.so.2"
    host_loader.write_bytes(b"native-loader")
    copied_loader = tmp_path / "copied-loader"
    copied_loader.write_bytes(host_loader.read_bytes())
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: (host_loader,)
    )

    with pytest.raises(RuntimeError, match="conflicting bindings"):
        _sandbox_command(
            ["/bin/true"],
            (tmp_path,),
            readable_bindings=((copied_loader, host_loader),),
        )


def test_linux_sandbox_mounts_nested_declared_toolchain_after_phase_root(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A broad phase bind must not hide its protected node_modules overlay."""
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    phase_root = tmp_path / "repository"
    phase_root.mkdir()
    dependency_source = tmp_path / "toolchain" / "node_modules"
    dependency_source.mkdir(parents=True)
    dependency_destination = phase_root / "node_modules"
    dependency_destination.mkdir()
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots",
        lambda *_args: (phase_root,),
    )

    _argv, plan = _sandbox_command(
        ["/bin/true"], (tmp_path,), cwd=phase_root,
        readable_bindings=((dependency_source, dependency_destination),),
    )

    bwrap = plan.bwrap_argv

    def mount_index(destination: Path) -> int:
        return next(
            index for index, value in enumerate(bwrap)
            if value == str(destination) and bwrap[index - 2] == "--ro-bind"
        )

    assert mount_index(phase_root) < mount_index(dependency_destination)


def test_linux_sandbox_allows_descriptor_proven_copied_loader_at_inferred_runtime(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """An explicit protected descriptor identity authorizes one copied loader."""
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    host_loader = tmp_path / "ld-linux-x86-64.so.2"
    host_loader.write_bytes(b"native-loader")
    copied_loader = tmp_path / "copied-loader"
    copied_loader.write_bytes(host_loader.read_bytes())
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: (host_loader,)
    )
    proof = _descriptor_runtime_proof(copied_loader, host_loader)

    assert json.loads(proof.descriptor_attestation)["adapter"] == "vitest"

    _argv, plan = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_bindings=((copied_loader, host_loader),),
        immutable_binding_proofs=(proof,),
    )

    bwrap = plan.bwrap_argv
    sources = [str(path) for path in plan.sources]
    destination_index = bwrap.index(str(host_loader))
    assert bwrap.count(str(host_loader)) == 1
    assert plan.launch_payload is not None
    assert sources[plan.launch_payload["path_tokens"].index(bwrap[destination_index - 1])] == str(
        copied_loader.resolve()
    )


def test_linux_sandbox_coalesces_descriptor_proven_loader_aliases(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Two copied aliases of one native loader retain one descriptor-proven mount."""
    from pdd.sync_core.runner import (  # pylint: disable=import-outside-toplevel
        VitestToolchainDescriptor,
        VitestToolchainMember,
        _vitest_descriptor_attestation,
        _vitest_immutable_binding_proofs,
        _vitest_member_payload,
        _vitest_members_identity,
    )

    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    host_loader = tmp_path / "ld-linux-x86-64.so.2"
    host_loader.write_bytes(b"native-loader")
    copied_loaders = (tmp_path / "copied-loader-a", tmp_path / "copied-loader-b")
    for copied in copied_loaders:
        copied.write_bytes(host_loader.read_bytes())
    digest = hashlib.sha256(host_loader.read_bytes()).hexdigest()
    members = tuple(sorted((
        VitestToolchainMember("dependencies", PurePosixPath("."), "directory", 0o755),
        VitestToolchainMember("entrypoint", PurePosixPath("."), "file", 0o644, digest),
        VitestToolchainMember("launcher", PurePosixPath("."), "file", 0o644, digest),
        VitestToolchainMember("lockfile", PurePosixPath("."), "file", 0o644, digest),
        VitestToolchainMember("native_runtime", PurePosixPath("0"), "file", 0o644, digest),
        VitestToolchainMember("native_runtime", PurePosixPath("1"), "file", 0o644, digest),
    ), key=lambda item: (item.role, item.relative_path.as_posix())))
    attestation, identity = _vitest_descriptor_attestation(
        tuple(_vitest_member_payload(member) for member in members),
        (host_loader, host_loader),
        linux_wasm_trap_handler_disabled=True,
    )
    descriptor = VitestToolchainDescriptor(
        host_loader.parent / "vitest-toolchain.json",
        host_loader,
        host_loader,
        host_loader.parent,
        (host_loader, host_loader),
        host_loader,
        identity,
        _vitest_members_identity(tuple(
            member for member in members if member.role == "dependencies"
        )),
        members,
    )
    proofs = _vitest_immutable_binding_proofs(copied_loaders, descriptor)
    assert all(proof.descriptor_attestation == attestation for proof in proofs)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: (host_loader,)
    )

    _argv, plan = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_bindings=tuple((copied, host_loader) for copied in copied_loaders),
        immutable_binding_proofs=proofs,
    )

    bwrap = plan.bwrap_argv
    sources = [str(path) for path in plan.sources]
    destination_index = bwrap.index(str(host_loader))
    assert bwrap.count(str(host_loader)) == 1
    assert plan.launch_payload is not None
    assert sources[plan.launch_payload["path_tokens"].index(bwrap[destination_index - 1])] == str(
        copied_loaders[0].resolve()
    )


@pytest.mark.parametrize(
    "mutation",
    [
        "attestation", "identity", "protected_source", "destination", "role",
        "path", "digest", "mode", "copied_contents", "unproved_binding",
    ],
)
def test_linux_sandbox_rejects_nonidentical_loader_alias_authority(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str,
) -> None:
    """Alias coalescing accepts only two proofs of one exact native authority."""
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    protected = tmp_path / "ld-linux-x86-64.so.2"
    protected.write_bytes(b"native-loader")
    copied = (tmp_path / "copy-a", tmp_path / "copy-b")
    for path in copied:
        path.write_bytes(protected.read_bytes())
    proofs = list(_descriptor_runtime_alias_proofs(copied, protected))
    bindings = [(copied[0], protected), (copied[1], protected)]
    if mutation == "attestation":
        proofs[1] = replace(proofs[1], descriptor_attestation="{}")
    elif mutation == "identity":
        proofs[1] = replace(proofs[1], descriptor_identity="a" * 64)
    elif mutation == "protected_source":
        other = tmp_path / "other-loader"
        other.write_bytes(protected.read_bytes())
        proofs[1] = replace(proofs[1], protected_source=other)
    elif mutation == "destination":
        proofs[1] = replace(proofs[1], destination=Path("/opt/other-loader"))
    elif mutation == "role":
        proofs[1] = replace(proofs[1], member_role="launcher")
    elif mutation == "path":
        proofs[1] = replace(proofs[1], member_path="2")
    elif mutation == "digest":
        proofs[1] = _proof_with_native_member_field(proofs[1], "digest", "a" * 64)
    elif mutation == "mode":
        proofs[1] = _proof_with_native_member_field(proofs[1], "mode", 0o600)
    elif mutation == "copied_contents":
        copied[1].write_bytes(b"different-copy")
    else:
        ordinary = tmp_path / "ordinary"
        ordinary.write_bytes(protected.read_bytes())
        bindings.append((ordinary, protected))
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: (protected,)
    )

    with pytest.raises(RuntimeError, match="immutable binding proof|conflicting bindings"):
        _sandbox_command(
            ["/bin/true"], (tmp_path,), readable_bindings=tuple(bindings),
            immutable_binding_proofs=tuple(proofs),
        )


@pytest.mark.parametrize("mutation", ["copied", "protected", "identity"])
def test_linux_sandbox_rejects_tampered_descriptor_proof(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str,
) -> None:
    """A copied loader must still match its descriptor identity at assembly."""
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    host_loader = tmp_path / "ld-linux-x86-64.so.2"
    host_loader.write_bytes(b"native-loader")
    copied_loader = tmp_path / "copied-loader"
    copied_loader.write_bytes(host_loader.read_bytes())
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: (host_loader,)
    )
    proof = _descriptor_runtime_proof(copied_loader, host_loader)
    if mutation == "copied":
        copied_loader.write_bytes(b"tampered-copy")
    elif mutation == "protected":
        host_loader.write_bytes(b"tampered-host")
    else:
        proof = replace(proof, descriptor_identity="a" * 64)

    with pytest.raises(RuntimeError, match="immutable binding proof|conflicting bindings"):
        _sandbox_command(
            ["/bin/true"],
            (tmp_path,),
            readable_bindings=((copied_loader, host_loader),),
            immutable_binding_proofs=(proof,),
        )


def test_linux_sandbox_helper_rejects_replacement_after_command_construction(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The exact root-helper protocol rejects a post-construction replacement."""
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    host_loader = tmp_path / "ld-linux-x86-64.so.2"
    host_loader.write_bytes(b"native-loader")
    copied_loader = tmp_path / "copied-loader"
    copied_loader.write_bytes(host_loader.read_bytes())
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: (host_loader,)
    )
    proof = _descriptor_runtime_proof(copied_loader, host_loader)

    _argv, plan = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_bindings=((copied_loader, host_loader),),
        immutable_binding_proofs=(proof,),
    )
    copied_loader.unlink()
    copied_loader.write_bytes(b"replaced-after-command-construction")
    namespace = {}
    exec(  # pylint: disable=exec-used
        "import hashlib,json,os,pathlib,stat\n"
        + supervisor._IMMUTABLE_STAGING_SOURCE,
        namespace,
    )
    target = tmp_path / "root-owned-snapshot"
    target.touch(mode=0o600)

    with pytest.raises(RuntimeError, match="immutable binding"):
        namespace["_stage_immutable_snapshot"](
            plan.immutable_binding_proofs[0], target, 1234, 2345
        )
    assert supervisor._IMMUTABLE_STAGING_SOURCE in plan.helper_source


@pytest.mark.parametrize(
    ("mode", "candidate_permission"),
    [
        (0o600, stat.S_IRUSR),
        (0o640, stat.S_IRUSR),
        (0o644, stat.S_IROTH),
        (0o700, stat.S_IXUSR),
        (0o750, stat.S_IXUSR),
        (0o755, stat.S_IXOTH),
    ],
)
def test_linux_sandbox_helper_stages_descriptor_mode_for_candidate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mode: int,
    candidate_permission: int,
) -> None:
    """The validated candidate owns and can use each staged descriptor mode."""
    candidate_uid = os.getuid()
    candidate_gid = os.getgid()
    protected, copied = _mock_runtime_collision(
        tmp_path, monkeypatch,
        candidate_uid=candidate_uid, candidate_gid=candidate_gid,
    )
    executable = bool(mode & (stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH))
    payload = b"#!/bin/sh\nexit 0\n" if executable else b"native-library"
    protected.write_bytes(payload)
    copied.write_bytes(payload)
    protected.chmod(mode)
    copied.chmod(mode)
    proof = _descriptor_runtime_proof(copied, protected, native_mode=mode)
    _argv, plan = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_bindings=((copied, protected),),
        immutable_binding_proofs=(proof,),
    )
    namespace = {}
    exec(  # pylint: disable=exec-used
        "import hashlib,json,os,pathlib,stat\n"
        + supervisor._IMMUTABLE_STAGING_SOURCE,
        namespace,
    )
    target = tmp_path / "root-owned-snapshot"
    target.touch(mode=0o600)
    monkeypatch.setenv("SUDO_UID", str(candidate_uid))
    monkeypatch.setenv("SUDO_GID", str(candidate_gid))
    monkeypatch.setattr(os, "geteuid", lambda: 0)
    monkeypatch.setattr(os, "getegid", lambda: 0)
    assert plan.launch_payload is not None
    validated_uid, validated_gid = namespace["_validated_candidate_identity"](
        plan.launch_payload["candidate_identity"], list(plan.bwrap_argv)
    )

    assert namespace["_stage_immutable_snapshot"](
        plan.immutable_binding_proofs[0], target, validated_uid, validated_gid
    ) == 0
    metadata = target.stat()
    snapshot_mode = stat.S_IMODE(metadata.st_mode)
    assert snapshot_mode == mode
    assert (metadata.st_uid, metadata.st_gid) == (candidate_uid, candidate_gid)
    assert snapshot_mode & candidate_permission
    assert target.read_bytes() == payload
    if executable:
        assert subprocess.run([target], check=False).returncode == 0
    bwrap = plan.bwrap_argv
    destination_index = bwrap.index(str(protected))
    assert bwrap[destination_index - 2] == "--ro-bind"
    assert "mode=0700,nosuid,nodev" in plan.helper_source
    assert "os.fchown" in plan.helper_source


@pytest.mark.parametrize(
    ("identity", "sudo_uid", "sudo_gid", "argv_mutation"),
    [
        ({"schema": "pdd-candidate-identity-v1", "uid": "1234", "gid": 2345},
         "1234", "2345", None),
        ({"schema": "pdd-candidate-identity-v1", "uid": 1234, "gid": True},
         "1234", "2345", None),
        ({"schema": "pdd-candidate-identity-v1", "uid": 1234, "gid": 2345},
         "9999", "2345", None),
        ({"schema": "pdd-candidate-identity-v1", "uid": 1234, "gid": 2345},
         "1234", "2345", "forged-drop"),
    ],
)
def test_linux_sandbox_helper_rejects_forged_candidate_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, identity: dict[str, object],
    sudo_uid: str, sudo_gid: str, argv_mutation: str | None,
) -> None:
    """Candidate ownership is bound to root invocation and the exact UID drop."""
    protected, copied = _mock_runtime_collision(tmp_path, monkeypatch)
    proof = _descriptor_runtime_proof(copied, protected)
    _command, plan = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_bindings=((copied, protected),),
        immutable_binding_proofs=(proof,),
    )
    bwrap = list(plan.bwrap_argv)
    if argv_mutation:
        bwrap[bwrap.index("--reuid") + 1] = "9999"
    namespace = {}
    exec(  # pylint: disable=exec-used
        "import hashlib,json,os,pathlib,stat\n"
        + supervisor._IMMUTABLE_STAGING_SOURCE,
        namespace,
    )
    monkeypatch.setenv("SUDO_UID", sudo_uid)
    monkeypatch.setenv("SUDO_GID", sudo_gid)
    monkeypatch.setattr(os, "geteuid", lambda: 0)
    monkeypatch.setattr(os, "getegid", lambda: 0)

    with pytest.raises(RuntimeError, match="immutable binding"):
        namespace["_validated_candidate_identity"](
            json.dumps(identity, sort_keys=True, separators=(",", ":")), bwrap
        )


def test_linux_sandbox_helper_rejects_mode_change_after_command_construction(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The helper revalidates the descriptor mode at the bind boundary."""
    protected, copied = _mock_runtime_collision(tmp_path, monkeypatch)
    proof = _descriptor_runtime_proof(copied, protected)
    _argv, plan = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_bindings=((copied, protected),),
        immutable_binding_proofs=(proof,),
    )
    copied.chmod(0o600)
    namespace = {}
    exec(  # pylint: disable=exec-used
        "import hashlib,json,os,pathlib,stat\n"
        + supervisor._IMMUTABLE_STAGING_SOURCE,
        namespace,
    )
    target = tmp_path / "root-owned-snapshot"
    target.touch(mode=0o600)

    with pytest.raises(RuntimeError, match="immutable binding"):
        namespace["_stage_immutable_snapshot"](
            plan.immutable_binding_proofs[0], target, 1234, 2345
        )


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("descriptor_identity", "a" * 64),
        ("member_role", "launcher"),
        ("member_path", "1"),
        ("collision_category", "playwright_inferred_runtime"),
    ],
)
def test_linux_sandbox_rejects_proof_authority_outside_exact_vitest_member(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, field: str, value: str,
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    host_loader = tmp_path / "ld-linux-x86-64.so.2"
    host_loader.write_bytes(b"native-loader")
    copied_loader = tmp_path / "copied-loader"
    copied_loader.write_bytes(host_loader.read_bytes())
    proof = replace(
        _descriptor_runtime_proof(copied_loader, host_loader), **{field: value}
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: (host_loader,)
    )

    with pytest.raises(RuntimeError, match="immutable binding proof"):
        _sandbox_command(
            ["/bin/true"],
            (tmp_path,),
            readable_bindings=((copied_loader, host_loader),),
            immutable_binding_proofs=(proof,),
        )


def test_linux_sandbox_rejects_symlink_spelled_proof_destination(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    host_loader = tmp_path / "ld-linux-x86-64.so.2"
    host_loader.write_bytes(b"native-loader")
    alias = tmp_path / "loader-alias"
    alias.symlink_to(host_loader)
    copied_loader = tmp_path / "copied-loader"
    copied_loader.write_bytes(host_loader.read_bytes())
    scratch = tmp_path / "scratch"
    scratch.mkdir()
    proof = _descriptor_runtime_proof(
        copied_loader, host_loader, destination=alias
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: (alias,)
    )

    with pytest.raises(RuntimeError, match="immutable binding proof|conflicting"):
        _sandbox_command(
            ["/bin/true"],
            (scratch,),
            readable_bindings=((copied_loader, alias),),
            immutable_binding_proofs=(proof,),
        )


@pytest.mark.parametrize(
    "mutation",
    [
        "copied_path_type",
        "missing_protected_path",
        "descriptor_identity_type",
        "descriptor_identity_subclass",
        "attestation_type",
        "digest_type",
        "digest_spelling",
        "mode_type",
        "mode_bool",
        "mode_range",
        "member_absent",
        "category_subclass",
    ],
)
def test_linux_sandbox_normalizes_malformed_proof_rejection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str,
) -> None:
    protected, copied = _mock_runtime_collision(tmp_path, monkeypatch)
    proof = _descriptor_runtime_proof(copied, protected)

    class Text(str):
        """Authority-confusing string subclass."""

    if mutation == "copied_path_type":
        proof = replace(proof, copied_source=str(copied))
    elif mutation == "missing_protected_path":
        proof = replace(proof, protected_source=tmp_path / "missing")
    elif mutation == "descriptor_identity_type":
        proof = replace(proof, descriptor_identity=7)
    elif mutation == "descriptor_identity_subclass":
        proof = replace(proof, descriptor_identity=Text(proof.descriptor_identity))
    elif mutation == "attestation_type":
        proof = replace(proof, descriptor_attestation=b"{}")
    elif mutation == "digest_type":
        proof = _proof_with_native_member_field(proof, "digest", 7)
    elif mutation == "digest_spelling":
        proof = _proof_with_native_member_field(proof, "digest", "not-a-digest")
    elif mutation == "mode_type":
        proof = _proof_with_native_member_field(proof, "mode", "420")
    elif mutation == "mode_bool":
        proof = _proof_with_native_member_field(proof, "mode", True)
    elif mutation == "mode_range":
        proof = _proof_with_native_member_field(proof, "mode", 0o1000)
    elif mutation == "member_absent":
        payload = json.loads(proof.descriptor_attestation)
        payload["members"] = [
            item for item in payload["members"]
            if item["role"] != "native_runtime"
        ]
        proof = replace(
            proof,
            descriptor_attestation=json.dumps(
                payload, sort_keys=True, separators=(",", ":")
            ),
        )
    else:
        proof = replace(
            proof, collision_category=Text("vitest_inferred_runtime")
        )

    if mutation in {"digest_type", "digest_spelling", "mode_type", "mode_bool", "mode_range"}:
        field = "digest" if mutation.startswith("digest") else "mode"
        member = next(
            item for item in json.loads(proof.descriptor_attestation)["members"]
            if item["role"] == "native_runtime" and item["path"] == "0"
        )
        assert member[field] == {
            "digest_type": 7,
            "digest_spelling": "not-a-digest",
            "mode_type": "420",
            "mode_bool": True,
            "mode_range": 0o1000,
        }[mutation]

    with pytest.raises(RuntimeError, match="immutable binding proof"):
        _sandbox_command(
            ["/bin/true"],
            (tmp_path,),
            readable_bindings=((copied, protected),),
            immutable_binding_proofs=(proof,),
        )


def test_linux_sandbox_rejects_unused_immutable_binding_proof(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    protected, copied = _mock_runtime_collision(tmp_path, monkeypatch)
    proof = _descriptor_runtime_proof(copied, protected)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: ()
    )

    with pytest.raises(RuntimeError, match="unused immutable binding proof"):
        _sandbox_command(
            ["/bin/true"],
            (tmp_path,),
            readable_bindings=((copied, protected),),
            immutable_binding_proofs=(proof,),
        )


def test_linux_sandbox_rejects_duplicate_or_ambiguous_binding_proofs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    protected, copied = _mock_runtime_collision(tmp_path, monkeypatch)
    proof = _descriptor_runtime_proof(copied, protected)
    ambiguous = replace(proof, member_path="1")

    for proofs in ((proof, proof), (proof, ambiguous)):
        with pytest.raises(RuntimeError, match="duplicate|ambiguous"):
            _sandbox_command(
                ["/bin/true"],
                (tmp_path,),
                readable_bindings=((copied, protected),),
                immutable_binding_proofs=proofs,
            )


def test_linux_sandbox_rejects_multiply_consumed_binding_proof(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    protected, copied = _mock_runtime_collision(tmp_path, monkeypatch)
    proof = _descriptor_runtime_proof(copied, protected)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots",
        lambda *_args: (protected, protected),
    )

    with pytest.raises(RuntimeError, match="multiply consumed"):
        _sandbox_command(
            ["/bin/true"],
            (tmp_path,),
            readable_bindings=((copied, protected),),
            immutable_binding_proofs=(proof,),
        )


def test_linux_sandbox_rejects_proof_for_declared_binding_collision(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    protected, copied = _mock_runtime_collision(tmp_path, monkeypatch)
    proof = _descriptor_runtime_proof(copied, protected)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._runtime_roots", lambda *_args: ()
    )

    with pytest.raises(RuntimeError, match="conflicting bindings"):
        _sandbox_command(
            ["/bin/true"],
            (tmp_path,),
            readable_bindings=((copied, protected), (protected, protected)),
            immutable_binding_proofs=(proof,),
        )


def test_linux_sandbox_rejects_conflicting_bindings(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    first = tmp_path / "first.so"
    second = tmp_path / "second.so"
    first.write_bytes(b"first")
    second.write_bytes(b"second")

    with pytest.raises(RuntimeError, match="conflicting bindings"):
        _sandbox_command(
            ["/bin/true"],
            (tmp_path,),
            readable_bindings=((first, Path("/opt/native.so")),
                               (second, Path("/opt/native.so"))),
        )


def test_linux_sandbox_fails_closed_for_root_caller(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 0)
    _mock_linux_tools(tmp_path, monkeypatch)

    result, surviving = run_supervised(
        ["/bin/true"], cwd=tmp_path, timeout=1, env={},
        writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert "non-root caller" in result.stderr
    assert surviving is False


def test_linux_sandbox_uses_portable_framework_observation_fifo(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )

    channel = tmp_path / "channel"
    channel.mkdir(mode=0o700)
    scratch = tmp_path / "scratch"
    scratch.mkdir(mode=0o700)
    fifo = channel / "checker.fifo"
    os.mkfifo(fifo)
    _argv, plan = _sandbox_command(
        ["/bin/true"], (scratch,), result_fifo=fifo, result_fd=198
    )

    assert plan.unit_name.startswith("pdd-validator-")
    assert _argv[:3] == [str(plan.tools.sudo), "-n", str(plan.tools.systemd_run)]
    assert "-C" not in _argv[:6]
    bwrap = list(plan.bwrap_argv)
    assert "--preserve-fds" not in bwrap
    observation_path = "/run/pdd-framework-observation"
    observation_index = bwrap.index(observation_path)
    assert bwrap[observation_index - 2] == "--bind"
    observation_token = bwrap[observation_index - 1]
    assert plan.launch_payload is not None
    tokens = plan.launch_payload["path_tokens"]
    sources = [str(path) for path in plan.sources]
    assert sources[tokens.index(observation_token)] == str(fifo.resolve())
    assert plan.launch_payload["fifo_indices"] == [tokens.index(observation_token)]
    assert "stat.S_ISFIFO(metadata.st_mode)" in plan.helper_source
    assert "os.mkfifo(target,mode=0o600)" in plan.helper_source
    assert str(channel) not in bwrap
    separator = bwrap.index("--")
    candidate_argv = bwrap[separator + 1:]
    assert str(fifo) not in candidate_argv
    wrapper = next(
        value for value in candidate_argv
        if "os.dup2(source,target)" in value
    )
    assert "os.dup2(source,target)" in wrapper
    assert "os.open(path" in wrapper
    assert "result_fifo" not in plan.helper_source


def test_linux_sandbox_does_not_authorize_declared_fifo_staging(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Only the fixed framework observation mount may stage a FIFO target."""
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    scratch = tmp_path / "scratch"
    scratch.mkdir()
    candidate_fifo = tmp_path / "candidate.fifo"
    os.mkfifo(candidate_fifo)

    _argv, plan = _sandbox_command(
        ["/bin/true"], (scratch,),
        readable_bindings=((candidate_fifo, Path("/run/candidate.fifo")),),
    )

    assert plan.launch_payload is not None
    assert plan.launch_payload["fifo_indices"] == []


def _mock_scope_run(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, helper: str,
    *, stop_scope=None,
) -> list[str]:
    """Install one deterministic transient-scope process for state-machine tests."""
    cgroup = tmp_path / "cgroup"
    cgroup.mkdir(exist_ok=True)
    (cgroup / "memory.events").write_text("oom 0\noom_kill 0\n", encoding="ascii")
    (cgroup / "pids.events").write_text("max 0\n", encoding="ascii")
    cleanup: list[str] = []

    def sandbox(_command, _writable_roots, **kwargs):
        control = str(kwargs["control_directory"])
        plan = SimpleNamespace(
            unit_name="pdd-validator-00000000000000000000000000000000.scope",
            tools=SimpleNamespace(),
            launch_payload={
                "schema": "pdd-sandbox-launch-v1", "control": control,
            },
        )
        return [sys.executable, "-c", _launch_aware_mock_helper(helper)], plan

    monkeypatch.setattr(supervisor, "_sandbox_command", sandbox)
    monkeypatch.setattr(supervisor, "_prepare_staging", lambda _plan: None)
    monkeypatch.setattr(
        supervisor, "_probe_scope",
        lambda _plan, _limits: (cgroup, {"oom": 0, "oom_kill": 0}, {"max": 0}),
    )
    monkeypatch.setattr(
        supervisor, "_stop_scope",
        stop_scope or (lambda *_args: cleanup.append("scope")),
    )
    monkeypatch.setattr(
        supervisor, "_cleanup_staging", lambda _plan: cleanup.append("mounts")
    )
    monkeypatch.setattr(
        supervisor, "_scope_properties", lambda *_args: {"Result": "success"}
    )
    return cleanup


def _launch_aware_mock_helper(helper: str) -> str:
    """Require launch-frame/EOF ordering before running a file-control fixture."""
    return f"""import json,sys
stream=sys.stdin.buffer
header=stream.read(4)
if len(header)!=4: raise RuntimeError('mock launch header is partial')
size=int.from_bytes(header,'big')
if not 0<size<={supervisor._DESCRIPTOR_PROTOCOL_MAX_LAUNCH_BYTES}: raise RuntimeError('mock launch size is invalid')
encoded=stream.read(size)
if len(encoded)!=size: raise RuntimeError('mock launch payload is partial')
launch=json.loads(encoded)
if type(launch) is not dict or set(launch)!={{'schema','control'}} or launch.get('schema')!='pdd-sandbox-launch-v1' or type(launch.get('control')) is not str: raise RuntimeError('mock launch payload is invalid')
if json.dumps(launch,sort_keys=True,separators=(',',':')).encode()!=encoded: raise RuntimeError('mock launch payload is not canonical')
if stream.read(1)!=b'': raise RuntimeError('mock launch payload has trailing data')
sys.argv=[sys.argv[0],launch['control']]
exec({helper!r})
"""


def _terminal_helper(
    returncode: int, timed_out: bool, *, write_result: bool = True,
    result_record: dict[str, object] | None = None, output: str = "",
    helper_exit: int | None = None,
) -> str:
    record = {
        "version": 1, "state": "terminal",
        "returncode": returncode, "timed_out": timed_out,
    }
    result = result_record if result_record is not None else record
    result_source = (
        f"(control/'result.json').write_text({json.dumps(json.dumps(result))})"
        if write_result else ""
    )
    encoded_exit = (
        helper_exit if helper_exit is not None
        else returncode if returncode >= 0 else 128 - returncode
    )
    return f"""import pathlib,time
control=pathlib.Path(__import__('sys').argv[1])
(control/'ready').write_text('ready')
while not (control/'start').exists(): time.sleep(.001)
print({output!r},flush=True)
(control/'candidate.json').write_text({json.dumps(json.dumps(record))})
{result_source}
while not (control/'finish').exists(): time.sleep(.001)
raise SystemExit({encoded_exit})
"""


def test_launch_descriptor_write_failure_stops_scope_and_cleans_staging(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A failed initial handoff remains inside the protected cleanup lifecycle."""
    cleanup = _mock_scope_run(
        tmp_path, monkeypatch, "import time; time.sleep(30)"
    )
    monkeypatch.setattr(
        supervisor, "_write_descriptor_frame_fd",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            RuntimeError("launch write failed")
        ),
    )

    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=1,
        env={}, writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert surviving is False
    assert "phase=launch-handoff: launch write failed" in result.stderr
    assert cleanup == ["scope", "mounts"]


def test_launch_descriptor_and_eof_precede_non_descriptor_ready(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The file-control lifecycle starts only after one canonical launch and EOF."""
    cleanup = _mock_scope_run(
        tmp_path, monkeypatch, _terminal_helper(0, False, output="launch-ok")
    )

    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=1,
        env={}, writable_roots=(tmp_path,),
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "launch-ok"
    assert surviving is False
    assert cleanup == ["scope", "mounts"]


@pytest.mark.parametrize("case", ("partial", "oversized", "trailing", "duplicate"))
def test_invalid_launch_descriptor_stops_scope_and_cleans_staging(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, case: str,
) -> None:
    """Malformed initial frames never reach ready and retain exact cleanup."""
    cleanup = _mock_scope_run(
        tmp_path, monkeypatch, _terminal_helper(0, False)
    )

    def malformed_write(descriptor, payload, maximum, _deadline):
        valid = supervisor._descriptor_frame(payload, maximum)
        if case == "partial":
            data = b"\x00\x00\x00\x08{}"
        elif case == "oversized":
            data = (maximum + 1).to_bytes(4, "big")
        elif case == "trailing":
            data = valid + b"x"
        else:
            data = valid + valid
        os.write(descriptor, data)

    monkeypatch.setattr(
        supervisor, "_write_descriptor_frame_fd", malformed_write
    )
    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=1,
        env={}, writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert surviving is False
    assert "exited before verification" in result.stderr
    assert cleanup == ["scope", "mounts"]


def test_authority_directory_replacement_is_detected_before_relay(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A same-UID replacement attempt leaves no trusted result to relay."""
    monkeypatch.setattr(supervisor, "_TRUSTED_POSTPROCESS_SECONDS", .05)
    helper = """import json,pathlib,sys,time
control=pathlib.Path(sys.argv[1])
(control/'ready').write_text('ready')
while not (control/'start').exists(): time.sleep(.001)
record={'version':1,'state':'terminal','returncode':0,'timed_out':False}
(control/'candidate.json').write_text(json.dumps(record))
authority=control/'authority'; authority.mkdir()
authority.rename(control/'replayed-authority'); authority.mkdir()
while not (control/'finish').exists(): time.sleep(.001)
"""
    _mock_scope_run(tmp_path, monkeypatch, helper)
    read_fd, write_fd = os.pipe()
    try:
        result, surviving = run_supervised(
            [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
            env=dict(os.environ), writable_roots=(tmp_path,),
            result_write_fd=write_fd,
        )
    finally:
        os.close(read_fd)
        os.close(write_fd)

    assert result.returncode == 125
    assert "trusted postprocessing" in result.stderr
    assert surviving is False


def test_scope_setup_deadline_is_not_candidate_timeout(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(supervisor, "_TRUSTED_SETUP_SECONDS", .03)
    cleanup = _mock_scope_run(tmp_path, monkeypatch, "import time;time.sleep(30)")

    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.03,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert result.termination.kind is supervisor.TerminationKind.SANDBOX_ERROR
    assert "phase=scope-setup" in result.stderr
    assert cleanup == ["scope", "mounts"]
    assert surviving is False


def test_slow_scope_setup_does_not_consume_tiny_candidate_timeout(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    helper = _terminal_helper(0, False).replace(
        "(control/'ready').write_text('ready')",
        "time.sleep(.15);(control/'ready').write_text('ready')",
    )
    cleanup = _mock_scope_run(tmp_path, monkeypatch, helper)

    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.03,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 0, result.stderr
    assert cleanup == ["scope", "mounts"]
    assert surviving is False


@pytest.mark.parametrize("returncode", [0, 1])
def test_normal_candidate_status_is_preserved_from_protected_record(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, returncode: int,
) -> None:
    cleanup = _mock_scope_run(
        tmp_path, monkeypatch, _terminal_helper(returncode, False)
    )

    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == returncode, result.stderr
    assert cleanup == ["scope", "mounts"]
    assert surviving is False


def test_helper_pidfd_timeout_record_requires_exact_cleanup(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    cleanup = _mock_scope_run(tmp_path, monkeypatch, _terminal_helper(124, True))

    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 124, result.stderr
    assert "timeout phase=candidate-execution" in result.stderr
    assert "scope produced no validated result" not in result.stderr
    assert cleanup == ["scope", "mounts"]
    assert surviving is False


def test_helper_exit_must_match_validated_timeout_record(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    _mock_scope_run(
        tmp_path, monkeypatch,
        _terminal_helper(124, True, helper_exit=125),
    )

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert "helper exit" in result.stderr


def test_signaled_candidate_helper_exit_encoding_is_preserved(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    _mock_scope_run(tmp_path, monkeypatch, _terminal_helper(-signal.SIGTERM, False))

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == -signal.SIGTERM, result.stderr


def test_helper_timeout_with_cleanup_failure_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fail_cleanup(*_args):
        raise RuntimeError("scope remained loaded")

    _mock_scope_run(
        tmp_path, monkeypatch, _terminal_helper(124, True), stop_scope=fail_cleanup
    )

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.03,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert result.termination.kind is supervisor.TerminationKind.SANDBOX_ERROR
    assert "scope-cleanup" in result.stderr


def test_helper_stall_after_candidate_exit_is_not_timeout(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    helper = """import pathlib,sys,time
control=pathlib.Path(sys.argv[1]);(control/'ready').write_text('ready')
while not (control/'start').exists(): time.sleep(.001)
time.sleep(30)
"""
    _mock_scope_run(tmp_path, monkeypatch, helper)
    monkeypatch.setattr(supervisor, "_TRUSTED_POSTPROCESS_SECONDS", .03)

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert "protected candidate record" in result.stderr


@pytest.mark.parametrize("failure", ["pidfd_open", "poll", "waitpid"])
def test_helper_pidfd_failure_without_terminal_record_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failure: str,
) -> None:
    helper = f"""import pathlib,sys,time
control=pathlib.Path(sys.argv[1]);(control/'ready').write_text('ready')
while not (control/'start').exists(): time.sleep(.001)
raise RuntimeError({failure!r})
"""
    _mock_scope_run(tmp_path, monkeypatch, helper)

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert "timeout phase=candidate-execution" not in result.stderr


def test_ordinary_candidate_exit_124_is_reserved_and_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    _mock_scope_run(tmp_path, monkeypatch, _terminal_helper(124, False))

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert "reserved exit status 124" in result.stderr


@pytest.mark.parametrize(
    "record",
    [
        {"version": 1, "state": "terminal", "returncode": 124},
        {"version": True, "state": "terminal", "returncode": 0, "timed_out": False},
        {"version": 1.0, "state": "terminal", "returncode": 0, "timed_out": False},
        {"version": 1, "state": "terminal", "returncode": 124, "timed_out": "yes"},
        {"version": 1, "state": "running", "returncode": 124, "timed_out": True},
        {"version": 1, "state": "terminal", "returncode": 0, "timed_out": True},
    ],
)
def test_malformed_candidate_terminal_record_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, record: dict[str, object],
) -> None:
    helper = _terminal_helper(0, False).replace(
        json.dumps(json.dumps({
            "version": 1, "state": "terminal", "returncode": 0,
            "timed_out": False,
        })),
        json.dumps(json.dumps(record)),
        1,
    )
    _mock_scope_run(tmp_path, monkeypatch, helper)

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125


def test_inconsistent_candidate_and_result_records_fail_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    inconsistent = {
        "version": 1, "state": "terminal", "returncode": 124, "timed_out": True,
    }
    _mock_scope_run(
        tmp_path, monkeypatch,
        _terminal_helper(0, False, result_record=inconsistent),
    )

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert "changed during handoff" in result.stderr


def test_helper_timeout_with_quota_postprocessing_failure_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    _mock_scope_run(
        tmp_path, monkeypatch, _terminal_helper(124, True, write_result=False)
    )
    monkeypatch.setattr(supervisor, "_TRUSTED_POSTPROCESS_SECONDS", .03)

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert "trusted postprocessing did not finish" in result.stderr


def test_helper_timeout_with_output_violation_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    _mock_scope_run(
        tmp_path, monkeypatch, _terminal_helper(124, True, output="x" * 4096)
    )

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
        limits=SupervisorLimits(max_output_bytes=1024),
    )

    assert result.returncode == 125


def test_helper_timeout_with_surviving_process_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    _mock_scope_run(tmp_path, monkeypatch, _terminal_helper(124, True))
    monkeypatch.setattr(supervisor, "_supervised_descendants", lambda _token: {999})
    monkeypatch.setattr(supervisor, "_process_identity", lambda _pid: "identity")
    monkeypatch.setattr(supervisor, "_live_processes", lambda _tracked: {999})
    monkeypatch.setattr(os, "kill", lambda *_args: None)

    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert surviving is True


def test_helper_timeout_with_unreadable_post_run_cgroup_events_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    _mock_scope_run(tmp_path, monkeypatch, _terminal_helper(124, True))
    monkeypatch.setattr(
        supervisor, "_cgroup_events",
        lambda *_args: (_ for _ in ()).throw(RuntimeError("events unreadable")),
    )

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert "events unreadable" in result.stderr


def test_helper_failure_without_result_preserves_original_diagnostic(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    helper = _terminal_helper(
        125, False, write_result=False, output="helper staging failed"
    ).replace(
        "while not (control/'finish').exists(): time.sleep(.001)", ""
    )
    _mock_scope_run(tmp_path, monkeypatch, helper)
    reads = 0

    def unreadable_events(*_args):
        nonlocal reads
        reads += 1
        raise RuntimeError("memory.events unavailable")

    monkeypatch.setattr(supervisor, "_cgroup_events", unreadable_events)

    result, _surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 125
    assert "helper staging failed" in result.stdout
    assert "memory.events unavailable" not in result.stderr
    assert reads == 0


def test_parent_timeout_protocol_never_observes_candidate_pid() -> None:
    source = inspect.getsource(run_supervised)

    assert "candidate-start" not in source
    assert "_candidate_proof" not in source
    assert "_process_descendants" not in source
    assert "_process_cgroup" not in source
    assert "kill(pid, 0)" not in source


def test_sandbox_directory_bind_provides_parent_for_nested_file(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    nested = tmp_path / "candidate-venv" / "bin"
    nested.mkdir(parents=True)
    interpreter = nested / "python"
    interpreter.write_text("python", encoding="utf-8")
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )

    _argv, plan = _sandbox_command([str(interpreter)], (tmp_path,), cwd=tmp_path)
    bwrap = plan.bwrap_argv
    directory_targets = {
        bwrap[index + 1] for index, value in enumerate(bwrap[:-1])
        if value == "--dir"
    }
    assert str(nested) not in directory_targets


def test_sandbox_binds_resolved_runtime_sources_at_original_destinations(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The namespace must retain the executable and loader lookup spellings."""
    runtime = tmp_path / "runtime"
    executable_source = runtime / "python-real"
    executable_source.parent.mkdir()
    executable_source.write_text("python", encoding="utf-8")
    executable_destination = tmp_path / "toolcache" / "bin" / "python"
    executable_destination.parent.mkdir(parents=True)
    executable_destination.symlink_to(executable_source)
    loader_source = runtime / "libc-real.so"
    loader_source.write_bytes(b"library")
    loader_destination = tmp_path / "loader" / "libc.so.6"
    loader_destination.parent.mkdir()
    loader_destination.symlink_to(loader_source)
    candidate = tmp_path / "candidate" / "bin" / "python"
    candidate.parent.mkdir(parents=True)
    candidate.write_text("python", encoding="utf-8")
    workdir = tmp_path / "work"
    workdir.mkdir()

    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._SUPERVISOR_EXECUTABLE",
        executable_destination,
    )
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr("pdd.sync_core.supervisor._runtime_directories", tuple)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths",
        lambda: (
            ("native/loader/libc.so.6", loader_destination),
            ("native/runtime/libc-real.so", loader_source),
        ),
    )

    _argv, plan = _sandbox_command(
        [str(candidate), "-c", "pass"], (workdir,), cwd=workdir
    )
    bwrap = plan.bwrap_argv
    sources = [str(path) for path in plan.sources]

    def bind_source(destination: Path) -> str:
        index = bwrap.index(str(destination))
        assert bwrap[index - 2] == "--ro-bind"
        placeholder = bwrap[index - 1]
        assert plan.launch_payload is not None
        tokens = plan.launch_payload["path_tokens"]
        return sources[tokens.index(placeholder)]

    assert str(executable_destination.parent) in {
        bwrap[index + 1] for index, value in enumerate(bwrap[:-1])
        if value == "--dir"
    }
    assert bind_source(executable_destination) == str(executable_source)
    assert bind_source(loader_destination) == str(loader_source)


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires Linux kernel namespace containment",
)
def test_sandboxed_python_minimal_smoke(tmp_path: Path) -> None:
    """A protected namespace can start the configured interpreter."""
    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"],
        cwd=tmp_path,
        timeout=10,
        env=dict(os.environ),
        writable_roots=(tmp_path,),
    )

    assert result.returncode == 0, result.stderr
    assert surviving is False


def test_protected_runner_declares_finite_resource_limits() -> None:
    limits = SupervisorLimits()
    assert 0 < limits.max_output_bytes <= 16 * 1024 * 1024
    assert 0 < limits.max_writable_bytes <= 1024 * 1024 * 1024
    assert 0 < limits.max_memory_bytes <= 4 * 1024 * 1024 * 1024
    assert 0 < limits.max_virtual_memory_bytes <= 2 * 1024 * 1024 * 1024
    assert 0 < limits.max_cpu_seconds <= 600
    assert 0 < limits.max_processes <= 256


@pytest.mark.parametrize("field", tuple(SupervisorLimits.__dataclass_fields__))
def test_security_limits_reject_boolean_numeric_values(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, field: str,
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    _mock_linux_tools(tmp_path, monkeypatch)
    values = vars(SupervisorLimits()) | {field: True}

    with pytest.raises(RuntimeError, match="invalid protected supervisor limits"):
        _sandbox_command(
            [sys.executable, "-c", "pass"], (tmp_path,),
            limits=SupervisorLimits(**values),
        )


def test_supervisor_separates_physical_and_virtual_memory_limits() -> None:
    """Keep physical memory bounded when one trusted tool needs more address space."""
    limits = SupervisorLimits(
        max_memory_bytes=2 * 1024 * 1024 * 1024,
        max_virtual_memory_bytes=64 * 1024 * 1024 * 1024,
    )

    command = _limited_command(["/bin/true"], limits)

    assert str(limits.max_virtual_memory_bytes) in command
    assert str(limits.max_memory_bytes) not in command[1:7]
    assert "RLIMIT_NPROC" not in command[2]


def test_linux_sandbox_binds_probe_identity_to_systemd_scope_execution(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Run one valid transient scope with exact trusted executable identities."""
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    tools = _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )

    argv, plan = _sandbox_command([sys.executable, "-c", "pass"], (tmp_path,))

    assert argv[:3] == [tools["sudo"], "-n", tools["systemd-run"]]
    separator = argv.index("--")
    assert argv[separator + 1:separator + 7] == [
        tools["unshare"], "--mount", "--propagation", "private", "--wd", "/",
    ]
    assert "--scope" in argv
    assert "--wait" not in argv
    assert "--collect" not in argv
    assert f"--unit={plan.unit_name}" in argv
    assert "--property=Delegate=yes" in argv
    assert "--property=MemoryMax=infinity" in argv
    assert "--property=MemorySwapMax=infinity" in argv
    assert "--property=TasksMax=infinity" in argv
    assert "--property=OOMPolicy=continue" in argv
    assert "--property=KillMode=control-group" in argv
    assert plan.bwrap_argv[0] == tools["bwrap"]


def test_linux_sandbox_stages_candidate_in_limited_leaf_before_exec(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The privileged helper must move the blocked child before untrusted exec."""
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_linux_tools(tmp_path, monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )

    argv, plan = _sandbox_command(
        [sys.executable, "-c", "pass"], (tmp_path,), candidate_timeout=17
    )
    helper = plan.helper_source

    compile(helper, "<privileged-scope-helper>", "exec")
    assert "monitor_cgroup=scope_cgroup/'monitor'" in helper
    assert "candidate_cgroup=scope_cgroup/'candidate'" in helper
    assert "monitor_cgroup.mkdir(mode=0o755)" in helper
    assert "candidate_cgroup.mkdir(mode=0o755)" in helper
    assert "monitor_cgroup.chmod(0o755)" in helper
    assert "candidate_cgroup.chmod(0o755)" in helper
    assert "(monitor_cgroup/'cgroup.procs').write_text(str(os.getpid())" in helper
    assert "(candidate_cgroup/'memory.max').write_text(str(limits['memory'])" in helper
    assert "(candidate_cgroup/'memory.swap.max').write_text('0'" in helper
    assert "(candidate_cgroup/'memory.oom.group').write_text('1'" in helper
    assert "(candidate_cgroup/'pids.max').write_text(str(limits['pids'])" in helper
    assert "(candidate_cgroup/'cgroup.kill').write_text('1'" in helper
    assert "ready" in helper and "start" in helper
    assert helper.index("start") < helper.index("os.fork()")
    assert "release_read,release_write=os.pipe()" in helper
    assert "os.read(release_read,1)" in helper
    assert "(candidate_cgroup/'cgroup.procs').write_text(str(pid)" not in helper
    assert helper.index("os.read(release_read,1)") < helper.index(
        "os.execvpe(argv[0],argv,os.environ)"
    )
    assert "os.pidfd_open(pid" in helper
    assert "select.poll()" in helper
    assert "poller.poll" in helper
    assert "os.waitpid(pid,0)" in helper
    assert "timed_out" in helper
    assert "candidate-start.json" not in helper
    assert supervisor._PIDFD_PROTOCOL_SOURCE.strip() in helper
    assert "timeout=limits['trusted_timeout']" in helper
    assert plan.launch_payload is not None
    assert plan.launch_payload["limits"]["timeout"] == 17
    assert "result.json" in helper and "finish" in helper
    assert "candidate cgroup remained populated" in helper
    assert "candidate_cgroup.rmdir()" in helper
    assert "monitor_cgroup.rmdir()" in helper
    assert "-t','tmpfs" in helper
    assert "/proc/self/mountinfo" in helper
    assert "writable tmpfs mount probe failed" in helper
    assert "statvfs" in helper
    assert "writable quota" in helper
    assert "copytree" in helper
    assert "replace_host" not in helper
    assert "_publish_writable_files" not in helper
    assert helper.index("candidate.json") < helper.index("result.tmp")
    assert helper.index("mount_lines=") < helper.index(
        "protocol_send({'kind':'ready'"
    )
    assert helper.index("mount_lines=") < helper.index(
        "(control/'ready').write_text"
    )
    assert plan.bwrap_argv.count("@PDD-CGROUP@") == 1
    cgroup_source = plan.bwrap_argv.index("@PDD-CGROUP@")
    assert plan.bwrap_argv[cgroup_source - 1] == "--bind"
    assert plan.bwrap_argv[cgroup_source + 1] == "/sys/fs/cgroup"
    status_supervisor = plan.bwrap_argv.index(
        supervisor._INNER_STATUS_SUPERVISOR_SOURCE
    )
    assert plan.bwrap_argv[status_supervisor + 3] == "/sys/fs/cgroup"


def _generated_pidfd_protocol(namespace: dict[str, object] | None = None):
    values = {"os": os, "select": __import__("select"), "math": math}
    if namespace:
        values.update(namespace)
    exec(supervisor._PIDFD_PROTOCOL_SOURCE, values)  # pylint: disable=exec-used
    return values["_supervise_candidate"]


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not hasattr(os, "pidfd_open"),
    reason="requires Linux pidfds",
)
@pytest.mark.parametrize(
    ("mode", "expected"),
    [
        ("zero", (0, False)),
        ("signal", (-signal.SIGTERM, False)),
        ("exit124", (124, False)),
        ("timeout", (124, True)),
    ],
)
def test_generated_pidfd_protocol_real_child_lifecycle(
    mode: str, expected: tuple[int, bool],
) -> None:
    protocol = _generated_pidfd_protocol()
    before = set(os.listdir("/proc/self/fd"))
    pid = os.fork()
    if pid == 0:
        if mode == "signal":
            os.kill(os.getpid(), signal.SIGTERM)
        elif mode == "exit124":
            os._exit(124)
        elif mode == "timeout":
            time.sleep(5)
        os._exit(0)
    try:
        assert protocol(pid, .03 if mode == "timeout" else 2) == expected
        with pytest.raises(ChildProcessError):
            os.waitpid(pid, os.WNOHANG)
        assert set(os.listdir("/proc/self/fd")) == before
    finally:
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            os.waitpid(pid, 0)
        except ChildProcessError:
            pass


@pytest.mark.parametrize("failure", ["pidfd_open", "poll", "waitpid"])
def test_generated_pidfd_protocol_errors_reap_once_and_close(
    failure: str,
) -> None:
    class FakeSystem:
        def __init__(self) -> None:
            self.closed = []
            self.killed = []
            self.wait_calls = 0
            self.reaps = 0

        def pidfd_open(self, _pid, _flags):
            if failure == "pidfd_open":
                raise OSError("pidfd failed")
            return 17

        def close(self, descriptor):
            self.closed.append(descriptor)

        def kill(self, pid, sig):
            self.killed.append((pid, sig))

        def waitpid(self, pid, _options):
            self.wait_calls += 1
            if failure == "waitpid" and self.wait_calls == 1:
                raise OSError("wait failed")
            self.reaps += 1
            return pid, 0

        @staticmethod
        def waitstatus_to_exitcode(_status):
            return 0

    class FakePoll:
        def register(self, *_args):
            return None

        def poll(self, _timeout):
            if failure == "poll":
                raise OSError("poll failed")
            return [(17, 1)]

    fake_system = FakeSystem()
    fake_select = SimpleNamespace(POLLIN=1, poll=lambda: FakePoll())
    protocol = _generated_pidfd_protocol(
        {"os": fake_system, "select": fake_select}
    )

    with pytest.raises(OSError, match="failed"):
        protocol(321, 1)

    assert fake_system.reaps == 1
    assert fake_system.killed == [(321, signal.SIGKILL)]
    assert fake_system.closed == ([] if failure == "pidfd_open" else [17])


def test_scope_unit_name_is_unique_and_strictly_validated() -> None:
    first = supervisor._scope_unit_name()
    second = supervisor._scope_unit_name()

    assert first != second
    assert supervisor._validated_scope_unit(first) == first
    for invalid in (
        "pdd-validator.scope", "../other.scope",
        "pdd-validator-00000000000000000000000000000000.service",
    ):
        with pytest.raises(RuntimeError, match="invalid protected scope unit"):
            supervisor._validated_scope_unit(invalid)


def test_scope_cleanup_error_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A failed systemd scope teardown must invalidate an otherwise clean exit."""
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    tools = supervisor._trusted_tools()
    monkeypatch.setattr(
        supervisor.subprocess, "run",
        lambda command, **_kwargs: subprocess.CompletedProcess(
            command, 1, "", "cannot remove scope"
        ),
    )

    with pytest.raises(RuntimeError, match="scope teardown failed"):
        supervisor._stop_scope(
            "pdd-validator-00000000000000000000000000000000.scope", tools
        )


def test_scope_cleanup_does_not_misclassify_bus_error_as_absent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    tools = supervisor._trusted_tools()
    monkeypatch.setattr(
        supervisor, "_root_run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess(
            [], 1, "", "Failed to connect to bus: unit not found"
        ),
    )

    with pytest.raises(RuntimeError, match="teardown failed"):
        supervisor._stop_scope(supervisor._scope_unit_name(), tools)


def test_root_tool_timeout_is_normalized_to_infrastructure_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    tools = supervisor._trusted_tools()
    monkeypatch.setattr(
        supervisor.subprocess, "run",
        lambda *args, **kwargs: (_ for _ in ()).throw(
            subprocess.TimeoutExpired(args[0], kwargs.get("timeout", 0))
        ),
    )

    with pytest.raises(RuntimeError, match="timed out"):
        supervisor._root_run(tools, ["show", supervisor._scope_unit_name()])


def test_mountinfo_read_error_fails_closed(monkeypatch: pytest.MonkeyPatch) -> None:
    original = Path.read_text

    def read_text(path: Path, *args, **kwargs):
        if path == Path("/proc/self/mountinfo"):
            raise OSError("mountinfo unavailable")
        return original(path, *args, **kwargs)

    monkeypatch.setattr(Path, "read_text", read_text)

    with pytest.raises(RuntimeError, match="mount table"):
        supervisor._mounted_paths()


def test_staging_umount_timeout_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    tools = supervisor._trusted_tools()
    target = tmp_path / "mounted"
    target.mkdir()
    plan = supervisor._ScopePlan(
        supervisor._scope_unit_name(), tmp_path, "", (), (), (target,), tools,
    )
    monkeypatch.setattr(supervisor, "_mounted_paths", lambda: {target})
    monkeypatch.setattr(
        supervisor.subprocess, "run",
        lambda *args, **kwargs: (_ for _ in ()).throw(
            subprocess.TimeoutExpired(args[0], kwargs.get("timeout", 0))
        ),
    )

    with pytest.raises(RuntimeError, match="timed out"):
        supervisor._cleanup_staging(plan)


def test_scope_probe_requires_systemd_and_kernel_limits_before_release(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Accept a scope only when systemd and cgroup-v2 report every hard limit."""
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    tools = supervisor._trusted_tools()
    cgroup = tmp_path / "scope-cgroup"
    cgroup.mkdir()
    candidate = cgroup / "candidate"
    candidate.mkdir()
    candidate.chmod(0o755)
    monitor = cgroup / "monitor"
    monitor.mkdir()
    monitor.chmod(0o755)
    (cgroup / "cgroup.procs").write_text("", encoding="ascii")
    (monitor / "cgroup.procs").write_text("123\n", encoding="ascii")
    (candidate / "cgroup.procs").write_text("", encoding="ascii")
    values = {
        "memory.max": "2147483648", "memory.swap.max": "0",
        "memory.oom.group": "1", "pids.max": "128",
        "memory.events": "oom 3\noom_kill 2\n",
        "pids.events": "max 4\n",
    }
    for name, value in values.items():
        (candidate / name).write_text(value, encoding="ascii")
    properties = {
        "LoadState": "loaded", "ActiveState": "active",
        "ControlGroup": "/system.slice/example.scope",
        "MemoryMax": "infinity", "MemorySwapMax": "infinity",
        "TasksMax": "infinity", "OOMPolicy": "continue", "Delegate": "yes",
        "KillMode": "control-group", "Result": "success",
    }
    monkeypatch.setattr(supervisor, "_scope_properties", lambda *_args: properties)
    monkeypatch.setattr(supervisor, "_scope_cgroup", lambda _properties: cgroup)
    plan = supervisor._ScopePlan(
        supervisor._scope_unit_name(), tmp_path, "", (), (), (), tools,
    )

    actual_cgroup, memory, pids = supervisor._probe_scope(
        plan, SupervisorLimits()
    )

    assert actual_cgroup == candidate
    assert memory["oom_kill"] == 2
    assert pids["max"] == 4
    properties["KillMode"] = "process"
    with pytest.raises(RuntimeError, match="properties unverified"):
        supervisor._probe_scope(plan, SupervisorLimits())


def test_scope_probe_rejects_missing_candidate_leaf(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The parent scope is never accepted as the candidate resource domain."""
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    tools = supervisor._trusted_tools()
    parent = tmp_path / "scope-cgroup"
    parent.mkdir()
    properties = {
        "LoadState": "loaded", "ActiveState": "active",
        "ControlGroup": "/system.slice/example.scope",
        "MemoryMax": "infinity", "MemorySwapMax": "infinity",
        "TasksMax": "infinity", "OOMPolicy": "continue", "Delegate": "yes",
        "KillMode": "control-group", "Result": "success",
    }
    monkeypatch.setattr(supervisor, "_scope_properties", lambda *_args: properties)
    monkeypatch.setattr(supervisor, "_scope_cgroup", lambda _properties: parent)
    plan = supervisor._ScopePlan(
        supervisor._scope_unit_name(), tmp_path, "", (), (), (), tools,
    )

    with pytest.raises(RuntimeError, match="candidate leaf"):
        supervisor._probe_scope(plan, SupervisorLimits())


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires Linux cgroup-v2 and bubblewrap",
)
@pytest.mark.parametrize("case", ["oom", "pids", "timeout"])
def test_exact_supervisor_candidate_leaf_preserves_monitor_and_events(
    tmp_path: Path, case: str,
) -> None:
    """Exercise the generated helper against real delegated cgroup-v2 limits."""
    commands = {
        "oom": [sys.executable, "-c", "bytearray(256 * 1024 * 1024)"],
        "pids": [
            sys.executable,
            "-c",
            "import subprocess,sys;"
            "children=[subprocess.Popen([sys.executable,'-c','import time;time.sleep(2)']) "
            "for _ in range(16)];[child.wait() for child in children]",
        ],
        "timeout": [sys.executable, "-c", "import time;time.sleep(30)"],
    }
    limits = SupervisorLimits(
        max_memory_bytes=96 * 1024 * 1024,
        max_virtual_memory_bytes=512 * 1024 * 1024,
        max_processes=8,
    )
    result, surviving = run_supervised(
        commands[case], cwd=tmp_path, timeout=.1 if case == "timeout" else 10,
        env=dict(os.environ), writable_roots=(tmp_path,), limits=limits,
    )

    assert not surviving
    assert "scope produced no protected candidate record" not in result.stderr
    if case == "oom":
        assert result.returncode != 125, result.stderr
        assert "cgroup memory.events oom delta=" in result.stderr
    elif case == "pids":
        assert result.returncode != 0, result.stderr
        assert "cgroup pids.events max delta=" in result.stderr
    else:
        assert result.returncode == 124, result.stderr


@pytest.mark.parametrize(
    ("filename", "content", "missing"),
    [
        ("memory.events", "oom 0\n", "oom_kill"),
        ("memory.events", "oom_kill 0\n", "oom"),
        ("pids.events", "other 0\n", "max"),
    ],
)
def test_cgroup_event_counters_require_authoritative_keys(
    tmp_path: Path, filename: str, content: str, missing: str,
) -> None:
    (tmp_path / filename).write_text(content, encoding="ascii")

    with pytest.raises(RuntimeError, match=missing):
        supervisor._cgroup_events(tmp_path, filename)


def test_signal_termination_retains_zero_cgroup_event_deltas() -> None:
    """A signal stays a signal while proving configured cgroup limits did not fire."""
    telemetry = supervisor.CgroupResourceTelemetry(
        memory_oom_delta=0,
        memory_oom_kill_delta=0,
        pids_max_delta=0,
    )

    termination = supervisor._termination_evidence(
        -signal.SIGABRT,
        timed_out=False,
        timeout_seconds=30,
        resource_limit=None,
        resource_telemetry=telemetry,
    )

    assert termination.kind is supervisor.TerminationKind.SIGNAL
    assert termination.signal_number == signal.SIGABRT
    assert termination.resource_limit is None
    assert termination.resource_telemetry == telemetry


def test_cgroup_resource_telemetry_rejects_counter_regression() -> None:
    """Kernel counters must be monotonic before becoming trusted diagnostics."""
    with pytest.raises(RuntimeError, match="counter regressed"):
        supervisor._cgroup_resource_telemetry(
            {"oom": 2, "oom_kill": 1},
            {"oom": 1, "oom_kill": 1},
            {"max": 0},
            {"max": 0},
        )


def test_scope_cleanup_targets_only_validated_unique_unit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Teardown uses whole-group systemd operations for exactly one unit."""
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    tools = supervisor._trusted_tools()
    unit = supervisor._scope_unit_name()
    commands = []

    def run(_tools, arguments, **_kwargs):
        commands.append(arguments)
        if len(commands) == 5:
            return subprocess.CompletedProcess(arguments, 0, "LoadState=not-found\n", "")
        return subprocess.CompletedProcess(arguments, 0, "LoadState=loaded\n", "")

    monkeypatch.setattr(supervisor, "_root_run", run)

    supervisor._stop_scope(unit, tools)

    assert [command[0] for command in commands] == [
        "show", "kill", "show", "stop", "show",
    ]
    assert all(unit in command for command in commands)
    assert commands[1][:3] == ["kill", "--kill-whom=all", "--signal=SIGKILL"]


def test_scope_cleanup_accepts_exact_unit_disappearance_after_kill(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A successful kill may synchronously collect the exact transient scope."""
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    tools = supervisor._trusted_tools()
    unit = supervisor._scope_unit_name()
    commands = []

    def run(_tools, arguments, **_kwargs):
        commands.append(arguments)
        if arguments[0] == "show" and len(commands) == 1:
            return subprocess.CompletedProcess(arguments, 0, "LoadState=loaded\n", "")
        if arguments[0] == "kill":
            return subprocess.CompletedProcess(arguments, 0, "", "")
        if arguments[0] == "show":
            return subprocess.CompletedProcess(arguments, 0, "LoadState=not-found\n", "")
        pytest.fail(f"cleanup acted on a collected scope: {arguments}")

    monkeypatch.setattr(supervisor, "_root_run", run)

    supervisor._stop_scope(unit, tools)

    assert [command[0] for command in commands] == ["show", "kill", "show"]


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires Linux kernel namespace containment",
)
def test_sandboxed_python_imports_standard_library_after_command_construction(
    tmp_path: Path,
) -> None:
    result, surviving = run_supervised(
        [sys.executable, "-c", "import math; print(math.pi)"],
        cwd=tmp_path,
        timeout=10,
        env=dict(os.environ),
        writable_roots=(tmp_path,),
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == str(math.pi)
    assert surviving is False


def test_linked_libraries_keeps_loader_alias_and_resolved_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    target = tmp_path / "libm-real.so"
    target.write_bytes(b"library")
    alias = tmp_path / "libm.so.6"
    alias.symlink_to(target)
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess(
            [], 0, f"libm.so.6 => {alias} (0x0000)\n", ""
        ),
    )

    assert _linked_libraries(tmp_path / "python") == (target, alias)


def test_sandbox_library_path_uses_only_measured_loader_directories(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    loader_alias = tmp_path / "lib" / "libm.so.6"
    loader_target = tmp_path / "usr" / "lib" / "libm-real.so"
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths",
        lambda: (
            ("native/lib/libm.so.6", loader_alias),
            ("native/usr/lib/libm-real.so", loader_target),
            ("interpreter/python", tmp_path / "python"),
        ),
    )

    search_path = _sandbox_library_path({"LD_LIBRARY_PATH": "/checker/lib"})

    assert search_path.split(os.pathsep)[:2] == [
        str(loader_alias.parent), str(loader_target.parent)
    ]
    assert "/checker/lib" in search_path.split(os.pathsep)


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires Linux kernel namespace containment",
)
def test_detached_session_descendant_is_terminated(tmp_path: Path) -> None:
    marker = tmp_path / "escaped"
    child = (
        "import os,sys,time; os.setsid(); os.close(1); os.close(2); time.sleep(1); "
        "open(sys.argv[1], 'w').write('escaped')"
    )
    parent = (
        "import subprocess,sys; "
        "subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]], "
        "start_new_session=False)"
    )
    result, surviving = run_supervised(
        [sys.executable, "-c", parent, child, str(marker)],
        cwd=tmp_path,
        timeout=10,
        env=dict(os.environ),
        writable_roots=(tmp_path,),
    )
    assert result.returncode == 0
    assert surviving is False
    time.sleep(1.2)
    assert not marker.exists()


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires Linux kernel namespace containment",
)
def test_detached_descendant_cannot_escape_by_removing_marker(tmp_path: Path) -> None:
    marker = tmp_path / "escaped-without-marker"
    child = (
        "import os,sys,time; os.setsid(); os.close(1); os.close(2); time.sleep(1); "
        "open(sys.argv[1], 'w').write('escaped')"
    )
    parent = (
        "import os,subprocess,sys,time; child_env=dict(os.environ); "
        "child_env.pop('PDD_SUPERVISION_TOKEN', None); "
        "subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]], "
        "env=child_env)"
    )
    result, surviving = run_supervised(
        [sys.executable, "-c", parent, child, str(marker)], cwd=tmp_path,
        timeout=10, env=dict(os.environ), writable_roots=(tmp_path,),
    )
    assert result.returncode == 0
    assert surviving is False
    time.sleep(1.2)
    assert not marker.exists()


@pytest.mark.skipif(not shutil.which("bwrap"), reason="requires Linux bubblewrap")
def test_candidate_cannot_read_absolute_host_sentinel(tmp_path: Path) -> None:
    sentinel = tmp_path.parent / "protected-host-secret"
    sentinel.write_text("secret", encoding="utf-8")
    result, surviving = run_supervised(
        [
            sys.executable, "-c",
            "import pathlib,sys; pathlib.Path(sys.argv[1]).read_text()",
            str(sentinel),
        ],
        cwd=tmp_path, timeout=10, env=dict(os.environ), writable_roots=(tmp_path,),
    )
    assert result.returncode != 0
    assert surviving is False


@pytest.mark.skipif(not shutil.which("bwrap"), reason="requires Linux bubblewrap")
def test_immediate_detached_child_cannot_forge_checker_result_channel(
    tmp_path: Path,
) -> None:
    scratch = tmp_path / "scratch"
    scratch.mkdir()
    result_channel = tmp_path / "junit.xml"
    result_channel.write_text("checker-owned", encoding="utf-8")
    child = (
        "import os,sys,time; os.setsid(); time.sleep(.1); "
        "open(sys.argv[1], 'w').write('forged')"
    )
    parent = (
        "import os,subprocess,sys; env=dict(os.environ); "
        "env.pop('PDD_SUPERVISION_TOKEN', None); "
        "subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]], env=env)"
    )
    completed, _surviving = run_supervised(
        [sys.executable, "-c", parent, child, str(result_channel)],
        cwd=scratch, timeout=10, env=dict(os.environ),
        writable_roots=(scratch,),
    )
    assert completed.returncode == 0
    time.sleep(0.3)
    assert result_channel.read_text(encoding="utf-8") == "checker-owned"


@pytest.mark.skipif(not shutil.which("bwrap"), reason="requires Linux bubblewrap")
def test_output_is_bounded(tmp_path: Path) -> None:
    result, _surviving = run_supervised(
        [sys.executable, "-c", "print('x' * 20000000)"], cwd=tmp_path,
        timeout=10, env=dict(os.environ), writable_roots=(tmp_path,),
    )
    assert len(result.stdout.encode()) <= 16 * 1024 * 1024
    assert result.returncode != 0


@pytest.mark.skipif(not shutil.which("bwrap"), reason="requires Linux bubblewrap")
@pytest.mark.parametrize(
    "program",
    [
        "bytearray(256 * 1024 * 1024)",
        "open('large', 'wb').truncate(8 * 1024 * 1024)",
        "while True: pass",
        "import subprocess,sys,time; "
        "children=[subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(2)']) "
        "for _ in range(16)]; [child.wait() for child in children]",
    ],
)
def test_memory_disk_and_process_limits_fail_closed(tmp_path: Path, program: str) -> None:
    limits = SupervisorLimits(
        max_memory_bytes=128 * 1024 * 1024,
        max_writable_bytes=1024 * 1024,
        max_cpu_seconds=1,
        max_processes=4,
    )
    result, _surviving = run_supervised(
        [sys.executable, "-c", program], cwd=tmp_path, timeout=10,
        env=dict(os.environ), writable_roots=(tmp_path,), limits=limits,
    )
    assert result.returncode != 0


def test_writable_accounting_errors_fail_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    inaccessible = tmp_path / "inaccessible"
    inaccessible.mkdir()
    monkeypatch.setattr(
        Path, "rglob", lambda _path, _pattern: (_ for _ in ()).throw(OSError("denied"))
    )

    with pytest.raises(RuntimeError, match="writable accounting failed"):
        supervisor._writable_size((inaccessible,))


def test_supervisor_has_no_host_output_publication_api() -> None:
    assert "writable_files" not in inspect.signature(run_supervised).parameters
    assert not hasattr(supervisor, "_publish_writable_files")


def test_candidate_deadline_stops_before_trusted_postprocessing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    helper = """import json,pathlib,sys,time
control=pathlib.Path(sys.argv[1])
(control/'ready').write_text('ready',encoding='ascii')
while not (control/'start').exists(): time.sleep(.001)
record={'version':1,'state':'terminal','returncode':0,'timed_out':False}
(control/'candidate.json').write_text(json.dumps(record),encoding='ascii')
time.sleep(.2)
(control/'result.json').write_text(json.dumps(record),encoding='ascii')
while not (control/'finish').exists(): time.sleep(.001)
"""
    cgroup = tmp_path / "cgroup"
    cgroup.mkdir()
    (cgroup / "memory.events").write_text("oom 0\noom_kill 0\n", encoding="ascii")
    (cgroup / "pids.events").write_text("max 0\n", encoding="ascii")

    def sandbox(_command, _writable_roots, **kwargs):
        control = str(kwargs["control_directory"])
        plan = SimpleNamespace(
            unit_name="pdd-validator-00000000000000000000000000000000.scope",
            tools=SimpleNamespace(),
            launch_payload={
                "schema": "pdd-sandbox-launch-v1", "control": control,
            },
        )
        return [sys.executable, "-c", _launch_aware_mock_helper(helper)], plan

    monkeypatch.setattr(supervisor, "_sandbox_command", sandbox)
    monkeypatch.setattr(supervisor, "_prepare_staging", lambda _plan: None)
    monkeypatch.setattr(
        supervisor, "_probe_scope",
        lambda _plan, _limits: (cgroup, {"oom": 0, "oom_kill": 0}, {"max": 0}),
    )
    monkeypatch.setattr(supervisor, "_stop_scope", lambda *_args: None)
    monkeypatch.setattr(supervisor, "_cleanup_staging", lambda _plan: None)
    monkeypatch.setattr(
        supervisor, "_scope_properties", lambda *_args: {"Result": "success"}
    )
    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.1,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )

    assert result.returncode == 0, result.stderr
    assert surviving is False


def test_macos_fails_closed_without_kernel_lifetime_containment(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "darwin")
    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=1, env={},
        writable_roots=(tmp_path,),
    )
    assert result.returncode == 125
    assert "cannot prove process lifetime isolation" in result.stderr
    assert surviving is False


def test_playwright_construction_failure_is_typed_sandbox_error(tmp_path: Path) -> None:
    """Malformed descriptor construction never becomes candidate EXIT evidence."""
    result, surviving = run_supervised(
        [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=1, env={},
        writable_roots=(tmp_path,),
        playwright_snapshot_aggregate=supervisor.PlaywrightSnapshotAggregate(
            "{}", "a" * 64, "b" * 64, 198,
        ),
    )
    assert result.returncode == 125
    assert result.termination.kind is supervisor.TerminationKind.SANDBOX_ERROR
    assert "phase=construction" in result.stderr
    assert surviving is False


def test_file_size_limit_uses_writable_budget() -> None:
    limits = SupervisorLimits(max_output_bytes=1234, max_writable_bytes=987654)
    command = _limited_command(["/bin/true"], limits)
    assert "987654" in command
    assert "1234" not in command[1:7]


@pytest.mark.skipif(not shutil.which("bwrap"), reason="requires Linux bubblewrap")
def test_binary_output_has_aggregate_limit_and_deterministic_decode(tmp_path: Path) -> None:
    limits = SupervisorLimits(max_output_bytes=1024)
    result, _surviving = run_supervised(
        [sys.executable, "-c", "import os; os.write(1, b'\\xff' * 800); os.write(2, b'x' * 800)"],
        cwd=tmp_path, timeout=10, env=dict(os.environ),
        writable_roots=(tmp_path,), limits=limits,
    )
    assert result.returncode == 125
    assert len(result.stdout.encode("utf-8")) + len(result.stderr.encode("utf-8")) <= 3 * 1024
    assert "\ufffd" in result.stdout


@pytest.mark.real
@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires hosted Linux privileged supervision",
)
@pytest.mark.parametrize("adapter", ("pytest", "vitest", "playwright"))
def test_real_linux_adapter_environment_handoff(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, adapter: str,
) -> None:
    """Every adapter receives only its exact post-drop sanitized environment."""
    token = "d" * 32
    monkeypatch.setattr(
        supervisor.uuid, "uuid4", lambda: SimpleNamespace(hex=token)
    )
    home = tmp_path / "home"
    environments = {
        "pytest": {
            "HOME": str(home), "PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1",
            "PYTHONNOUSERSITE": "1",
        },
        "vitest": {
            "HOME": str(home), "NODE_ENV": "test",
            "XDG_CACHE_HOME": str(home / "cache"),
            "XDG_CONFIG_HOME": str(home / "config"),
        },
        "playwright": {
            "HOME": str(home), "NODE_ENV": "test",
            "NODE_PATH": "/opt/pdd/node_modules",
            "PLAYWRIGHT_BROWSERS_PATH": "/opt/pdd/browsers",
            "XDG_CACHE_HOME": str(home / "cache"),
            "XDG_CONFIG_HOME": str(home / "config"),
        },
    }
    environment = environments[adapter]
    expected = supervisor._parse_candidate_environment_record(
        supervisor._candidate_environment_record(
            environment, temp_directory=tmp_path, supervision_token=token
        )
    )

    result, surviving = run_supervised(
        [sys.executable, "-c", "import json,os;print(json.dumps(dict(os.environ),sort_keys=True))"],
        cwd=tmp_path, timeout=10, env=environment, writable_roots=(tmp_path,),
        temp_directory=tmp_path,
    )

    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout) == expected
    assert surviving is False


@pytest.mark.real
@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires hosted Linux privileged supervision",
)
def test_real_linux_authenticated_termination_and_cleanup(tmp_path: Path) -> None:
    """The production chain authenticates exit, signal, timeout, and pids evidence."""
    cases = (
        ([sys.executable, "-c", "raise SystemExit(17)"], 5,
         supervisor.TerminationKind.EXIT, 17),
        ([sys.executable, "-c",
          "import os,signal;os.kill(os.getpid(),signal.SIGTERM)"], 5,
         supervisor.TerminationKind.SIGNAL, -signal.SIGTERM),
        ([sys.executable, "-c", "import time;time.sleep(5)"], 1,
         supervisor.TerminationKind.TIMEOUT, 124),
    )
    for command, timeout, kind, returncode in cases:
        result, surviving = run_supervised(
            command, cwd=tmp_path, timeout=timeout, env=dict(os.environ),
            writable_roots=(tmp_path,),
        )
        assert isinstance(result, supervisor.SupervisedCompletedProcess)
        assert result.termination.kind is kind
        assert result.returncode == returncode
        assert surviving is False

    fork_program = (
        "import os,time\n"
        "for _ in range(32):\n"
        " try: pid=os.fork()\n"
        " except OSError: break\n"
        " if pid==0: time.sleep(2);os._exit(0)\n"
        "time.sleep(.1)\n"
    )
    result, surviving = run_supervised(
        [sys.executable, "-c", fork_program], cwd=tmp_path, timeout=5,
        env=dict(os.environ), writable_roots=(tmp_path,),
        limits=replace(SupervisorLimits(), max_processes=8),
    )
    assert result.termination.kind is supervisor.TerminationKind.RESOURCE_LIMIT
    assert result.termination.resource_limit == "pids"
    assert surviving is False


_ROOT_PROC_SCANNER_SOURCE = r"""
import json,os,pathlib,sys

payload=json.loads(sys.argv[1])
proc=pathlib.Path('/proc')
self_pid=os.getpid()

def fail(message):
    raise RuntimeError(message)

def vanished_or_fail(pid_dir, operation, error):
    if isinstance(error, FileNotFoundError):
        try:
            pid_dir.stat()
        except FileNotFoundError:
            raise ProcessLookupError from error
        except OSError as verify_error:
            fail(f'verify process ENOENT: pid={pid_dir.name}: '
                 f'{type(verify_error).__name__}: {verify_error}')
    fail(f'{operation}: pid={pid_dir.name}: {type(error).__name__}: {error}')

def read_text(path,pid_dir,operation,encoding='ascii'):
    try:
        return path.read_text(encoding=encoding)
    except OSError as error:
        vanished_or_fail(pid_dir,operation,error)

def identity(pid_dir):
    raw=read_text(pid_dir/'stat',pid_dir,'read stat')
    closing=raw.rfind(')')
    if closing<2:
        fail(f'parse stat: pid={pid_dir.name}: missing comm terminator')
    fields=raw[closing+2:].split()
    if (len(fields)<=19 or len(fields[0])!=1 or
            not fields[1].isdigit() or not fields[19].isdigit()):
        fail(f'parse stat: pid={pid_dir.name}: invalid fields')
    try:
        uid=pid_dir.stat().st_uid
    except OSError as error:
        vanished_or_fail(pid_dir,'stat process directory',error)
    return {'pid':int(pid_dir.name),'ppid':int(fields[1]),'state':fields[0],
            'start_time':fields[19],'uid':uid}

def namespace(pid_dir):
    path=pid_dir/'ns'/'mnt'
    try:
        link=os.readlink(path)
        inode=path.stat().st_ino
    except OSError as error:
        vanished_or_fail(pid_dir,'read mount namespace',error)
    if (not link.startswith('mnt:[') or not link.endswith(']') or inode<=0 or
            not link[5:-1].isdigit() or int(link[5:-1])!=inode):
        fail(f'parse mount namespace: pid={pid_dir.name}: {link!r}/{inode!r}')
    return link,inode

def cmdline(pid_dir):
    try:
        raw=(pid_dir/'cmdline').read_bytes()
    except OSError as error:
        vanished_or_fail(pid_dir,'read cmdline',error)
    try:
        return [value.decode('utf-8') for value in raw.split(b'\0') if value]
    except UnicodeError as error:
        fail(f'parse cmdline: pid={pid_dir.name}: {error}')

def wchan(pid_dir):
    return read_text(pid_dir/'wchan',pid_dir,'read wchan').strip()

def fd_links(pid_dir):
    directory=pid_dir/'fd'
    try:
        entries=list(directory.iterdir())
    except OSError as error:
        vanished_or_fail(pid_dir,'list descriptors',error)
    links=[]
    for entry in entries:
        try:
            links.append((int(entry.name),os.readlink(entry),entry.stat().st_ino))
        except FileNotFoundError as error:
            try:
                entry.lstat()
            except FileNotFoundError:
                continue
            except OSError as verify_error:
                fail(f'verify descriptor ENOENT: pid={pid_dir.name} fd={entry.name}: '
                     f'{type(verify_error).__name__}: {verify_error}')
            fail(f'read descriptor: pid={pid_dir.name} fd={entry.name}: '
                 f'ENOENT while descriptor still exists: {error}')
        except (OSError,ValueError) as error:
            fail(f'read descriptor: pid={pid_dir.name} fd={entry.name}: '
                 f'{type(error).__name__}: {error}')
    return links

def unescape(value):
    return value.replace('\\040',' ').replace('\\011','\t').replace('\\134','\\')

def canonical_path(value,label):
    if type(value) is not str or not value.startswith('/'):
        fail(f'{label} is not an absolute string path: {value!r}')
    path=pathlib.PurePosixPath(value)
    if str(path)!=value or any(part in ('.','..') for part in path.parts):
        fail(f'{label} is not canonical: {value!r}')
    return path

def owned_mount(point,prefix,targets):
    path=canonical_path(point,'mount point')
    if str(path) in targets:
        return True
    if prefix is None:
        return False
    try:
        path.relative_to(prefix)
    except ValueError:
        return False
    return True

def mounts(pid_dir):
    records=[]
    for line in read_text(pid_dir/'mountinfo',pid_dir,'read mountinfo','utf-8').splitlines():
        fields=line.split()
        if len(fields)<10 or '-' not in fields or not fields[0].isdigit():
            fail(f'parse mountinfo: pid={pid_dir.name}: {line!r}')
        records.append({'mount_id':int(fields[0]),'mount_point':unescape(fields[4])})
    return records

def cgroup_pids(path):
    if not path:
        return False,set()
    root=pathlib.Path(path)
    try:
        root.lstat()
    except FileNotFoundError:
        return False,set()
    except OSError as error:
        fail(f'stat cgroup: {root}: {type(error).__name__}: {error}')
    for attempt in range(2):
        found=set()
        try:
            files=list(root.rglob('cgroup.procs'))
            if not files:
                fail(f'cgroup has no membership files: {root}')
            for membership in files:
                values=membership.read_text(encoding='ascii').split()
                if any(not value.isdigit() for value in values):
                    fail(f'parse cgroup membership: {membership}')
                found.update(int(value) for value in values)
            return True,found
        except FileNotFoundError as error:
            try:
                root.lstat()
            except FileNotFoundError:
                return False,set()
            except OSError as verify_error:
                fail(f'verify cgroup ENOENT: {root}: '
                     f'{type(verify_error).__name__}: {verify_error}')
            if attempt==0:
                continue
            fail(f'read cgroup membership raced twice: {root}: {error}')
        except OSError as error:
            fail(f'read cgroup membership: {root}: {type(error).__name__}: {error}')
    fail(f'unreachable cgroup scan state: {root}')

try:
    cgroup_exists,members=cgroup_pids(payload.get('cgroup',''))
    watched=set(payload.get('watch_pids',[]))
    if any(type(pid) is not int or pid<=0 for pid in watched):
        fail('invalid watched PID payload')
    expected_namespace=payload.get('namespace')
    if expected_namespace is not None and (
            type(expected_namespace) is not dict or
            set(expected_namespace)!=set(('link','inode')) or
            type(expected_namespace.get('link')) is not str or
            type(expected_namespace.get('inode')) is not int):
        fail('invalid expected mount namespace payload')
    targets=set(payload.get('targets',[]))
    for value in targets:
        canonical_path(value,'target')
    prefix_value=payload.get('target_prefix','')
    prefix=canonical_path(prefix_value,'target prefix') if prefix_value else None
    identities=[]; cgroup_members=[]; watched_processes=[]
    current_holders=[]; fd_holders=[]; mount_holders=[]
    for pid_dir in sorted(
        (path for path in proc.iterdir() if path.name.isdigit()),
        key=lambda path:int(path.name),
    ):
        if int(pid_dir.name)==self_pid:
            continue
        try:
            record=identity(pid_dir)
            identities.append(record.copy())
            if record['state']=='Z':
                if record['pid'] in members:
                    cgroup_members.append(record.copy())
                if record['pid'] in watched:
                    watched_processes.append(record.copy())
                continue
            ns_link,ns_inode=namespace(pid_dir)
            descriptors=fd_links(pid_dir)
            mount_records=mounts(pid_dir)
            verified=identity(pid_dir)
            if (verified['pid'],verified['start_time']) != (
                    record['pid'],record['start_time']):
                identities.pop()
                continue
            record.update({'ppid':verified['ppid'],'state':verified['state'],
                           'uid':verified['uid']})
            record.update({'namespace':ns_link,'namespace_inode':ns_inode})
            identities[-1]=record.copy()
            if record['pid'] in members or record['pid'] in watched:
                record['cmdline']=cmdline(pid_dir)
                record['wchan']=wchan(pid_dir)
                final=identity(pid_dir)
                if (final['pid'],final['start_time']) != (
                        record['pid'],record['start_time']):
                    identities.pop()
                    continue
                record.update({'ppid':final['ppid'],'state':final['state'],
                               'uid':final['uid']})
                identities[-1]=record.copy()
            if record['pid'] in members:
                cgroup_members.append(record.copy())
            if record['pid'] in watched:
                watched_processes.append(record.copy())
            if expected_namespace is not None and (
                ns_link==expected_namespace['link'] and
                ns_inode==expected_namespace['inode']
            ):
                current_holders.append(record|{'holder_kind':'current'})
            if expected_namespace is not None:
                for fd,link,inode in descriptors:
                    if (link==expected_namespace['link'] and
                            inode==expected_namespace['inode']):
                        fd_holders.append(record|{
                            'holder_kind':'fd','fd':fd,
                            'fd_path':str(pid_dir/'fd'/str(fd)),
                            'fd_link':link,'fd_inode':inode,
                        })
            for mount_record in mount_records:
                point=mount_record['mount_point']
                in_expected_namespace=(
                    expected_namespace is None or
                    (ns_link==expected_namespace['link'] and
                     ns_inode==expected_namespace['inode'])
                )
                if in_expected_namespace and owned_mount(point,prefix,targets):
                    mount_holders.append(record|mount_record|{'holder_kind':'mount'})
        except ProcessLookupError:
            continue
    final_cgroup_exists,final_members=cgroup_pids(payload.get('cgroup',''))
    cgroup_exists=final_cgroup_exists
    cgroup_members=[
        record for record in cgroup_members if record['pid'] in final_members
    ]
    output={
        'scanner_pid':self_pid,'cgroup_exists':cgroup_exists,
        'identities':identities,'cgroup_members':cgroup_members,
        'watched':watched_processes,'current_holders':current_holders,
        'fd_holders':fd_holders,'mount_holders':mount_holders,
    }
    print(json.dumps(output,sort_keys=True,separators=(',',':')))
except Exception as error:
    print(f'root proc scanner failed: {type(error).__name__}: {error}',file=sys.stderr)
    raise SystemExit(2)
"""


def _root_proc_scan(
    *, cgroup: Path | None = None, namespace: dict[str, object] | None = None,
    targets: tuple[Path, ...] = (), target_prefix: Path | None = None,
    watch_pids: tuple[int, ...] = (),
) -> dict[str, object]:
    """Run one bounded root scanner that fails closed on ambiguous procfs evidence."""
    payload = {
        "cgroup": str(cgroup) if cgroup is not None else "",
        "namespace": namespace,
        "targets": [str(path) for path in targets],
        "target_prefix": str(target_prefix) if target_prefix is not None else "",
        "watch_pids": list(watch_pids),
    }
    scanner_python = supervisor._trusted_tools().helper_python
    try:
        completed = subprocess.run(
            ["sudo", "-n", str(scanner_python), "-I", "-S", "-c",
             _ROOT_PROC_SCANNER_SOURCE, json.dumps(payload)],
            capture_output=True, text=True, check=False, timeout=10,
        )
    except subprocess.TimeoutExpired as exc:
        raise AssertionError("root proc scanner exceeded its 10 second bound") from exc
    assert completed.returncode == 0, completed.stderr
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise AssertionError(
            f"root proc scanner returned invalid JSON: {completed.stdout!r}"
        ) from exc
    assert isinstance(result, dict), result
    return result


def _process_key(record: dict[str, object]) -> tuple[int, str]:
    """Return the PID-reuse-safe identity used by cleanup assertions."""
    return int(record["pid"]), str(record["start_time"])


def _canonical_owned_mount_point(
    value: str, control_prefix: Path, targets: tuple[Path, ...] = (),
) -> bool:
    """Validate one canonical absolute mountpoint and test component containment."""
    if not isinstance(value, str) or not value.startswith("/"):
        raise ValueError(f"mount point is not absolute: {value!r}")
    point = PurePosixPath(value)
    if str(point) != value or any(part in {".", ".."} for part in point.parts):
        raise ValueError(f"mount point is not canonical: {value!r}")
    prefix = PurePosixPath(str(control_prefix))
    if not prefix.is_absolute() or str(prefix) != str(control_prefix):
        raise ValueError(f"control prefix is not canonical: {control_prefix!r}")
    exact_targets = {PurePosixPath(str(target)) for target in targets}
    if point in exact_targets:
        return True
    try:
        point.relative_to(prefix)
    except ValueError:
        return False
    return True


def _exact_namespace_mounts(
    scan: dict[str, object], namespace: dict[str, object], control_prefix: Path,
    targets: tuple[Path, ...] = (),
) -> tuple[Path, ...]:
    """Return only canonical owned mounts reported from the captured namespace."""
    mounts = set()
    for record in scan["mount_holders"]:
        if (
            record.get("namespace") != namespace["link"]
            or record.get("namespace_inode") != namespace["inode"]
        ):
            continue
        value = str(record["mount_point"])
        if _canonical_owned_mount_point(value, control_prefix, targets):
            mounts.add(Path(value))
    return tuple(sorted(mounts))


def _namespace_entry_path(
    holder: dict[str, object], namespace: dict[str, object],
) -> str:
    """Build the exact procfs namespace entry after strict holder-schema checks."""
    pid = holder.get("pid")
    start_time = holder.get("start_time")
    if type(pid) is not int or pid <= 0 or not str(start_time).isdigit():
        raise ValueError("namespace holder has invalid process identity")
    current_link = holder.get("namespace")
    current_inode = holder.get("namespace_inode")
    if (
        not isinstance(current_link, str)
        or not current_link.startswith("mnt:[") or not current_link.endswith("]")
        or type(current_inode) is not int or current_inode <= 0
    ):
        raise ValueError("namespace holder has invalid current namespace identity")
    kind = holder.get("holder_kind")
    if kind == "current":
        if (
            holder.get("namespace") != namespace.get("link")
            or holder.get("namespace_inode") != namespace.get("inode")
        ):
            raise ValueError("current holder does not match captured namespace")
        return f"/proc/{pid}/ns/mnt"
    if kind != "fd":
        raise ValueError(f"unsupported namespace holder kind: {kind!r}")
    descriptor = holder.get("fd")
    if type(descriptor) is not int or descriptor < 0:
        raise ValueError("FD-only namespace holder has invalid descriptor")
    expected_path = f"/proc/{pid}/fd/{descriptor}"
    if holder.get("fd_path") != expected_path:
        raise ValueError("FD-only namespace holder has wrong descriptor path")
    if (
        holder.get("fd_link") != namespace["link"]
        or holder.get("fd_inode") != namespace["inode"]
    ):
        raise ValueError("FD-only namespace holder has wrong descriptor identity")
    return expected_path


def _holder_key(record: dict[str, object]) -> tuple[object, ...]:
    """Return the complete identity of one current or FD-only namespace holder."""
    return (
        record.get("holder_kind"), *_process_key(record), record.get("fd"),
        record.get("fd_path"), record.get("fd_link"), record.get("fd_inode"),
        record.get("namespace"),
        record.get("namespace_inode"),
    )


def _select_captured_namespace_holder(
    scan: dict[str, object], captured: tuple[dict[str, object], ...],
    namespace: dict[str, object],
) -> dict[str, object] | None:
    """Select only a still-live holder with the complete previously captured identity."""
    captured_keys = {_holder_key(record) for record in captured}
    candidates = [*scan["current_holders"], *scan["fd_holders"]]
    for record in candidates:
        if _holder_key(record) in captured_keys:
            _namespace_entry_path(record, namespace)
            return record
    return None


def _exact_unit_not_found(completed: object) -> bool:
    """Accept only canonical successful systemd LoadState=not-found output."""
    return (
        getattr(completed, "returncode", None) == 0
        and getattr(completed, "stdout", None) == "not-found\n"
        and getattr(completed, "stderr", None) == ""
    )


_NSENTER_REVALIDATOR_SOURCE = r"""
import json,os,pathlib,sys

payload=json.loads(sys.argv[1])
holder=payload['holder']; namespace=payload['namespace']
pid=holder.get('pid'); start_time=holder.get('start_time')
if type(pid) is not int or pid<=0 or type(start_time) is not str:
    raise SystemExit('invalid holder process identity')
proc=pathlib.Path('/proc')/str(pid)

def identity():
    raw=(proc/'stat').read_text(encoding='ascii')
    closing=raw.rfind(')'); fields=raw[closing+2:].split()
    if closing<2 or len(fields)<=19 or not fields[19].isdigit():
        raise RuntimeError('invalid holder stat')
    return fields[19]

def exact_namespace(path):
    link=os.readlink(path); inode=path.stat().st_ino
    if link!=namespace['link'] or inode!=namespace['inode']:
        raise RuntimeError('holder namespace identity changed')
    return str(path)

if identity()!=start_time:
    raise RuntimeError('holder PID was reused')
current_path=proc/'ns'/'mnt'
current_link=os.readlink(current_path); current_inode=current_path.stat().st_ino
if (current_link!=holder.get('namespace') or
        current_inode!=holder.get('namespace_inode')):
    raise RuntimeError('holder current namespace identity changed')
kind=holder.get('holder_kind')
if kind=='current':
    entry=exact_namespace(current_path)
elif kind=='fd':
    fd=holder.get('fd')
    if type(fd) is not int or fd<0:
        raise RuntimeError('invalid namespace descriptor')
    entry_path=proc/'fd'/str(fd)
    link=os.readlink(entry_path); inode=entry_path.stat().st_ino
    if (str(entry_path)!=holder.get('fd_path') or
            link!=holder.get('fd_link') or inode!=holder.get('fd_inode') or
            link!=namespace['link'] or inode!=namespace['inode']):
        raise RuntimeError('namespace descriptor identity changed')
    entry=str(entry_path)
else:
    raise RuntimeError('invalid namespace holder kind')
if identity()!=start_time:
    raise RuntimeError('holder identity raced before namespace entry')
operation=payload.get('operation')
if operation=='unmount':
    command=[payload['umount'],payload['mount']]
elif operation=='scan':
    command=[payload['python'],'-I','-S','-c',payload['scanner'],
             json.dumps(payload['scan_payload'],sort_keys=True)]
else:
    raise RuntimeError('invalid namespace operation')
os.execv(payload['nsenter'],[payload['nsenter'],'--mount='+entry,'--',*command])
"""


_NAMESPACE_MOUNT_SCANNER_SOURCE = r"""
import json,pathlib,sys

payload=json.loads(sys.argv[1])

def canonical(value,label):
    if type(value) is not str or not value.startswith('/'):
        raise RuntimeError(f'{label} is not absolute: {value!r}')
    path=pathlib.PurePosixPath(value)
    if str(path)!=value or any(part in ('.','..') for part in path.parts):
        raise RuntimeError(f'{label} is not canonical: {value!r}')
    return path

prefix=canonical(payload['prefix'],'prefix')
targets={str(canonical(value,'target')) for value in payload['targets']}
mounts=[]
for line in pathlib.Path('/proc/self/mountinfo').read_text(encoding='utf-8').splitlines():
    fields=line.split()
    if len(fields)<10 or '-' not in fields or not fields[0].isdigit():
        raise RuntimeError(f'malformed mountinfo: {line!r}')
    value=fields[4].replace('\\040',' ').replace('\\011','\t').replace('\\134','\\')
    point=canonical(value,'mount point')
    try:
        point.relative_to(prefix); contained=True
    except ValueError:
        contained=False
    if str(point) in targets or contained:
        mounts.append(str(point))
print(json.dumps(sorted(set(mounts)),separators=(',',':')))
"""


_BLOCKED_WCHAN_MARKERS = ("sleep", "wait", "pause", "futex")


def _assert_exact_blocked_role_snapshot(
    expected_roles: list[dict[str, object]], scan: dict[str, object],
) -> None:
    """Require exact live role identities to remain blocked in the candidate scope."""
    expected = {str(record["role"]): record for record in expected_roles}
    assert len(expected) == 4
    observed = {
        _process_key(record): record
        for record in scan["cgroup_members"]
    }
    for role, prior in expected.items():
        record = observed.get(_process_key(prior))
        assert record is not None, (role, prior, scan["cgroup_members"])
        assert int(record["ppid"]) == int(prior["ppid"]), (role, prior, record)
        state = str(record["state"])
        assert state.lower() != "r" and state.lower() != "running", (role, record)
        wchan = str(record.get("wchan", "")).strip()
        assert wchan and wchan != "0", (role, record)
        assert any(marker in wchan.lower() for marker in _BLOCKED_WCHAN_MARKERS), (
            role, record,
        )


def _cleanup_failure(primary: BaseException, cleanup: BaseException) -> None:
    """Keep cleanup evidence on, but never replace, the triggering failure."""
    primary.add_note(f"stalled-observation cleanup failure: {cleanup}")


def _fallback_stalled_observation_cleanup(
    ownership: dict[str, object], owned_fds: tuple[int, ...], *,
    runner=subprocess.run, scanner=_root_proc_scan,
) -> tuple[int, ...]:
    """Boundedly remove every captured privileged resource after early observation loss."""
    errors = []
    deadline = time.monotonic() + 20
    unit = str(ownership["unit"])
    cgroup = Path(str(ownership["cgroup"]))
    control_prefix = Path(str(ownership["control_prefix"]))
    namespace = ownership["namespace"]
    coordinator = ownership["coordinator"]
    assert isinstance(namespace, dict) and isinstance(coordinator, dict)
    expected_coordinator = _process_key(coordinator)
    captured_mounts = {
        Path(path) for path in ownership["mount_points"]
        if _canonical_owned_mount_point(str(path), control_prefix)
    }
    holder_records = ownership.get("namespace_holders")
    if holder_records is None:
        holder_records = (ownership["namespace_holder"],)
    captured_holders = tuple(holder_records)
    unit_action_failures = []

    def remaining() -> float:
        return deadline - time.monotonic()

    def command(argv: list[str], purpose: str):
        timeout = min(5, remaining())
        if timeout <= 0:
            errors.append(f"cleanup deadline expired before {purpose}")
            return None
        try:
            return runner(
                argv, check=False, capture_output=True, text=True, timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            errors.append(f"{purpose} timed out")
        except OSError as exc:
            errors.append(f"{purpose} failed: {type(exc).__name__}: {exc}")
        return None

    def scan_owned() -> dict[str, object] | None:
        if remaining() <= 0:
            errors.append("cleanup deadline expired before privileged procfs scan")
            return None
        try:
            return scanner(
                cgroup=cgroup, namespace=namespace,
                targets=tuple(sorted(captured_mounts)), target_prefix=control_prefix,
                watch_pids=(int(coordinator["pid"]),),
            )
        except BaseException as exc:  # pylint: disable=broad-exception-caught
            # Scanner failure is cleanup evidence, not a reason to abandon teardown.
            errors.append(f"privileged procfs scan failed: {type(exc).__name__}: {exc}")
            return None

    for descriptor in owned_fds:
        if descriptor < 0:
            continue
        try:
            os.close(descriptor)
        except OSError as exc:
            if exc.errno != 9:
                errors.append(f"close fd {descriptor} failed: {exc}")

    for action in (
        ["kill", "--kill-whom=all", "--signal=SIGKILL", unit],
        ["stop", unit],
        ["reset-failed", unit],
    ):
        purpose = f"systemctl {action[0]} exact scope"
        before = len(errors)
        completed = command(["sudo", "-n", "systemctl", *action], purpose)
        if len(errors) != before:
            unit_action_failures.extend(errors[before:])
            del errors[before:]
        elif completed is not None and completed.returncode != 0:
            unit_action_failures.append(
                completed.stderr.strip() or f"{purpose} returned {completed.returncode}"
            )

    # Signal only a procfs-confirmed PID/start-time identity; a reused PID is untouchable.
    scan = scan_owned()
    coordinator_present = scan is not None and any(
        _process_key(record) == expected_coordinator for record in scan["watched"]
    )
    if coordinator_present:
        try:
            os.kill(int(coordinator["pid"]), signal.SIGTERM)
        except ProcessLookupError:
            pass
    reap_deadline = min(deadline, time.monotonic() + 5)
    reaped = False
    while time.monotonic() < reap_deadline:
        try:
            waited, _status = os.waitpid(int(coordinator["pid"]), os.WNOHANG)
        except ChildProcessError:
            reaped = True
            break
        if waited == int(coordinator["pid"]):
            reaped = True
            break
        time.sleep(.05)
    if not reaped and coordinator_present:
        try:
            os.kill(int(coordinator["pid"]), signal.SIGKILL)
        except ProcessLookupError:
            pass
        kill_deadline = min(deadline, time.monotonic() + 5)
        while time.monotonic() < kill_deadline:
            try:
                waited, _status = os.waitpid(int(coordinator["pid"]), os.WNOHANG)
            except ChildProcessError:
                reaped = True
                break
            if waited == int(coordinator["pid"]):
                reaped = True
                break
            time.sleep(.05)
    if coordinator_present and not reaped:
        errors.append("captured coordinator could not be reaped before deadline")

    # The scanner sees mounts in the privileged private namespace, including binds/*.
    scan = scan_owned()
    if scan is not None:
        captured_mounts.update(
            _exact_namespace_mounts(
                scan, namespace, control_prefix, tuple(captured_mounts)
            )
        )
    holders = [] if scan is None else [*scan["current_holders"], *scan["fd_holders"]]
    namespace_holder = None if scan is None else _select_captured_namespace_holder(
        scan, captured_holders, namespace,
    )
    if holders and namespace_holder is None:
        errors.append("no live namespace holder matches the complete captured identity")

    def holder_command_payload(operation: str, mount: Path | None = None) -> str:
        assert namespace_holder is not None
        _namespace_entry_path(namespace_holder, namespace)
        nsenter = shutil.which("nsenter") or "/usr/bin/nsenter"
        umount = shutil.which("umount") or "/usr/bin/umount"
        helper_python = str(supervisor._trusted_tools().helper_python)
        return json.dumps({
            "holder": namespace_holder, "namespace": namespace,
            "nsenter": nsenter, "umount": umount, "python": helper_python,
            "operation": operation, "mount": str(mount) if mount else "",
            "scanner": _NAMESPACE_MOUNT_SCANNER_SOURCE,
            "scan_payload": {
                "prefix": str(control_prefix),
                "targets": [str(path) for path in sorted(captured_mounts)],
            },
        }, sort_keys=True)

    def holder_mount_scan() -> tuple[Path, ...] | None:
        if namespace_holder is None:
            return ()
        payload = holder_command_payload("scan")
        completed = command([
            "sudo", "-n", str(supervisor._trusted_tools().helper_python),
            "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE, payload,
        ], "scan exact held mount namespace")
        if completed is None or completed.returncode != 0:
            if completed is not None:
                errors.append(
                    completed.stderr.strip() or "held mount namespace scan failed"
                )
            return None
        try:
            values = json.loads(completed.stdout)
            if not isinstance(values, list) or any(
                not isinstance(value, str) for value in values
            ):
                raise ValueError("mount scan result is not a string list")
            mounts = tuple(Path(value) for value in values if
                           _canonical_owned_mount_point(value, control_prefix))
        except (json.JSONDecodeError, ValueError) as exc:
            errors.append(f"held mount namespace scan was malformed: {exc}")
            return None
        return tuple(sorted(set(mounts)))

    held_mounts = holder_mount_scan()
    if held_mounts is not None:
        captured_mounts.update(held_mounts)
    if ownership.get("require_fd_only_holder") and (
        namespace_holder is None
        or namespace_holder.get("holder_kind") != "fd"
        or scan is None
        or scan["current_holders"]
        or not held_mounts
    ):
        errors.append("exact FD-only namespace mount ownership was not preserved")
    for mount in sorted(
        captured_mounts, key=lambda path: (len(path.parts), str(path)), reverse=True,
    ):
        if namespace_holder is None:
            argv = ["sudo", "-n", "umount", str(mount)]
        else:
            payload = holder_command_payload("unmount", mount)
            argv = [
                "sudo", "-n", str(supervisor._trusted_tools().helper_python),
                "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE, payload,
            ]
        completed = command(argv, f"unmount {mount}")
        if completed is None or completed.returncode == 0:
            continue
        diagnostic = (completed.stderr or completed.stdout).strip().lower()
        if "not mounted" not in diagnostic and "no such file" not in diagnostic:
            errors.append(diagnostic or f"cannot unmount {mount}")

    remaining_held_mounts = holder_mount_scan()
    if remaining_held_mounts:
        errors.append(
            "owned mounts remain in held namespace: "
            + ", ".join(str(path) for path in remaining_held_mounts)
        )

    for holder in ownership.get("external_holders", ()):
        expected = _process_key(holder)
        holder_scan = scanner(watch_pids=(int(holder["pid"]),))
        if any(_process_key(record) == expected for record in holder_scan["watched"]):
            try:
                os.kill(int(holder["pid"]), signal.SIGTERM)
            except ProcessLookupError:
                pass
        holder_deadline = min(deadline, time.monotonic() + 5)
        while time.monotonic() < holder_deadline:
            try:
                waited, _status = os.waitpid(int(holder["pid"]), os.WNOHANG)
            except ChildProcessError:
                break
            if waited == int(holder["pid"]):
                break
            time.sleep(.05)
        else:
            errors.append(f"external namespace holder was not reaped: {expected}")
    for reaper in ownership.get("external_reapers", ()):
        timeout = min(5, remaining())
        try:
            reaper.wait(timeout=max(.01, timeout))
        except subprocess.TimeoutExpired:
            reaper.kill()
            reaper.wait(timeout=max(.01, min(5, remaining())))

    verification_deadline = min(deadline, time.monotonic() + 8)
    final_leaks = ["verification did not run"]
    while time.monotonic() < verification_deadline:
        scan = scan_owned()
        load_state = command(
            ["sudo", "-n", "systemctl", "show", unit,
             "--property=LoadState", "--value"],
            "verify exact scope absent",
        )
        fds_open = []
        for descriptor in owned_fds:
            if descriptor < 0:
                continue
            try:
                os.fstat(descriptor)
            except OSError as exc:
                if exc.errno == 9:
                    continue
                fds_open.append(f"fd={descriptor}: {exc}")
            else:
                fds_open.append(f"fd={descriptor}")
        if scan is None or load_state is None:
            break
        current = {_process_key(record) for record in scan["identities"]}
        coordinator_alive = expected_coordinator in current
        external_alive = [
            _process_key(record) for record in ownership.get("external_holders", ())
            if _process_key(record) in current
        ]
        final_leaks = []
        if (
            load_state.returncode != 0 or load_state.stderr != ""
            or load_state.stdout not in {
                "not-found\n", "loaded\n", "inactive\n", "failed\n",
            }
        ):
            final_leaks.append(
                "malformed-unit-load-state="
                + repr((load_state.returncode, load_state.stdout, load_state.stderr))
            )
            errors.append(final_leaks[-1])
            break
        if not _exact_unit_not_found(load_state):
            final_leaks.append(
                "unit-load-state="
                + repr((load_state.returncode, load_state.stdout, load_state.stderr))
            )
        if scan["cgroup_exists"]:
            final_leaks.append(f"cgroup={cgroup}")
        if coordinator_alive:
            final_leaks.append(f"coordinator={expected_coordinator}")
        if external_alive:
            final_leaks.append(f"external-holders={external_alive}")
        if scan["current_holders"]:
            final_leaks.append("current-namespace-holder")
        if scan["fd_holders"]:
            final_leaks.append("fd-namespace-holder")
        if scan["mount_holders"]:
            final_leaks.append("owned-nested-mount")
        final_leaks.extend(fds_open)
        if not final_leaks:
            break
        time.sleep(.05)
    else:
        errors.append("cleanup verification deadline expired")
    if final_leaks:
        errors.append("cleanup survivors: " + ", ".join(final_leaks))
    if final_leaks and unit_action_failures:
        errors.extend(unit_action_failures)
    if errors:
        raise AssertionError("; ".join(errors))
    return tuple(-1 for _descriptor in owned_fds)


def _run_stalled_observation_setup(scan, assert_watched, failure_cleanup) -> None:
    """Keep early privileged-observation failures inside cleanup ownership."""
    try:
        assert_watched(scan())
    except BaseException as primary:
        try:
            failure_cleanup()
        except BaseException as cleanup:  # pylint: disable=broad-exception-caught
            _cleanup_failure(primary, cleanup)
        raise


def test_root_proc_scanner_source_compiles() -> None:
    """The hosted privileged scanner must remain valid isolated Python."""
    compile(_ROOT_PROC_SCANNER_SOURCE, "<root-proc-scanner>", "exec")
    compile(_NSENTER_REVALIDATOR_SOURCE, "<nsenter-revalidator>", "exec")
    compile(_NAMESPACE_MOUNT_SCANNER_SOURCE, "<namespace-mount-scanner>", "exec")


@pytest.mark.parametrize(
    ("returncode", "stdout", "stderr"),
    (
        (0, "inactive\n", ""), (0, "failed\n", ""), (0, "loaded\n", ""),
        (0, "not-found", ""), (0, "not-found\nextra\n", ""),
        (1, "not-found\n", ""), (0, "not-found\n", "warning"),
    ),
    ids=("inactive", "failed", "loaded", "no-newline", "extra", "status", "stderr"),
)
def test_exact_unit_absence_rejects_noncanonical_load_state(
    returncode: int, stdout: str, stderr: str,
) -> None:
    """Only exact successful LoadState=not-found is unit-absence evidence."""
    completed = SimpleNamespace(
        returncode=returncode, stdout=stdout, stderr=stderr,
    )
    assert not _exact_unit_not_found(completed)


def test_exact_unit_absence_accepts_only_not_found() -> None:
    completed = SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
    assert _exact_unit_not_found(completed)


def test_owned_mount_containment_rejects_sibling_escape_and_malformed() -> None:
    prefix = Path("/tmp/pdd-scope-abc")
    assert _canonical_owned_mount_point("/tmp/pdd-scope-abc/binds/2", prefix)
    assert not _canonical_owned_mount_point("/tmp/pdd-scope-abc-extra/binds/2", prefix)
    for value in (
        "relative/binds/2", "/tmp/pdd-scope-abc/../escape",
        "/tmp/pdd-scope-abc//binds/2", "/tmp/pdd-scope-abc/./binds/2",
    ):
        with pytest.raises(ValueError):
            _canonical_owned_mount_point(value, prefix)


def test_exact_namespace_mounts_excludes_other_namespaces() -> None:
    namespace = {"link": "mnt:[11]", "inode": 11}
    scan = {"mount_holders": [
        {"mount_point": "/tmp/pdd-scope-abc/binds/1",
         "namespace": "mnt:[11]", "namespace_inode": 11},
        {"mount_point": "/tmp/pdd-scope-abc/binds/foreign",
         "namespace": "mnt:[12]", "namespace_inode": 12},
    ]}
    assert _exact_namespace_mounts(
        scan, namespace, Path("/tmp/pdd-scope-abc")
    ) == (Path("/tmp/pdd-scope-abc/binds/1"),)


def test_namespace_holder_selection_rejects_wrong_kind_fd_reuse_and_race() -> None:
    namespace = {"link": "mnt:[11]", "inode": 11}
    captured = {
        "holder_kind": "fd", "pid": 22, "start_time": "100",
        "namespace": "mnt:[1]", "namespace_inode": 1,
        "fd": 7, "fd_path": "/proc/22/fd/7",
        "fd_link": "mnt:[11]", "fd_inode": 11,
    }
    current = captured | {"holder_kind": "current"}
    with pytest.raises(ValueError, match="captured namespace"):
        _namespace_entry_path(current, namespace)
    current = captured | {"holder_kind": "mount", "namespace": "mnt:[11]",
                          "namespace_inode": 11}
    with pytest.raises(ValueError, match="holder kind"):
        _namespace_entry_path(current, namespace)
    wrong_fd = captured | {"namespace": "mnt:[11]", "namespace_inode": 11,
                           "fd_inode": 12}
    with pytest.raises(ValueError, match="descriptor identity"):
        _namespace_entry_path(wrong_fd, namespace)
    with pytest.raises(ValueError, match="descriptor path"):
        _namespace_entry_path(captured | {"fd_path": "/proc/22/fd/8"}, namespace)

    exact = captured | {"namespace": "mnt:[11]", "namespace_inode": 11}
    reused = exact | {"start_time": "101"}
    raced = exact | {"fd": 8}
    assert _select_captured_namespace_holder(
        {"current_holders": [], "fd_holders": [reused]}, (exact,), namespace,
    ) is None
    assert _select_captured_namespace_holder(
        {"current_holders": [], "fd_holders": [raced]}, (exact,), namespace,
    ) is None
    assert _namespace_entry_path(exact, namespace) == "/proc/22/fd/7"


def test_cleanup_process_identity_rejects_pid_reuse() -> None:
    """A reused PID with a different kernel start time is not the recorded process."""
    original = {"pid": 123, "start_time": "100"}
    reused = {"pid": 123, "start_time": "101"}

    assert _process_key(original) != _process_key(reused)


@pytest.mark.parametrize("failure", ("scan", "watched"))
def test_stalled_observation_setup_failure_preserves_primary_and_reaps_owned_state(
    tmp_path: Path, failure: str,
) -> None:
    """The first scan and watched assertion both retain fallback cleanup ownership."""
    read_fd, write_fd = os.pipe()
    coordinator = os.fork()
    if coordinator == 0:
        os.close(read_fd)
        os.close(write_fd)
        signal.pause()
        os._exit(125)
    os.close(write_fd)
    commands = []
    calls = 0

    def runner(*args, **_kwargs):
        commands.append(args[0])
        if args[0][2:4] == ["systemctl", "stop"]:
            return SimpleNamespace(returncode=5, stdout="", stderr="already removed")
        if args[0][2:4] == ["systemctl", "show"]:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    coordinator_record = {"pid": coordinator, "start_time": "unit-test"}

    def scanner(**_kwargs):
        nonlocal calls
        calls += 1
        if calls == 1:
            return {
                "watched": [coordinator_record], "mount_holders": [],
                "current_holders": [], "fd_holders": [], "identities": [],
                "cgroup_exists": False,
            }
        return {
            "watched": [], "mount_holders": [], "current_holders": [],
            "fd_holders": [], "identities": [], "cgroup_exists": False,
        }

    ownership = {
        "unit": "pdd-validator-test.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": tmp_path / "pdd-scope-owned",
        "namespace": {"link": "mnt:[1]", "inode": 1},
        "namespace_holder": {
            "holder_kind": "current", "pid": coordinator,
            "start_time": "unit-test", "namespace": "mnt:[1]",
            "namespace_inode": 1,
        },
        "coordinator": coordinator_record,
        "mount_points": [tmp_path / "pdd-scope-owned" / "binds" / "nested"],
    }

    def scan():
        if failure == "scan":
            raise AssertionError("injected initial scan failure")
        return {"watched": []}

    def assert_watched(scan_result):
        if scan_result["watched"] != ["coordinator"]:
            raise AssertionError("injected initial watched assertion failure")

    with pytest.raises(AssertionError, match="injected initial"):
        _run_stalled_observation_setup(
            scan, assert_watched,
            lambda: _fallback_stalled_observation_cleanup(
                ownership, (read_fd,), runner=runner, scanner=scanner,
            ),
        )

    with pytest.raises(OSError):
        os.fstat(read_fd)
    with pytest.raises(ChildProcessError):
        os.waitpid(coordinator, os.WNOHANG)
    assert commands == [
        ["sudo", "-n", "systemctl", "kill", "--kill-whom=all",
         "--signal=SIGKILL", "pdd-validator-test.scope"],
        ["sudo", "-n", "systemctl", "stop", "pdd-validator-test.scope"],
        ["sudo", "-n", "systemctl", "reset-failed", "pdd-validator-test.scope"],
        ["sudo", "-n", "umount", str(tmp_path / "pdd-scope-owned" / "binds" / "nested")],
        ["sudo", "-n", "systemctl", "show", "pdd-validator-test.scope",
         "--property=LoadState", "--value"],
    ]


def test_stalled_cleanup_load_state_timeout_fails_closed(tmp_path: Path) -> None:
    """A bounded exact-unit probe timeout can never prove cleanup success."""
    coordinator = os.fork()
    if coordinator == 0:
        signal.pause()
        os._exit(125)
    record = {"pid": coordinator, "start_time": "100"}
    calls = 0

    def scanner(**_kwargs):
        nonlocal calls
        calls += 1
        return {
            "watched": [record] if calls == 1 else [], "mount_holders": [],
            "current_holders": [], "fd_holders": [], "identities": [],
            "cgroup_exists": False,
        }

    def runner(argv, **_kwargs):
        if argv[2:4] == ["systemctl", "show"]:
            raise subprocess.TimeoutExpired(argv, 5)
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    ownership = {
        "unit": "pdd-validator-timeout.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": tmp_path / "pdd-scope-owned", "namespace": {
            "link": "mnt:[1]", "inode": 1,
        },
        "namespace_holder": {
            "holder_kind": "current", **record, "namespace": "mnt:[1]",
            "namespace_inode": 1,
        },
        "coordinator": record, "mount_points": [],
    }
    with pytest.raises(AssertionError, match="verify exact scope absent timed out"):
        _fallback_stalled_observation_cleanup(
            ownership, (), runner=runner, scanner=scanner,
        )


def test_exact_blocked_role_snapshot_rejects_running_and_reused_identity() -> None:
    """A running role or PID reuse cannot satisfy blocked-role evidence."""
    roles = [
        {"role": role, "pid": index + 10, "start_time": str(index + 100),
         "ppid": 1 if index == 0 else index + 9}
        for index, role in enumerate(("coordinator", "worker", "browser", "descendant"))
    ]
    members = [
        record | {"state": "S", "wchan": "hrtimer_nanosleep"}
        for record in roles
    ]
    _assert_exact_blocked_role_snapshot(roles, {"cgroup_members": members})

    with pytest.raises(AssertionError):
        _assert_exact_blocked_role_snapshot(
            roles, {"cgroup_members": members[:1] + [
                members[1] | {"state": "R"}, *members[2:]
            ]},
        )
    with pytest.raises(AssertionError):
        _assert_exact_blocked_role_snapshot(
            roles, {"cgroup_members": members[:2] + [
                members[2] | {"start_time": "reused"}, members[3]
            ]},
        )


@pytest.mark.real
@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires hosted Linux privileged descriptor supervision",
)
@pytest.mark.parametrize("case", (
    "normal-hierarchy-environment",
    "parent-exit-before-start",
    "parent-exit-during-execution",
    "parent-exit-after-result",
    "stalled-result-reader",
    "missing-ack",
    "duplicate-ack",
    "trailing-frame",
    "trailing-raw",
    "reordered-extra",
    "stalled-observation-reader",
    "initial-scan-failure",
    "initial-watched-assertion-failure",
    "fd-only-namespace-holder-cleanup",
), ids=(
    "normal-hierarchy-environment",
    "parent-exit-before-start",
    "parent-exit-during-execution",
    "parent-exit-after-result",
    "stalled-result-reader",
    "missing-ack",
    "duplicate-ack",
    "trailing-frame",
    "trailing-raw",
    "reordered-extra",
    "stalled-observation-reader",
    "initial-scan-failure",
    "initial-watched-assertion-failure",
    "fd-only-namespace-holder-cleanup",
))
def test_real_linux_playwright_descriptor_exact_chain(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, case: str,
) -> None:
    """Exercise real descriptor parent-loss, frame, relay, and FD-denial paths."""
    from pdd.sync_core.runner import (  # pylint: disable=import-outside-toplevel
        PlaywrightToolchainRoles,
        _playwright_reporter_source,
        _playwright_snapshot_aggregate_identity,
        _playwright_snapshot_binding_proofs,
    )

    if subprocess.run(["sudo", "-n", "true"], check=False).returncode:
        pytest.fail("hosted descriptor lane requires passwordless sudo")

    toolchain = tmp_path / "descriptor-toolchain"
    dependencies = toolchain / "node_modules"
    entrypoint = dependencies / "@playwright/test/cli.js"
    entrypoint.parent.mkdir(parents=True)
    entrypoint.write_text("cli", encoding="utf-8")
    launcher = toolchain / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    launcher.chmod(0o755)
    browser = toolchain / "browser"
    browser.mkdir()
    lockfile = toolchain / "package-lock.json"
    lockfile.write_text("{}", encoding="utf-8")
    native = toolchain / "native.so"
    native.write_bytes(b"native")
    reporter = toolchain / "reporter.cjs"
    reporter.write_text(_playwright_reporter_source(198), encoding="utf-8")
    roles = PlaywrightToolchainRoles(
        launcher, entrypoint, dependencies, browser, (native,), lockfile
    )
    destination = tmp_path / "phase" / "node_modules"
    proofs = _playwright_snapshot_binding_proofs(
        reporter, roles, launcher, destination, roles.native_bindings
    )
    _identity, aggregate = _playwright_snapshot_aggregate_identity(
        proofs, reporter, roles, launcher, destination, roles.native_bindings
    )

    inventory_program = """import fcntl,json,os
def inventory():
    opened=[]
    for fd in range(256):
        try: fcntl.fcntl(fd,fcntl.F_GETFD)
        except OSError: continue
        opened.append(fd)
    return opened
def emit(role):
    denied=all(fd not in inventory() for fd in (3,4,5,6,7,8))
    payload={'role':role,'fds':inventory(),'denied':denied}
    if role=='coordinator': payload['environment']=dict(os.environ)
    os.write(198,(json.dumps(payload,sort_keys=True)+'\\n').encode('ascii'))
def descend(roles):
    emit(roles[0])
    if len(roles)==1: return
    pid=os.fork()
    if pid==0:
        descend(roles[1:]); os._exit(0)
    waited,status=os.waitpid(pid,0)
    if waited!=pid or status!=0: raise SystemExit(125)
descend(('coordinator','worker','browser','descendant'))
"""
    live_hierarchy_program = """import os,sys,time
roles=('coordinator','worker','browser','descendant')
source=sys.argv[1]
role=sys.argv[2]
index=roles.index(role)
child=None
if index+1<len(roles):
    child=os.fork()
    if child==0:
        next_role=roles[index+1]
        os.execv(sys.executable,[sys.executable,'-I','-S','-c',source,source,next_role])
time.sleep(30)
if child is not None:
    waited,status=os.waitpid(child,0)
    if waited!=child or status!=0: raise SystemExit(125)
"""
    candidate_environment = {
        "HOME": "/tmp/pdd-home",
        "NODE_ENV": "test",
        "NODE_PATH": str(destination),
        "PLAYWRIGHT_BROWSERS_PATH": str(browser),
        "PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1",
        "PYTHONNOUSERSITE": "1",
        "XDG_CACHE_HOME": "/tmp/pdd-home/cache",
        "XDG_CONFIG_HOME": "/tmp/pdd-home/config",
    }

    def launch(program: str, arguments: tuple[str, ...] = ()):
        control = Path(tempfile.mkdtemp(prefix="pdd-descriptor-", dir=tmp_path))
        scratch = control / "scratch"
        scratch.mkdir()
        read_fd, write_fd = os.pipe()
        try:
            argv, plan = _sandbox_command(
                [sys.executable, "-c", program, *arguments], (scratch,), cwd=scratch,
                readable_roots=(reporter, *roles.readable_roots),
                readable_bindings=(*roles.native_bindings, (dependencies, destination)),
                snapshot_binding_proofs=proofs,
                playwright_snapshot_aggregate=aggregate,
                result_write_fd=write_fd, result_fd=198,
                observation_nonce="a" * 64, candidate_timeout=10,
                control_directory=control,
                candidate_environment_values=candidate_environment,
                candidate_temp_directory=Path("/tmp"),
                supervision_token="c" * 32,
            )
        finally:
            os.close(read_fd)
            os.close(write_fd)
        supervisor._prepare_staging(plan)
        process = subprocess.Popen(
            argv, cwd=Path("/"), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, env=supervisor._privileged_helper_environment(),
            start_new_session=True,
        )
        assert process.stdin is not None and process.stdout is not None
        assert plan.launch_payload is not None
        supervisor._write_descriptor_frame_fd(
            process.stdin.fileno(), plan.launch_payload,
            supervisor._DESCRIPTOR_PROTOCOL_MAX_LAUNCH_BYTES,
            time.monotonic() + 30,
        )
        ready = supervisor._read_descriptor_frame_fd(
            process.stdout.fileno(), supervisor._DESCRIPTOR_PROTOCOL_MAX_CONTROL_BYTES,
            time.monotonic() + 30,
        )
        assert ready == {"kind": "ready", "nonce": "a" * 64}
        return control, plan, process

    def send(frame, process) -> None:
        supervisor._write_descriptor_frame_fd(
            process.stdin.fileno(), frame,
            supervisor._DESCRIPTOR_PROTOCOL_MAX_CONTROL_BYTES, time.monotonic() + 5,
        )

    def start(process) -> None:
        send({"kind": "start", "nonce": "a" * 64}, process)

    def read_result(process):
        return supervisor._read_descriptor_frame_fd(
            process.stdout.fileno(), supervisor._DESCRIPTOR_PROTOCOL_MAX_RESULT_BYTES,
            time.monotonic() + 15,
        )

    def ack(result, process) -> dict[str, str]:
        frame = {
            "kind": "ack", "nonce": "a" * 64,
            "digest": hashlib.sha256(
                supervisor._canonical_json(result).encode("utf-8")
            ).hexdigest(),
        }
        send(frame, process)
        return frame

    def scope_control_group(unit: str) -> Path:
        """Read the exact full systemd scope cgroup under a monotonic bound."""
        deadline = time.monotonic() + 10
        last_error = "scope was not observable"
        while time.monotonic() < deadline:
            try:
                completed = subprocess.run(
                    ["sudo", "-n", "systemctl", "show", unit,
                     "--property=ControlGroup", "--value"],
                    capture_output=True, text=True, check=False, timeout=5,
                )
            except subprocess.TimeoutExpired:
                last_error = "systemctl ControlGroup probe timed out"
                continue
            relative = completed.stdout.strip()
            if (
                completed.returncode == 0
                and relative.startswith("/")
                and relative.endswith("/" + unit)
            ):
                cgroup = Path("/sys/fs/cgroup") / relative.lstrip("/")
                if cgroup.is_dir():
                    return cgroup
            last_error = completed.stderr.strip() or relative or last_error
            time.sleep(.05)
        raise AssertionError(f"exact ControlGroup unavailable for {unit}: {last_error}")

    def capture_live_state(
        unit: str, targets: tuple[Path, ...], *,
        target_prefix: Path | None = None, watch_pids: tuple[int, ...] = (),
    ) -> dict[str, object]:
        """Capture exact helper namespace, mounts, and PID/start-time identities."""
        cgroup = scope_control_group(unit)
        deadline = time.monotonic() + 10
        last_scan = None
        while time.monotonic() < deadline:
            scan = _root_proc_scan(
                cgroup=cgroup, targets=targets, target_prefix=target_prefix,
                watch_pids=watch_pids,
            )
            last_scan = scan
            members = scan["cgroup_members"]
            member_keys = {_process_key(record) for record in members}
            root_mount_holders = [
                record for record in scan["mount_holders"]
                if _process_key(record) in member_keys and int(record["uid"]) == 0
            ]
            if members and root_mount_holders:
                holder = root_mount_holders[0]
                namespace = {
                    "link": holder["namespace"],
                    "inode": holder["namespace_inode"],
                }
                exact_scan = _root_proc_scan(
                    cgroup=cgroup, namespace=namespace, targets=targets,
                    target_prefix=target_prefix, watch_pids=watch_pids,
                )
                exact_members = exact_scan["cgroup_members"]
                exact_member_keys = {_process_key(record) for record in exact_members}
                namespace_holders = [
                    *exact_scan["current_holders"], *exact_scan["fd_holders"]
                ]
                if (
                    _process_key(holder) not in exact_member_keys
                    or not namespace_holders
                ):
                    time.sleep(.05)
                    continue
                observed_targets = set(targets)
                if target_prefix is not None:
                    observed_targets.update(_exact_namespace_mounts(
                        exact_scan, namespace, target_prefix, targets,
                    ))
                tracked = {
                    _process_key(record): record
                    for record in (*exact_members, *exact_scan["watched"])
                }
                coordinator_record = next(
                    (record for record in exact_scan["watched"]
                     if int(record["pid"]) in watch_pids),
                    None,
                )
                if coordinator_record is None:
                    time.sleep(.05)
                    continue
                return {
                    "unit": unit,
                    "cgroup": str(cgroup),
                    "targets": [str(path) for path in sorted(observed_targets)],
                    "mount_points": [str(path) for path in sorted(observed_targets)],
                    "control_prefix": str(target_prefix) if target_prefix else "",
                    "namespace": namespace,
                    "namespace_holder": holder,
                    "namespace_holders": namespace_holders,
                    "coordinator": coordinator_record,
                    "recorded_identities": list(tracked.values()),
                }
            time.sleep(.05)
        raise AssertionError(
            "privileged helper namespace was not observable: "
            + json.dumps(last_scan, sort_keys=True)
        )

    def await_live_role_identities(details: dict[str, object]) -> None:
        """Bind all four live roles to exact procfs identities and ancestry."""
        expected_roles = ("coordinator", "worker", "browser", "descendant")
        candidate = Path(str(details["cgroup"])) / "candidate"
        deadline = time.monotonic() + 10
        last_records = []
        while time.monotonic() < deadline:
            scan = _root_proc_scan(cgroup=candidate)
            records = []
            for record in scan["cgroup_members"]:
                command = record.get("cmdline", [])
                if (
                    len(command) >= 3
                    and command[-3] == live_hierarchy_program
                    and command[-2] == live_hierarchy_program
                    and command[-1] in expected_roles
                ):
                    records.append(record)
            last_records = records
            by_role = {
                record["cmdline"][-1]: record | {"role": record["cmdline"][-1]}
                for record in records
            }
            if len(records) == 4 and set(by_role) == set(expected_roles):
                for parent_role, child_role in zip(expected_roles, expected_roles[1:]):
                    assert int(by_role[child_role]["ppid"]) == int(
                        by_role[parent_role]["pid"]
                    ), (parent_role, child_role, by_role)
                details["role_identities"] = [by_role[role] for role in expected_roles]
                tracked = {
                    _process_key(record): record
                    for record in details["recorded_identities"]
                }
                tracked.update({_process_key(record): record for record in records})
                details["recorded_identities"] = list(tracked.values())
                return
            time.sleep(.05)
        raise AssertionError(
            "exact blocked four-role hierarchy was not observable: "
            + json.dumps(last_records, sort_keys=True)
        )

    def await_same_blocked_role_identities(details: dict[str, object]) -> None:
        """Re-observe the recorded roles as blocked candidates before parent loss."""
        candidate = Path(str(details["cgroup"])) / "candidate"
        deadline = time.monotonic() + 10
        last_scan = None
        while time.monotonic() < deadline:
            scan = _root_proc_scan(cgroup=candidate)
            last_scan = scan
            try:
                _assert_exact_blocked_role_snapshot(details["role_identities"], scan)
                return
            except AssertionError:
                time.sleep(.05)
        raise AssertionError(
            "exact role identities were not blocked before parent exit: "
            + json.dumps(last_scan, sort_keys=True)
        )

    def leak_state(details: dict[str, object]) -> list[str]:
        """Return only exact identity, namespace, mount, and cgroup survivors."""
        scan = _root_proc_scan(
            cgroup=Path(str(details["cgroup"])),
            namespace=details["namespace"],
            targets=tuple(Path(path) for path in details["targets"]),
            target_prefix=(
                Path(str(details["control_prefix"]))
                if details.get("control_prefix") else None
            ),
        )
        leaks = []
        if scan["cgroup_exists"]:
            leaks.append(f"cgroup={details['cgroup']}")
        current = {_process_key(record) for record in scan["identities"]}
        survivors = [
            record for record in details["recorded_identities"]
            if _process_key(record) in current
        ]
        if survivors:
            leaks.append("identities=" + json.dumps(survivors, sort_keys=True))
        if scan["current_holders"]:
            leaks.append(
                "current-namespace-holders="
                + json.dumps(scan["current_holders"], sort_keys=True)
            )
        if scan["fd_holders"]:
            leaks.append(
                "fd-namespace-holders="
                + json.dumps(scan["fd_holders"], sort_keys=True)
            )
        if scan["mount_holders"]:
            leaks.append("mounts=" + json.dumps(scan["mount_holders"], sort_keys=True))
        return leaks

    def await_automatic_cleanup(details: dict[str, object]) -> None:
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline:
            if not leak_state(details):
                return
            time.sleep(.05)
        assert not leak_state(details), (
            "automatic cleanup deadline expired: " + "; ".join(leak_state(details))
        )

    def emergency_cleanup(
        details: dict[str, object], pid: int | None = None, *,
        process_group: bool = True,
    ) -> None:
        if pid is not None:
            expected = next(
                (record for record in details["recorded_identities"]
                 if int(record["pid"]) == pid),
                None,
            )
            scan = _root_proc_scan(watch_pids=(pid,))
            if expected is not None and any(
                _process_key(record) == _process_key(expected)
                for record in scan["watched"]
            ):
                try:
                    if process_group:
                        os.killpg(pid, signal.SIGKILL)
                    else:
                        os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        subprocess.run(
            ["sudo", "-n", "systemctl", "stop", str(details["unit"])], check=False,
            capture_output=True, text=True,
        )
        for target in reversed(tuple(Path(path) for path in details["targets"])):
            subprocess.run(
                ["sudo", "-n", "umount", str(target)], check=False,
                capture_output=True, text=True,
            )

    def assert_case_cleanup(control, details, process, should_succeed: bool) -> None:
        try:
            returncode = process.wait(timeout=20)
            assert (returncode == 0) is should_succeed
            await_automatic_cleanup(details)
        except BaseException:
            emergency_cleanup(details, process.pid)
            raise
        finally:
            shutil.rmtree(control, ignore_errors=True)

    if case.startswith("parent-exit-"):
        report = tmp_path / f"{case}.json"
        coordinator = os.fork()
        if coordinator == 0:
            program = (
                live_hierarchy_program
                if case == "parent-exit-during-execution"
                else inventory_program
            )
            arguments = (
                (live_hierarchy_program, "coordinator")
                if case == "parent-exit-during-execution"
                else ()
            )
            control, plan, process = launch(program, arguments)
            details = capture_live_state(
                plan.unit_name, plan.staging_targets, watch_pids=(process.pid,)
            )
            if case != "parent-exit-before-start":
                start(process)
            if case == "parent-exit-during-execution":
                await_live_role_identities(details)
                await_same_blocked_role_identities(details)
            elif case == "parent-exit-after-result":
                read_result(process)
            details["pid"] = process.pid
            details["control"] = str(control)
            report.write_text(json.dumps(details), encoding="utf-8")
            os._exit(0)
        waited, status = os.waitpid(coordinator, 0)
        assert waited == coordinator and status == 0
        details = json.loads(report.read_text(encoding="utf-8"))
        try:
            await_automatic_cleanup(details)
        except BaseException:
            emergency_cleanup(details, details["pid"])
            raise
        finally:
            shutil.rmtree(details["control"], ignore_errors=True)
        return

    if case in {
        "stalled-observation-reader", "initial-scan-failure",
        "initial-watched-assertion-failure", "fd-only-namespace-holder-cleanup",
    }:
        unit = "pdd-validator-" + "e" * 32 + ".scope"
        token = "c" * 32
        monkeypatch.setattr(supervisor, "_scope_unit_name", lambda: unit)
        monkeypatch.setattr(
            supervisor.uuid, "uuid4", lambda: SimpleNamespace(hex=token)
        )
        monkeypatch.setattr(supervisor.tempfile, "tempdir", str(tmp_path))
        read_fd, write_fd = os.pipe()
        report = tmp_path / "stalled-observation-reader.json"
        program = (
            "import os;data=b'x'*262144;offset=0\n"
            "while offset<len(data): offset+=os.write(198,data[offset:])"
        )
        coordinator = os.fork()
        if coordinator == 0:
            os.close(read_fd)
            exit_status = 0
            try:
                result, surviving = run_supervised(
                    [sys.executable, "-c", program], cwd=tmp_path, timeout=10,
                    env=candidate_environment, writable_roots=(tmp_path,),
                    readable_roots=(reporter, *roles.readable_roots),
                    readable_bindings=(
                        *roles.native_bindings, (dependencies, destination)
                    ),
                    snapshot_binding_proofs=proofs,
                    playwright_snapshot_aggregate=aggregate,
                    result_write_fd=write_fd, result_fd=198,
                    temp_directory=Path("/tmp"),
                )
                report.write_text(json.dumps({
                    "kind": result.termination.kind.value,
                    "stderr": result.stderr,
                    "surviving": surviving,
                }), encoding="utf-8")
            except BaseException as error:  # pylint: disable=broad-exception-caught
                exit_status = 125
                report.write_text(json.dumps({
                    "error": f"{type(error).__name__}: {error}",
                }), encoding="utf-8")
            finally:
                os.close(write_fd)
            os._exit(exit_status)
        os.close(write_fd)
        write_fd = -1
        details = None
        fallback_done = False
        external_reaper = None
        try:
            def exact_control_prefix() -> Path:
                deadline = time.monotonic() + 10
                while time.monotonic() < deadline:
                    controls = tuple(
                        path for path in tmp_path.glob("pdd-scope-*") if path.is_dir()
                    )
                    if len(controls) == 1:
                        return controls[0]
                    time.sleep(.05)
                raise AssertionError("exact stalled-observation control directory unavailable")

            def assert_initial_coordinator(scan: dict[str, object]) -> None:
                assert len(scan["watched"]) == 1
                if case == "initial-watched-assertion-failure":
                    raise AssertionError("injected initial watched assertion failure")

            def initial_scan() -> dict[str, object]:
                scan = _root_proc_scan(watch_pids=(coordinator,))
                if case == "initial-scan-failure":
                    raise AssertionError("injected initial scan failure")
                return scan

            def early_failure_cleanup() -> None:
                nonlocal details, read_fd, write_fd, fallback_done
                control_prefix = exact_control_prefix()
                details = capture_live_state(
                    unit, (), target_prefix=control_prefix,
                    watch_pids=(coordinator,),
                )
                assert all(
                    Path(path).is_relative_to(control_prefix)
                    for path in details["mount_points"]
                )
                assert any(
                    len(Path(path).relative_to(control_prefix).parts) > 1
                    for path in details["mount_points"]
                ), "hosted injection requires a real nested control mount"
                try:
                    read_fd, write_fd = _fallback_stalled_observation_cleanup(
                        details, (read_fd, write_fd),
                    )
                finally:
                    fallback_done = True

            if case in {"initial-scan-failure", "initial-watched-assertion-failure"}:
                with pytest.raises(AssertionError, match="injected initial"):
                    _run_stalled_observation_setup(
                        initial_scan, assert_initial_coordinator, early_failure_cleanup,
                    )
                assert fallback_done and details is not None
                assert read_fd == -1 and write_fd == -1
                return

            _run_stalled_observation_setup(
                initial_scan, assert_initial_coordinator, early_failure_cleanup,
            )
            details = capture_live_state(
                unit, (), target_prefix=exact_control_prefix(),
                watch_pids=(coordinator,),
            )
            if case == "fd-only-namespace-holder-cleanup":
                holder_source = r"""
import json,os,signal,sys
target=int(sys.argv[1])
descriptor=os.open(f'/proc/{target}/ns/mnt',os.O_RDONLY|os.O_CLOEXEC)
raw=open(f'/proc/{os.getpid()}/stat',encoding='ascii').read()
fields=raw[raw.rfind(')')+2:].split()
print(json.dumps({'pid':os.getpid(),'start_time':fields[19],
                  'fd':descriptor}),flush=True)
signal.pause()
"""
                external_reaper = subprocess.Popen(
                    [
                        "sudo", "-n", str(supervisor._trusted_tools().helper_python),
                        "-I", "-S", "-c", holder_source,
                        str(details["namespace_holder"]["pid"]),
                    ],
                    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, text=True,
                )
                assert external_reaper.stdout is not None
                ready, _, _ = select.select(
                    [external_reaper.stdout.fileno()], [], [], 5,
                )
                assert ready, "external namespace-FD holder did not become ready"
                holder_ready = json.loads(external_reaper.stdout.readline())
                details["external_holders"] = [holder_ready]
                details["external_reapers"] = [external_reaper]
                holder_deadline = time.monotonic() + 8
                holder_record = None
                while time.monotonic() < holder_deadline:
                    holder_scan = _root_proc_scan(
                        namespace=details["namespace"],
                        targets=tuple(Path(path) for path in details["mount_points"]),
                        target_prefix=Path(str(details["control_prefix"])),
                        watch_pids=(int(holder_ready["pid"]),),
                    )
                    holder_record = next((
                        record for record in holder_scan["fd_holders"]
                        if int(record["pid"]) == int(holder_ready["pid"])
                        and int(record["fd"]) == int(holder_ready["fd"])
                        and _process_key(record) == _process_key(holder_ready)
                    ), None)
                    if holder_record is not None:
                        assert not any(
                            int(record["pid"]) == int(holder_ready["pid"])
                            for record in holder_scan["current_holders"]
                        )
                        break
                    time.sleep(.05)
                assert holder_record is not None, "exact namespace-FD holder unavailable"
                details["namespace_holders"].append(holder_record)
                details["require_fd_only_holder"] = True
                read_fd, write_fd = _fallback_stalled_observation_cleanup(
                    details, (read_fd, write_fd),
                )
                fallback_done = True
                assert external_reaper.poll() is not None
                assert read_fd == -1 and write_fd == -1
                return
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline:
                waited, status = os.waitpid(coordinator, os.WNOHANG)
                if waited == coordinator:
                    assert status == 0
                    break
                time.sleep(.05)
            else:
                raise AssertionError("stalled observation coordinator did not exit")
            await_automatic_cleanup(details)
            outcome = json.loads(report.read_text(encoding="utf-8"))
            assert outcome["kind"] == supervisor.TerminationKind.SANDBOX_ERROR.value
            assert "timed out" in outcome["stderr"]
            assert outcome["surviving"] is False
        except BaseException as primary:
            if not fallback_done:
                try:
                    if details is None:
                        details = capture_live_state(
                            unit, (), target_prefix=exact_control_prefix(),
                            watch_pids=(coordinator,),
                        )
                    read_fd, write_fd = _fallback_stalled_observation_cleanup(
                        details, (read_fd, write_fd),
                    )
                except BaseException as cleanup:
                    _cleanup_failure(primary, cleanup)
                finally:
                    fallback_done = True
            raise
        finally:
            if read_fd >= 0:
                os.close(read_fd)
            if write_fd >= 0:
                os.close(write_fd)
            try:
                os.waitpid(coordinator, os.WNOHANG)
            except ChildProcessError:
                pass
            if external_reaper is not None and external_reaper.poll() is None:
                external_reaper.terminate()
                try:
                    external_reaper.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    external_reaper.kill()
                    external_reaper.wait(timeout=5)
        return

    program = inventory_program
    if case == "stalled-result-reader":
        program = "import os;os.write(1,b'x'*1048576);os.write(198,b'{}')"
    control, plan, process = launch(program)
    details = capture_live_state(
        plan.unit_name, plan.staging_targets, watch_pids=(process.pid,)
    )
    should_succeed = case == "normal-hierarchy-environment"
    try:
        if case == "reordered-extra":
            send({"kind": "ack", "nonce": "a" * 64, "digest": "0" * 64}, process)
            process.stdin.close()
        else:
            start(process)
            if case == "stalled-result-reader":
                pass
            elif case == "stalled-observation-reader":
                pass
            else:
                result = read_result(process)
                if case == "normal-hierarchy-environment":
                    parsed = supervisor._descriptor_result(
                        result, "a" * 64, aggregate.digest, 16 * 1024
                    )
                    rows = [json.loads(row) for row in parsed.observation.splitlines()]
                    assert [row["role"] for row in rows] == [
                        "coordinator", "worker", "browser", "descendant"
                    ]
                    assert all(row["fds"] == [0, 1, 2, 198] for row in rows)
                    assert all(row["denied"] for row in rows)
                    environment = rows[0]["environment"]
                    expected_environment = supervisor._parse_candidate_environment_record(
                        supervisor._candidate_environment_record(
                            candidate_environment,
                            temp_directory=Path("/tmp"),
                            supervision_token="c" * 32,
                        )
                    )
                    assert environment == expected_environment
                    ack(result, process)
                    process.stdin.close()
                elif case == "missing-ack":
                    process.stdin.close()
                elif case == "duplicate-ack":
                    frame = ack(result, process)
                    send(frame, process)
                    process.stdin.close()
                elif case == "trailing-frame":
                    ack(result, process)
                    send({"kind": "extra", "nonce": "a" * 64}, process)
                    process.stdin.close()
                elif case == "trailing-raw":
                    ack(result, process)
                    os.write(process.stdin.fileno(), b"x")
                    process.stdin.close()
        assert_case_cleanup(control, details, process, should_succeed)
    except BaseException:
        if process.poll() is None:
            emergency_cleanup(details, process.pid)
        raise


@pytest.mark.skipif(not shutil.which("bwrap"), reason="requires Linux bubblewrap")
def test_simultaneous_high_volume_stdio_has_one_aggregate_bound(tmp_path: Path) -> None:
    """Concurrent stdout/stderr drains share one synchronized byte budget."""
    program = (
        "import os,threading\n"
        "def emit(fd):\n"
        " [os.write(fd,b'x'*65536) for _ in range(6)]\n"
        "threads=[threading.Thread(target=emit,args=(fd,)) for fd in (1,2)]\n"
        "[thread.start() for thread in threads]\n"
        "[thread.join() for thread in threads]\n"
    )
    result, surviving = run_supervised(
        [sys.executable, "-c", program], cwd=tmp_path, timeout=10,
        env=dict(os.environ), writable_roots=(tmp_path,),
        limits=replace(SupervisorLimits(), max_output_bytes=1024 * 1024),
    )
    assert result.returncode == 0
    assert len(result.stdout.encode()) + len(result.stderr.encode()) == 12 * 65536
    assert surviving is False


def test_live_processes_rejects_reused_pid_identity(monkeypatch) -> None:
    monkeypatch.setattr("pdd.sync_core.supervisor._process_identity", lambda _pid: "new")
    monkeypatch.setattr(os, "kill", lambda *_args: None)
    assert _live_processes({123: "old"}) == set()


@pytest.mark.parametrize("frame", [
    b"", b"\x00\x00\x00\x08{}", b"\x00\x00\x20\x00{}",
    b"\x00\x00\x00\x02[]",
])
def test_descriptor_transport_rejects_partial_malformed_and_oversized_frames(
    frame: bytes,
) -> None:
    """Descriptor authority accepts one exact canonical object frame only."""
    with pytest.raises(RuntimeError, match="descriptor"):
        supervisor._read_descriptor_frame(io.BytesIO(frame), 16)


def test_descriptor_transport_rejects_duplicate_and_trailing_terminal_frames() -> None:
    """The finite-state transport stores one frame and requires terminal EOF."""
    read_fd, write_fd = os.pipe()
    try:
        os.write(write_fd, supervisor._descriptor_frame(
            {"kind": "ready", "nonce": "a" * 64}, 4096,
        ))
        os.write(write_fd, supervisor._descriptor_frame(
            {"kind": "ready", "nonce": "a" * 64}, 4096,
        ))
        os.close(write_fd)
        write_fd = -1
        first = supervisor._read_descriptor_frame_fd(
            read_fd, 4096, time.monotonic() + 1,
        )
        duplicate = supervisor._read_descriptor_frame_fd(
            read_fd, 4096, time.monotonic() + 1,
        )
        assert first == duplicate
        with pytest.raises(RuntimeError, match="descriptor result"):
            supervisor._descriptor_result(duplicate, "a" * 64, "b" * 64, 1024)
    finally:
        os.close(read_fd)
        if write_fd >= 0:
            os.close(write_fd)

    read_fd, write_fd = os.pipe()
    try:
        os.write(write_fd, b"trailing")
        os.close(write_fd)
        write_fd = -1
        with pytest.raises(RuntimeError, match="trailing data"):
            supervisor._expect_descriptor_eof(read_fd, time.monotonic() + 1)
    finally:
        os.close(read_fd)
        if write_fd >= 0:
            os.close(write_fd)


def test_descriptor_control_read_has_monotonic_deadline() -> None:
    """A parent/helper stall cannot leave descriptor control blocked forever."""
    read_fd, write_fd = os.pipe()
    try:
        started = time.monotonic()
        with pytest.raises(RuntimeError, match="timed out"):
            supervisor._read_descriptor_frame_fd(
                read_fd, 4096, time.monotonic() + 0.02,
            )
        assert time.monotonic() - started < 0.5
    finally:
        os.close(read_fd)
        os.close(write_fd)


@pytest.mark.parametrize("payload", [
    None, [], {}, {"version": 1},
    {"version": 1, "state": "terminal", "returncode": 0},
    {"version": 1, "state": "terminal", "returncode": 0,
     "timed_out": False, "extra": True},
    {"version": 1, "state": "terminal", "returncode": True,
     "timed_out": False},
])
def test_candidate_record_parser_fails_closed_for_every_malformed_shape(
    payload: object,
) -> None:
    """Nested candidate status has one exact key and type grammar."""
    with pytest.raises(RuntimeError, match="candidate record"):
        supervisor._load_candidate_record_payload(payload)


@pytest.mark.parametrize(
    ("program", "expected"),
    [
        ("raise SystemExit(17)", 17),
        ("import os,signal;os.kill(os.getpid(),signal.SIGTERM)", -signal.SIGTERM),
    ],
)
def test_inner_status_supervisor_authenticates_nested_returncode(
    tmp_path: Path, program: str, expected: int,
) -> None:
    """The exact production inner supervisor reports exit and signal status."""
    token = "a" * 32
    cgroup = tmp_path / "candidate-cgroup"
    cgroup.mkdir()
    (cgroup / "cgroup.procs").touch()
    read_fd, write_fd = os.pipe()
    try:
        completed = subprocess.run(
            [sys.executable, "-I", "-S", "-c",
             supervisor._INNER_STATUS_SUPERVISOR_SOURCE, str(write_fd), token,
             str(cgroup), sys.executable, "-c", program],
            pass_fds=(write_fd,), check=False, timeout=5,
        )
        os.close(write_fd)
        write_fd = -1
        record = os.read(read_fd, supervisor._TERMINATION_HEADER_BYTES)
    finally:
        os.close(read_fd)
        if write_fd >= 0:
            os.close(write_fd)
    assert len(record) == supervisor._TERMINATION_HEADER_BYTES
    assert record.startswith(supervisor._TERMINATION_HEADER_PREFIX)
    payload = json.loads(record[len(supervisor._TERMINATION_HEADER_PREFIX):].rstrip())
    assert payload == {"returncode": expected, "token": token}
    assert completed.returncode == (expected if expected >= 0 else 128 - expected)


def test_inner_status_supervisor_moves_only_candidate_to_cgroup(
    tmp_path: Path,
) -> None:
    """Only the forked untrusted child consumes the candidate pids budget."""
    cgroup = tmp_path / "candidate-cgroup"
    cgroup.mkdir()
    membership = cgroup / "cgroup.procs"
    membership.touch()
    candidate_pid = tmp_path / "candidate-pid"
    token = "a" * 32
    read_fd, write_fd = os.pipe()
    program = (
        "from pathlib import Path;import os,sys;"
        "Path(sys.argv[1]).write_text(str(os.getpid()),encoding='ascii')"
    )
    try:
        completed = subprocess.run(
            [
                sys.executable, "-I", "-S", "-c",
                supervisor._INNER_STATUS_SUPERVISOR_SOURCE, str(write_fd), token,
                str(cgroup), sys.executable, "-c", program, str(candidate_pid),
            ],
            pass_fds=(write_fd,), check=False, timeout=5,
        )
        os.close(write_fd)
        write_fd = -1
        record = os.read(read_fd, supervisor._TERMINATION_HEADER_BYTES)
    finally:
        os.close(read_fd)
        if write_fd >= 0:
            os.close(write_fd)

    payload = json.loads(record[len(supervisor._TERMINATION_HEADER_PREFIX):].rstrip())
    assert completed.returncode == 0
    assert payload == {"returncode": 0, "token": token}
    assert membership.read_text(encoding="ascii") == candidate_pid.read_text(encoding="ascii")


def test_descriptor_result_rejects_replayed_nonce_and_aggregate() -> None:
    """A result from another helper lifecycle cannot be replayed as a PASS."""
    observation = b'{"tests":[]}'
    payload = {
        "kind": "result", "nonce": "a" * 64, "aggregate_digest": "b" * 64,
        "candidate": {"version": 1, "state": "terminal", "returncode": 0, "timed_out": False},
        "stdout": base64.b64encode(b"").decode(), "stderr": base64.b64encode(b"").decode(),
        "observation": base64.b64encode(observation).decode(),
        "observation_sha256": hashlib.sha256(observation).hexdigest(),
        "observation_size": len(observation),
    }
    with pytest.raises(RuntimeError, match="descriptor result"):
        supervisor._descriptor_result(payload, "c" * 64, "b" * 64, 1024)
    with pytest.raises(RuntimeError, match="descriptor result"):
        supervisor._descriptor_result(payload, "a" * 64, "d" * 64, 1024)


def test_playwright_descriptor_helper_denies_candidate_control_descriptors() -> None:
    """The aggregate branch replaces all candidate stdio before exec."""
    source = inspect.getsource(supervisor._staged_bwrap)
    assert "os.dup2(null,0)" in source
    assert "os.dup2(candidate_stdout_write,1)" in source
    assert "os.dup2(candidate_stderr_write,2)" in source
    assert "POLLHUP|select.POLLERR" in source
    assert "os.set_blocking(protocol_out_fd,False)" in source
    assert "protected descriptor write timed out" in source
    assert "protocol_expect_eof(time.monotonic()+limits['trusted_timeout'])" in source
    assert source.index("protocol_send(payload,limits['protocol']") < source.index(
        "parent_watch_done.set()"
    )
    assert "protocol_receive(4096,time.monotonic()+limits['trusted_timeout'])" in source


def test_playwright_descriptor_transport_timeout_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A helper that sends READY but never a result cannot leave a passing state."""
    cgroup = tmp_path / "cgroup"
    cgroup.mkdir()
    (cgroup / "memory.events").write_text("oom 0\noom_kill 0\n", encoding="ascii")
    (cgroup / "pids.events").write_text("max 0\n", encoding="ascii")
    helper = (
        "import json,sys,time;"
        "payload=json.dumps({'kind':'ready','nonce':'aa'*32},sort_keys=True,"
        "separators=(',',':')).encode();"
        "sys.stdout.buffer.write(len(payload).to_bytes(4,'big')+payload);"
        "sys.stdout.buffer.flush();"
        "sys.stdin.buffer.read(4096);time.sleep(30)"
    )

    def sandbox(_command, _roots, **_kwargs):
        return [sys.executable, "-c", helper], SimpleNamespace(
            unit_name="pdd-validator-00000000000000000000000000000000.scope",
            tools=SimpleNamespace(),
            launch_payload={},
        )

    monkeypatch.setattr(supervisor, "_sandbox_command", sandbox)
    monkeypatch.setattr(supervisor, "_prepare_staging", lambda _plan: None)
    monkeypatch.setattr(
        supervisor, "_probe_scope",
        lambda _plan, _limits: (cgroup, {"oom": 0, "oom_kill": 0}, {"max": 0}),
    )
    monkeypatch.setattr(supervisor, "_stop_scope", lambda *_args: None)
    monkeypatch.setattr(supervisor, "_cleanup_staging", lambda _plan: None)
    monkeypatch.setattr(supervisor, "_TRUSTED_POSTPROCESS_SECONDS", .02)
    monkeypatch.setattr(supervisor.os, "urandom", lambda size: b"\xaa" * size)
    read_fd, write_fd = os.pipe()
    try:
        result, surviving = supervisor._run_playwright_descriptor_supervised(
            [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=.01, env={},
            writable_roots=(tmp_path,), limits=SupervisorLimits(), readable_roots=(),
            readable_bindings=(), immutable_binding_proofs=(), snapshot_binding_proofs=(),
            playwright_snapshot_aggregate=supervisor.PlaywrightSnapshotAggregate(
                "{}", "b" * 64, "identity", 198,
            ), writable_bindings=(), temp_directory=None,
            result_write_fd=write_fd, result_fd=198,
        )
    finally:
        os.close(read_fd)
        os.close(write_fd)
    assert result.returncode == 125
    assert result.termination.kind is supervisor.TerminationKind.SANDBOX_ERROR
    assert "descriptor transport timed out" in result.stderr
    assert surviving is False


def test_playwright_descriptor_records_events_before_helper_cleanup(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Authenticated event deltas remain readable until result handoff is acknowledged."""
    cgroup = tmp_path / "cgroup"
    cgroup.mkdir()
    memory_events = cgroup / "memory.events"
    pids_events = cgroup / "pids.events"
    memory_events.write_text("oom 0\noom_kill 0\n", encoding="ascii")
    pids_events.write_text("max 0\n", encoding="ascii")
    helper = """
import hashlib,json,os,sys
def receive():
    size=int.from_bytes(sys.stdin.buffer.read(4),'big')
    return json.loads(sys.stdin.buffer.read(size))
def send(value):
    payload=json.dumps(value,sort_keys=True,separators=(',',':')).encode()
    sys.stdout.buffer.write(len(payload).to_bytes(4,'big')+payload);sys.stdout.buffer.flush()
receive()
nonce='aa'*32
send({'kind':'ready','nonce':nonce})
receive()
observation=b''
send({'kind':'result','nonce':nonce,'aggregate_digest':'b'*64,
      'candidate':{'version':1,'state':'terminal','returncode':0,'timed_out':False},
      'stdout':'','stderr':'','observation':'',
      'observation_sha256':hashlib.sha256(observation).hexdigest(),
      'observation_size':0})
receive()
os.unlink(sys.argv[1]);os.unlink(sys.argv[2])
"""

    def sandbox(_command, _roots, **_kwargs):
        return [sys.executable, "-c", helper, str(memory_events), str(pids_events)], SimpleNamespace(
            unit_name="pdd-validator-00000000000000000000000000000000.scope",
            tools=SimpleNamespace(), launch_payload={},
        )

    monkeypatch.setattr(supervisor, "_sandbox_command", sandbox)
    monkeypatch.setattr(supervisor, "_prepare_staging", lambda _plan: None)
    monkeypatch.setattr(
        supervisor, "_probe_scope",
        lambda _plan, _limits: (cgroup, {"oom": 0, "oom_kill": 0}, {"max": 0}),
    )
    monkeypatch.setattr(supervisor, "_stop_scope", lambda *_args: None)
    monkeypatch.setattr(supervisor, "_cleanup_staging", lambda _plan: None)
    monkeypatch.setattr(supervisor.os, "urandom", lambda size: b"\xaa" * size)
    read_fd, write_fd = os.pipe()
    try:
        result, surviving = supervisor._run_playwright_descriptor_supervised(
            [sys.executable, "-c", "pass"], cwd=tmp_path, timeout=1, env={},
            writable_roots=(tmp_path,), limits=SupervisorLimits(), readable_roots=(),
            readable_bindings=(), immutable_binding_proofs=(), snapshot_binding_proofs=(),
            playwright_snapshot_aggregate=supervisor.PlaywrightSnapshotAggregate(
                "{}", "b" * 64, "identity", 198,
            ), writable_bindings=(), temp_directory=None,
            result_write_fd=write_fd, result_fd=198,
        )
    finally:
        os.close(read_fd)
        os.close(write_fd)

    assert result.returncode == 0, result.stderr
    assert result.termination.kind is supervisor.TerminationKind.EXIT
    assert surviving is False


@pytest.mark.skipif(not shutil.which("bwrap"), reason="requires Linux bubblewrap")
def test_writable_churn_cannot_escape_supervisor_cleanup(tmp_path: Path) -> None:
    program = (
        "import pathlib, threading, time\n"
        "root=pathlib.Path('.')\n"
        "def churn():\n"
        "  while True:\n"
        "    p=root/'churn'; p.write_bytes(b'x'); p.unlink(missing_ok=True)\n"
        "threading.Thread(target=churn, daemon=True).start(); time.sleep(.5)\n"
    )
    result, surviving = run_supervised(
        [sys.executable, "-c", program], cwd=tmp_path, timeout=5,
        env=dict(os.environ), writable_roots=(tmp_path,),
    )
    assert result.returncode == 0
    assert surviving is False
    assert not (tmp_path / "churn").exists()
