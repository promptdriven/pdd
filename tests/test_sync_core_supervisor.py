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
import threading
import time
from dataclasses import dataclass, replace
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


def _credential_free_environment(home: Path) -> dict[str, str]:
    """Return a fixed candidate environment independent of hosted CI secrets."""
    return {"HOME": str(home), "NODE_ENV": "test"}


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
        "LANG": "C", "LC_ALL": "C",
        "LD_LIBRARY_PATH": supervisor._sandbox_library_path(environment),
        "PATH": supervisor._TRUSTED_ROOT_PATH,
        "PDD_SUPERVISION_TOKEN": "a" * 32,
        "PYTHONDONTWRITEBYTECODE": "1",
        "TEMP": "/tmp", "TMP": "/tmp", "TMPDIR": "/tmp",
    }
    assert list(parsed) == sorted(parsed)


def test_supervision_token_generation_is_independent_of_staging_identifiers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A deterministic authority token cannot collapse bind-staging identities."""
    monkeypatch.setattr(
        supervisor.uuid, "uuid4", lambda: SimpleNamespace(hex="d" * 32)
    )
    monkeypatch.setattr(supervisor.os, "urandom", lambda size: b"\xaa" * size)

    assert supervisor._fresh_supervision_token() == "aa" * 16


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
    assert {"--unshare-pid", "--unshare-net"} <= set(bwrap)
    assert "--unshare-cgroup" not in bwrap
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
    assert supervisor.InfrastructureFailurePhase.SCOPE_CLEANUP in (
        result.termination.failure_phases
    )


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
        env=_credential_free_environment(tmp_path),
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
    fork_offset = helper.index("pid=os.fork()")
    assert fork_offset < helper.index("observation_thread.start()")
    assert fork_offset < helper.index("[thread.start() for thread in candidate_output_threads]")
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
        env=_credential_free_environment(tmp_path), writable_roots=(tmp_path,), limits=limits,
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


@pytest.mark.parametrize(
    "phase",
    [
        "construction",
        "launch",
        "scope-setup",
        "candidate-execution",
        "trusted-postprocessing",
        "result-handoff",
        "scope-cleanup",
        "mount-cleanup",
        "output-drain",
        "process-cleanup",
    ],
)
def test_sandbox_termination_preserves_only_allowlisted_failure_phases(
    phase: str,
) -> None:
    """Candidate prose cannot manufacture a trusted infrastructure phase."""
    trusted = supervisor.InfrastructureFailurePhase(phase)

    termination = supervisor._sandbox_termination(
        (trusted, "candidate-spoofed-phase"),
        resource_telemetry=None,
    )

    assert termination.kind is supervisor.TerminationKind.SANDBOX_ERROR
    assert termination.failure_phases == (
        trusted,
        supervisor.InfrastructureFailurePhase.UNKNOWN,
    )


def test_sandbox_termination_preserves_available_cgroup_telemetry() -> None:
    """Fail-closed classification retains already observed trusted counters."""
    telemetry = supervisor.CgroupResourceTelemetry(2, 1, 3)

    termination = supervisor._sandbox_termination(
        (supervisor.InfrastructureFailurePhase.PROCESS_CLEANUP,),
        resource_telemetry=telemetry,
    )

    assert termination.resource_telemetry == telemetry


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
        env=_credential_free_environment(tmp_path),
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
        env=_credential_free_environment(tmp_path),
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
        timeout=10, env=_credential_free_environment(tmp_path), writable_roots=(tmp_path,),
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
        cwd=tmp_path, timeout=10, env=_credential_free_environment(tmp_path), writable_roots=(tmp_path,),
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
        cwd=scratch, timeout=10, env=_credential_free_environment(tmp_path),
        writable_roots=(scratch,),
    )
    assert completed.returncode == 0
    time.sleep(0.3)
    assert result_channel.read_text(encoding="utf-8") == "checker-owned"


@pytest.mark.skipif(not shutil.which("bwrap"), reason="requires Linux bubblewrap")
def test_output_is_bounded(tmp_path: Path) -> None:
    result, _surviving = run_supervised(
        [sys.executable, "-c", "print('x' * 20000000)"], cwd=tmp_path,
        timeout=10, env=_credential_free_environment(tmp_path), writable_roots=(tmp_path,),
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
        env=_credential_free_environment(tmp_path), writable_roots=(tmp_path,), limits=limits,
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
    assert result.termination.failure_phases == (
        supervisor.InfrastructureFailurePhase.CONSTRUCTION,
    )
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
        cwd=tmp_path, timeout=10, env=_credential_free_environment(tmp_path),
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
    monkeypatch.setattr(supervisor, "_fresh_supervision_token", lambda: token)
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
            command, cwd=tmp_path, timeout=timeout,
            env=_credential_free_environment(tmp_path),
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
        env=_credential_free_environment(tmp_path), writable_roots=(tmp_path,),
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
        except FileNotFoundError:
            continue
        except (OSError,ValueError) as error:
            fail(f'read descriptor: pid={pid_dir.name} fd={entry.name}: '
                 f'{type(error).__name__}: {error}')
    return links

def fd_mnt_id(pid_dir,fd):
    lines=read_text(pid_dir/'fdinfo'/str(fd),pid_dir,'read descriptor mount ID').splitlines()
    values=[line.partition(':')[2].strip() for line in lines if line.startswith('mnt_id:')]
    if len(values)!=1 or not values[0].isdigit() or int(values[0])<=0:
        fail(f'parse descriptor mount ID: pid={pid_dir.name} fd={fd}')
    return int(values[0])

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
    scope_only=payload.get('scope_only')
    if type(scope_only) is not bool:
        fail('invalid scope-only payload')
    expected_namespace=payload.get('namespace')
    if expected_namespace is not None and (
            type(expected_namespace) is not dict or
            set(expected_namespace)!=set(('link','inode')) or
            type(expected_namespace.get('link')) is not str or
            type(expected_namespace.get('inode')) is not int):
        fail('invalid expected mount namespace payload')
    root_holders=payload.get('root_holders')
    if type(root_holders) is not list:
        fail('invalid root holder payload')
    root_by_key={}
    for holder in root_holders:
        if type(holder) is not dict:
            fail('invalid root holder payload')
        pid=holder.get('pid'); start_time=holder.get('start_time')
        descriptor=holder.get('fd'); root_fd=holder.get('root_fd')
        if (type(pid) is not int or pid<=0 or type(start_time) is not str or
                not start_time.isdigit() or type(descriptor) is not int or
                descriptor<0 or type(root_fd) is not int or root_fd<0):
            fail('invalid root holder payload')
        key=(pid,start_time,descriptor)
        if key in root_by_key:
            fail('duplicate root holder payload')
        root_by_key[key]=root_fd
    targets=set(payload.get('targets',[]))
    for value in targets:
        canonical_path(value,'target')
    prefix_value=payload.get('target_prefix','')
    prefix=canonical_path(prefix_value,'target prefix') if prefix_value else None
    identities=[]; cgroup_members=[]; watched_processes=[]
    current_holders=[]; fd_holders=[]; mount_holders=[]
    if scope_only:
        pid_directories=(proc/str(pid) for pid in sorted(members|watched))
    else:
        pid_directories=sorted(
            (path for path in proc.iterdir() if path.name.isdigit()),
            key=lambda path:int(path.name),
        )
    for pid_dir in pid_directories:
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
                        fd_holder=record|{
                            'holder_kind':'fd','fd':fd,
                            'fd_path':str(pid_dir/'fd'/str(fd)),
                            'fd_link':link,'fd_inode':inode,
                        }
                        root_fd=root_by_key.get((record['pid'],record['start_time'],fd))
                        if root_fd is not None:
                            root_path=pid_dir/'fd'/str(root_fd)
                            root_metadata=root_path.stat()
                            fd_holder=fd_holder|{
                                'root_fd':root_fd,'root_path':str(root_path),
                                'root_device':root_metadata.st_dev,
                                'root_inode':root_metadata.st_ino,
                                'root_mode':root_metadata.st_mode,
                                'root_mnt_id':fd_mnt_id(pid_dir,root_fd),
                            }
                        fd_holders.append(fd_holder)
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


@dataclass(frozen=True)
class _RootProcSelection:
    """Bound the privileged procfs scan to selected process identities."""

    watch_pids: tuple[int, ...] = ()
    scope_only: bool = False
    root_holders: tuple[dict[str, object], ...] = ()


def _root_proc_scan(
    *, cgroup: Path | None = None, namespace: dict[str, object] | None = None,
    targets: tuple[Path, ...] = (), target_prefix: Path | None = None,
    selection: _RootProcSelection = _RootProcSelection(),
) -> dict[str, object]:
    """Run one bounded root scanner that fails closed on ambiguous procfs evidence."""
    payload = {
        "cgroup": str(cgroup) if cgroup is not None else "",
        "namespace": namespace,
        "targets": [str(path) for path in targets],
        "target_prefix": str(target_prefix) if target_prefix is not None else "",
        "watch_pids": list(selection.watch_pids),
        "scope_only": selection.scope_only,
        "root_holders": list(selection.root_holders),
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


def _namespace_root_entry_path(holder: dict[str, object]) -> str:
    """Return the PID-reuse-safe root entry paired with a namespace holder."""
    pid = holder.get("pid")
    if type(pid) is not int or pid <= 0:
        raise ValueError("namespace holder has invalid process identity")
    if holder.get("holder_kind") == "current":
        return f"/proc/{pid}/root"
    descriptor = holder.get("root_fd")
    if type(descriptor) is not int or descriptor < 0:
        raise ValueError("FD-only namespace holder has invalid root descriptor")
    expected_path = f"/proc/{pid}/fd/{descriptor}"
    if holder.get("root_path") != expected_path:
        raise ValueError("FD-only namespace holder has wrong root descriptor path")
    if (
        type(holder.get("root_device")) is not int
        or type(holder.get("root_inode")) is not int
        or type(holder.get("root_mode")) is not int
        or type(holder.get("root_mnt_id")) is not int
        or int(holder["root_device"]) < 0
        or int(holder["root_inode"]) <= 0
        or int(holder["root_mode"]) <= 0
        or int(holder["root_mnt_id"]) <= 0
    ):
        raise ValueError("FD-only namespace holder has invalid root descriptor identity")
    return expected_path


def _external_holder_termination_payload(
    holder: dict[str, object], namespace: dict[str, object],
) -> str:
    """Serialize only a complete captured holder for pidfd termination."""
    _namespace_entry_path(holder, namespace)
    return json.dumps({
        "holder": holder, "namespace": namespace, "operation": "terminate",
    }, sort_keys=True, separators=(",", ":"))


@dataclass(frozen=True)
class _NamespaceHolderCommandContext:
    """Trusted command and ownership values for one held-namespace operation."""

    control_prefix: Path
    captured_mounts: set[Path]
    nsenter: str
    umount: str
    helper_python: str


_HELD_NAMESPACE_DIAGNOSTIC_MAX_TARGETS = 512
_HELD_NAMESPACE_DIAGNOSTIC_MAX_PATH_BYTES = 1024
_HELD_NAMESPACE_DIAGNOSTIC_MAX_DETAIL_BYTES = 128
_HELD_NAMESPACE_DIAGNOSTIC_MAX_EXACT_MOUNTS = 16
_HELD_NAMESPACE_DIAGNOSTIC_MAX_RELATED_MOUNTS = 8
_HELD_NAMESPACE_DIAGNOSTIC_MAX_TARGET_SAMPLES = 16
# A non-ASCII UTF-8 byte can expand to three JSON bytes (a four-byte scalar
# becomes two ``\\uXXXX`` escapes).  The scan contains one complete inventory;
# the response contains complete target and mount inventories.
_HELD_NAMESPACE_JSON_ESCAPED_BYTES_PER_UTF8_BYTE = 3
_HELD_NAMESPACE_SCAN_PAYLOAD_MAX_BYTES = (
    _HELD_NAMESPACE_DIAGNOSTIC_MAX_TARGETS
    * _HELD_NAMESPACE_DIAGNOSTIC_MAX_PATH_BYTES
    * _HELD_NAMESPACE_JSON_ESCAPED_BYTES_PER_UTF8_BYTE
    + 64 * 1024
)
_HELD_NAMESPACE_DIAGNOSTIC_MAX_BYTES = (
    2 * _HELD_NAMESPACE_DIAGNOSTIC_MAX_TARGETS
    * _HELD_NAMESPACE_DIAGNOSTIC_MAX_PATH_BYTES
    * _HELD_NAMESPACE_JSON_ESCAPED_BYTES_PER_UTF8_BYTE
    + 256 * 1024
)
# Kept solely for the retained v1 parser fixture below.
_HELD_NAMESPACE_DIAGNOSTIC_MAX_TEXT = _HELD_NAMESPACE_DIAGNOSTIC_MAX_PATH_BYTES
_HELD_NAMESPACE_DIAGNOSTIC_MAX_DETAIL_TEXT = _HELD_NAMESPACE_DIAGNOSTIC_MAX_DETAIL_BYTES


def _held_namespace_scan_stdin(
    holder: dict[str, object], context: _NamespaceHolderCommandContext,
) -> bytes:
    """Serialize the complete inventory for the bounded authenticated stdin leg."""
    root_fields = ("root_device", "root_inode", "root_mode", "root_mnt_id")
    expected_root = None if not all(field in holder for field in root_fields) else {
        "device": holder["root_device"], "inode": holder["root_inode"],
        "mode": holder["root_mode"], "mount_id": holder["root_mnt_id"],
    }
    payload = {
        "operation": "scan", "prefix": str(context.control_prefix),
        "targets": [str(path) for path in sorted(context.captured_mounts)],
        "expected_root": expected_root,
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    if len(encoded) > _HELD_NAMESPACE_SCAN_PAYLOAD_MAX_BYTES:
        raise ValueError("namespace diagnostic scan payload exceeds byte cap")
    return encoded


def _namespace_holder_command_payload(
    holder: dict[str, object], namespace: dict[str, object], operation: str, *,
    mount: Path | None = None, context: _NamespaceHolderCommandContext,
) -> str:
    """Serialize one exact namespace scan or unmount without empty mount arguments."""
    _namespace_entry_path(holder, namespace)
    _namespace_root_entry_path(holder)
    if operation == "unmount":
        if mount is None or not _canonical_owned_mount_point(
            str(mount), context.control_prefix, tuple(context.captured_mounts),
        ):
            raise ValueError("namespace unmount point is not owned")
    elif operation != "scan" or mount is not None:
        raise ValueError("invalid namespace holder operation")
    payload = {
        "holder": holder, "namespace": namespace,
        "nsenter": context.nsenter, "umount": context.umount,
        "python": context.helper_python,
        "operation": operation,
    }
    if operation == "unmount":
        payload["mount"] = str(mount)
    else:
        scan_stdin = _held_namespace_scan_stdin(holder, context)
        payload["scanner"] = _NAMESPACE_MOUNT_SCANNER_SOURCE
        payload["scan_bytes"] = len(scan_stdin)
        payload["scan_sha256"] = hashlib.sha256(scan_stdin).hexdigest()
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def _holder_key(record: dict[str, object]) -> tuple[object, ...]:
    """Return the complete identity of one current or FD-only namespace holder."""
    return (
        record.get("holder_kind"), *_process_key(record), record.get("fd"),
        record.get("fd_path"), record.get("fd_link"), record.get("fd_inode"),
        record.get("root_fd"), record.get("root_path"),
        record.get("root_device"), record.get("root_inode"),
        record.get("root_mode"), record.get("root_mnt_id"),
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
import errno,fcntl,hashlib,json,os,pathlib,signal,sys

COMPONENT='revalidator'
PHASE='control-parsing'
EXCEPTION_TOKENS=((json.JSONDecodeError,'jsondecodeerror'),(OSError,'oserror'),
                  (ValueError,'valueerror'),(TypeError,'typeerror'),
                  (KeyError,'keyerror'),(RuntimeError,'runtimeerror'),
                  (Exception,'exception'),(BaseException,'baseexception'))
def uncaught(exception_type,_exception,_traceback):
    token=next(token for expected,token in EXCEPTION_TOKENS
               if issubclass(exception_type,expected))
    try: os.write(2,('pdd-held-namespace-failure:'+COMPONENT+':'+PHASE+':'+token+'\n').encode('ascii'))
    except OSError: pass
sys.excepthook=uncaught

if len(sys.argv)!=2 or len(sys.argv[1].encode('utf-8'))>131072:
    raise SystemExit('diagnostic transport invariant')
try:
    payload=json.loads(sys.argv[1])
except json.JSONDecodeError as error:
    raise SystemExit('diagnostic transport invariant') from error
if not isinstance(payload,dict):
    raise SystemExit('diagnostic transport invariant')
if sys.argv[1] != json.dumps(payload,sort_keys=True,separators=(',',':')):
    raise SystemExit('diagnostic transport invariant')
PHASE='holder-validation'
holder=payload['holder']; namespace=payload['namespace']
pid=holder.get('pid'); start_time=holder.get('start_time')
if type(pid) is not int or pid<=0 or type(start_time) is not str:
    raise SystemExit('invalid holder process identity')
PHASE='pidfd'
try:
    pidfd=os.pidfd_open(pid,0)
except ProcessLookupError:
    raise SystemExit(0)
PHASE='namespace-pin'
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
operation=payload.get('operation')
if operation=='terminate':
    try:
        signal.pidfd_send_signal(pidfd,signal.SIGTERM,None,0)
    except ProcessLookupError:
        pass
    os.close(pidfd)
    raise SystemExit(0)

def transport_failure(category):
    raise RuntimeError('diagnostic transport '+category)

def read_scan_stdin(expected_bytes,expected_digest):
    if (type(expected_bytes) is not int or expected_bytes<0 or
            expected_bytes>1638400 or type(expected_digest) is not str or
            len(expected_digest)!=64 or any(char not in '0123456789abcdef' for char in expected_digest)):
        transport_failure('invariant')
    chunks=[]; total=0
    while True:
        chunk=sys.stdin.buffer.read(min(65536,1638401-total))
        if not chunk: break
        total+=len(chunk)
        if total>1638400: transport_failure('oversized')
        chunks.append(chunk)
    raw=b''.join(chunks)
    if len(raw)!=expected_bytes or hashlib.sha256(raw).hexdigest()!=expected_digest:
        transport_failure('authentication')
    return raw

def sealed_memfd(raw):
    required=('F_ADD_SEALS','F_GET_SEALS','F_SEAL_WRITE','F_SEAL_GROW','F_SEAL_SHRINK','F_SEAL_SEAL')
    if not hasattr(os,'memfd_create') or not hasattr(os,'MFD_ALLOW_SEALING') or any(not hasattr(fcntl,name) for name in required):
        transport_failure('unavailable')
    try:
        fd=os.memfd_create('pdd-held-namespace-scan',os.MFD_CLOEXEC|os.MFD_ALLOW_SEALING)
        offset=0
        while offset<len(raw):
            written=os.write(fd,raw[offset:])
            if written<=0: transport_failure('invariant')
            offset+=written
        if offset!=len(raw) or os.lseek(fd,0,os.SEEK_SET)!=0:
            transport_failure('invariant')
        seals=fcntl.F_SEAL_WRITE|fcntl.F_SEAL_GROW|fcntl.F_SEAL_SHRINK|fcntl.F_SEAL_SEAL
        fcntl.fcntl(fd,fcntl.F_ADD_SEALS,seals)
        if fcntl.fcntl(fd,fcntl.F_GET_SEALS)&seals!=seals:
            transport_failure('invariant')
        return fd
    except RuntimeError:
        raise
    except OSError as error:
        transport_failure('unavailable' if error.errno in {1,22,38,95} else 'invariant')

def inherit_only(*descriptors):
    allowed=set(descriptors)
    try:
        opened=[int(entry.name) for entry in pathlib.Path('/proc/self/fd').iterdir()]
        for descriptor in opened:
            if descriptor>2 and descriptor not in allowed:
                try:
                    os.set_inheritable(descriptor,False)
                except OSError as error:
                    if error.errno==errno.EBADF:
                        continue
                    raise
        for descriptor in allowed:
            os.set_inheritable(descriptor,True)
    except OSError:
        transport_failure('invariant')
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
PHASE='root-pin'
if kind=='current':
    root_entry=str(proc/'root')
else:
    root_fd=holder.get('root_fd')
    if type(root_fd) is not int or root_fd<0:
        raise RuntimeError('invalid root descriptor')
    root_path=proc/'fd'/str(root_fd)
    if str(root_path)!=holder.get('root_path'):
        raise RuntimeError('root descriptor identity changed')
    root_entry=str(root_path)
namespace_fd=os.open(entry,os.O_RDONLY|os.O_CLOEXEC)
exact_namespace(pathlib.Path('/proc/self/fd')/str(namespace_fd))
root_fd=os.open(root_entry,getattr(os,'O_PATH',0)|os.O_CLOEXEC)
root_metadata=os.fstat(root_fd)
root_info=(pathlib.Path('/proc/self/fdinfo')/str(root_fd)).read_text(encoding='ascii')
root_mnt_ids=[line.partition(':')[2].strip() for line in root_info.splitlines() if line.startswith('mnt_id:')]
if (len(root_mnt_ids)!=1 or not root_mnt_ids[0].isdigit() or
        int(root_mnt_ids[0])<=0):
    raise RuntimeError('invalid root descriptor mount ID')
if kind=='fd' and (root_metadata.st_dev!=holder.get('root_device') or
        root_metadata.st_ino!=holder.get('root_inode') or
        root_metadata.st_mode!=holder.get('root_mode') or
        int(root_mnt_ids[0])!=holder.get('root_mnt_id')):
    raise RuntimeError('root descriptor identity changed')
if identity()!=start_time:
    raise RuntimeError('holder identity raced after descriptor pinning')
scan_fd=None
if operation=='scan':
    PHASE='scan-transport'
    scan_fd=sealed_memfd(read_scan_stdin(payload.get('scan_bytes'),payload.get('scan_sha256')))
PHASE='fd-inheritance'
inherit_only(namespace_fd,root_fd,*(() if scan_fd is None else (scan_fd,)))
PHASE='exec'
os.close(pidfd)
if operation=='unmount':
    mount=payload.get('mount')
    if type(mount) is not str or not mount.startswith('/'):
        raise RuntimeError('invalid namespace unmount point')
    mount_path=pathlib.PurePosixPath(mount)
    if str(mount_path)!=mount or any(part in ('.','..') for part in mount_path.parts):
        raise RuntimeError('invalid namespace unmount point')
    command=[payload['umount'],mount]
elif operation=='scan':
    if scan_fd is None:
        transport_failure('invariant')
    command=[payload['python'],'-I','-S','-c',payload['scanner'],
             '/proc/self/fd/'+str(scan_fd),str(payload['scan_bytes']),payload['scan_sha256']]
else:
    raise RuntimeError('invalid namespace operation')
os.execv(payload['nsenter'],[payload['nsenter'],'--mount=/proc/self/fd/'+str(namespace_fd),
                             '--root=/proc/self/fd/'+str(root_fd),'--',*command])
"""


_NAMESPACE_MOUNT_SCANNER_SOURCE = r"""
import hashlib,json,os,pathlib,sys

COMPONENT='scanner'
PHASE='transport'
EXCEPTION_TOKENS=((json.JSONDecodeError,'jsondecodeerror'),(OSError,'oserror'),
                  (ValueError,'valueerror'),(TypeError,'typeerror'),
                  (KeyError,'keyerror'),(RuntimeError,'runtimeerror'),
                  (Exception,'exception'),(BaseException,'baseexception'))
def uncaught(exception_type,_exception,_traceback):
    token=next(token for expected,token in EXCEPTION_TOKENS
               if issubclass(exception_type,expected))
    try: os.write(2,('pdd-held-namespace-failure:'+COMPONENT+':'+PHASE+':'+token+'\n').encode('ascii'))
    except OSError: pass
sys.excepthook=uncaught

# Hosted inventory has reached roughly 130 mountpoints; retain all up to 512.
MAX_INVENTORY=512
MAX_TARGET_SAMPLES=16
MAX_EXACT_SAMPLES=16
MAX_RELATED_MOUNTS=8
MAX_PATH_BYTES=1024
MAX_DETAIL_BYTES=128
MAX_INPUT_BYTES=1638400
MAX_OUTPUT_BYTES=3407872
if len(sys.argv)!=4 or not sys.argv[1].startswith('/proc/self/fd/'):
    raise RuntimeError('invalid diagnostic transport reference')
try:
    expected_bytes=int(sys.argv[2]); expected_digest=sys.argv[3]
except ValueError as error:
    raise RuntimeError('invalid diagnostic transport reference') from error
if (expected_bytes<0 or expected_bytes>MAX_INPUT_BYTES or len(expected_digest)!=64 or
        any(character not in '0123456789abcdef' for character in expected_digest)):
    raise RuntimeError('invalid diagnostic transport reference')
with open(sys.argv[1],'rb',buffering=0) as transport:
    chunks=[]; total=0
    while True:
        chunk=transport.read(min(65536,MAX_INPUT_BYTES+1-total))
        if not chunk: break
        total+=len(chunk)
        if total>MAX_INPUT_BYTES: raise RuntimeError('oversized diagnostic scan payload')
        chunks.append(chunk)
    if transport.read(1)!=b'': raise RuntimeError('diagnostic scan payload has trailing bytes')
raw_payload=b''.join(chunks)
if len(raw_payload)!=expected_bytes or hashlib.sha256(raw_payload).hexdigest()!=expected_digest:
    raise RuntimeError('invalid diagnostic scan payload')
PHASE='payload'
try:
    payload=json.loads(raw_payload.decode('utf-8'))
except (UnicodeDecodeError,json.JSONDecodeError) as error:
    raise RuntimeError('invalid diagnostic scan payload') from error
if raw_payload!=json.dumps(payload,sort_keys=True,separators=(',',':')).encode('utf-8'):
    raise RuntimeError('diagnostic scan payload has trailing bytes')

def raw_text(value,label):
    if (type(value) is not str or not value or
            any((ord(character)<32 and character not in '\t\n') or ord(character)==127
                for character in value)):
        raise RuntimeError(f'invalid {label}')
    return value

def text(value,label):
    value=raw_text(value,label)
    if len(value.encode('utf-8'))>MAX_PATH_BYTES:
        raise RuntimeError(f'oversized {label}')
    return value

def limited(value,label):
    value=raw_text(value,label)
    encoded=value.encode('utf-8')
    return encoded[:MAX_DETAIL_BYTES].decode('utf-8','ignore'),len(encoded)>MAX_DETAIL_BYTES

def canonical(value,label):
    value=text(value,label)
    if not value.startswith('/'):
        raise RuntimeError(f'{label} is not absolute')
    path=pathlib.PurePosixPath(value)
    if str(path)!=value or any(part in ('.','..') for part in path.parts):
        raise RuntimeError(f'{label} is not canonical')
    return path

def unescape(value,label):
    output=[]; index=0
    while index<len(value):
        if value[index]!='\\':
            output.append(value[index]); index+=1; continue
        escaped=value[index+1:index+4]
        if escaped not in {'040','011','012','134'}:
            raise RuntimeError(f'invalid {label} escape')
        output.append(chr(int(escaped,8))); index+=4
    return raw_text(''.join(output),label)

def metadata(path,follow):
    path=pathlib.Path(path)
    try:
        result=path.stat() if follow else path.lstat()
    except OSError as error:
        if type(error.errno) is not int or error.errno<=0 or error.errno>4095:
            raise RuntimeError('invalid metadata errno') from error
        return {'status':'error','errno':error.errno}
    return {'status':'ok','device':result.st_dev,'inode':result.st_ino,'mode':result.st_mode}

def path_record(path):
    lstat=metadata(path,False); followed=metadata(path,True)
    return {'path':str(path),'exists':followed['status']=='ok','lstat':lstat,'stat':followed}

def cwd_record():
    try:
        return {'status':'ok','path':str(canonical(os.getcwd(),'cwd'))}
    except OSError as error:
        if type(error.errno) is not int or error.errno<=0 or error.errno>4095:
            raise RuntimeError('invalid cwd errno') from error
        return {'status':'error','errno':error.errno}

def mount_record(line):
    fields=line.split(); separator=fields.index('-') if '-' in fields else -1
    if (separator<6 or len(fields)!=separator+4 or not fields[0].isdigit() or
            not fields[1].isdigit() or fields[2].count(':')!=1):
        raise RuntimeError('malformed mountinfo')
    major,minor=fields[2].split(':')
    if not major.isdigit() or not minor.isdigit():
        raise RuntimeError('malformed mountinfo device')
    truncated=[]
    filesystem,filesystem_truncated=limited(fields[separator+1],'filesystem')
    source,source_truncated=limited(unescape(fields[separator+2],'source'),'source')
    mount_options,mount_options_truncated=limited(fields[5],'mount options')
    super_options,super_options_truncated=limited(fields[separator+3],'super options')
    for label,was_truncated in (
            ('filesystem',filesystem_truncated),('source',source_truncated),
            ('options.mount',mount_options_truncated),('options.super',super_options_truncated)):
        if was_truncated: truncated.append(label)
    truncated.sort()
    return {
        'mount_id':int(fields[0]),'parent_id':int(fields[1]),
        'root':str(canonical(unescape(fields[3],'mount root'),'mount root')),
        'mount_point':str(canonical(unescape(fields[4],'mount point'),'mount point')),
        'major_minor':fields[2], 'filesystem':filesystem,'source':source,
        'options':{'mount':mount_options,'super':super_options},'truncated':truncated,
    }

def contained(point):
    try:
        pathlib.PurePosixPath(point).relative_to(prefix); return True
    except ValueError:
        return False

def common_parts(left,right):
    count=0
    for left_part,right_part in zip(left.parts,right.parts):
        if left_part!=right_part: break
        count+=1
    return count

def valid_optional_fields(fields):
    for field in fields:
        field=unescape(field,'mountinfo optional field')
        tag,separator,value=field.partition(':')
        if (not tag or not tag.replace('_','a').replace('-','a').isalnum() or
                not tag[0].isalpha() or any(ord(character)<32 or ord(character)==127 for character in field) or
                (separator and (not value or ':' in value))):
            raise RuntimeError('invalid mountinfo optional field')
        if tag in {'shared','master','propagate_from'} and (separator!=':' or not value.isdigit() or int(value)<=0):
            raise RuntimeError('invalid mountinfo optional field')

if set(payload)!={'operation','prefix','targets','expected_root'} or payload['operation']!='scan':
    raise RuntimeError('invalid diagnostic scan payload')
PHASE='paths'
prefix=canonical(payload['prefix'],'prefix')
if type(payload['targets']) is not list or len(payload['targets'])>MAX_INVENTORY:
    raise RuntimeError('invalid diagnostic targets')
target_paths=[canonical(value,'target') for value in payload['targets']]
if [str(path) for path in target_paths]!=sorted({str(path) for path in target_paths}):
    raise RuntimeError('diagnostic targets are not unique and sorted')
targets={str(path) for path in target_paths}
expected_root=payload['expected_root']
if expected_root is not None:
    if set(expected_root)!={'device','inode','mode','mount_id'} or any(
            type(expected_root[field]) is not int or expected_root[field] <= 0
            for field in expected_root):
        raise RuntimeError('invalid expected root identity')
PHASE='namespace'
namespace_path=pathlib.Path('/proc/self/ns/mnt')
namespace_link=text(os.readlink(namespace_path),'mount namespace link')
namespace_inode=namespace_path.stat().st_ino
if not namespace_link.startswith('mnt:[') or not namespace_link.endswith(']') or namespace_inode<=0:
    raise RuntimeError('invalid current mount namespace')
PHASE='root'
root_path=pathlib.Path('/proc/self/root')
root_link=str(canonical(os.readlink(root_path),'root link'))
root_fd=os.open(root_path,getattr(os,'O_PATH',0)|os.O_CLOEXEC)
try:
    root_metadata=os.fstat(root_fd)
    root_info=(pathlib.Path('/proc/self/fdinfo')/str(root_fd)).read_text(encoding='ascii')
finally:
    os.close(root_fd)
root_mnt_ids=[line.partition(':')[2].strip() for line in root_info.splitlines()
              if line.startswith('mnt_id:')]
if len(root_mnt_ids)!=1 or not root_mnt_ids[0].isdigit() or int(root_mnt_ids[0])<=0:
    raise RuntimeError('invalid current root mount ID')
PHASE='mountinfo'
records=[]
for line in pathlib.Path('/proc/self/mountinfo').read_text(encoding='utf-8').splitlines():
    fields=line.split(); separator=fields.index('-') if '-' in fields else -1
    if separator<6:
        raise RuntimeError('malformed mountinfo')
    valid_optional_fields(fields[6:separator])
    records.append(mount_record(line))
exact=[record for record in records if record['mount_point'] in targets or contained(record['mount_point'])]
exact=sorted(exact,key=lambda record:(record['mount_point'],record['mount_id']))
mounts=[record['mount_point'] for record in exact]
if len(mounts)>MAX_INVENTORY:
    raise RuntimeError('too many held mount inventory entries')
exact_samples=exact[:MAX_EXACT_SAMPLES]
related=[]
if not exact:
    probes=(prefix,*target_paths)
    def distance(record):
        point=pathlib.PurePosixPath(record['mount_point'])
        shared=max(common_parts(point,probe) for probe in probes)
        return (len(point.parts)+min(len(probe.parts) for probe in probes)-2*shared,
                -shared,record['mount_id'])
    related=sorted(records,key=distance)[:MAX_RELATED_MOUNTS]
PHASE='paths'
cwd=cwd_record()
paths={'prefix':path_record(prefix),'target_count':len(target_paths),
       'targets':[path_record(path) for path in target_paths[:MAX_TARGET_SAMPLES]]}
PHASE='output'
output={
    'schema':'pdd-held-namespace-diagnostic-v1','operation':'scan',
    'prefix':str(prefix),'targets':[str(path) for path in target_paths],
    'mount_namespace':{'link':namespace_link,'inode':namespace_inode},
    'root':{'link':root_link,'expected':expected_root,
            'actual':{'device':root_metadata.st_dev,'inode':root_metadata.st_ino,
                      'mode':root_metadata.st_mode,'mount_id':int(root_mnt_ids[0])},
            'matches':None if expected_root is None else expected_root=={
                'device':root_metadata.st_dev,'inode':root_metadata.st_ino,
                'mode':root_metadata.st_mode,'mount_id':int(root_mnt_ids[0])}},
    'cwd':cwd,
    'paths':paths,
    'mountinfo':{'mounts':mounts,'exact_count':len(exact),
                 'samples':exact_samples,'related':related},
}
encoded=json.dumps(output,sort_keys=True,separators=(',',':')).encode('utf-8')
if len(encoded)+1>MAX_OUTPUT_BYTES:
    raise RuntimeError('oversized held namespace diagnostic output')
sys.stdout.buffer.write(encoded)
sys.stdout.buffer.write(b'\n')
"""


def _parse_held_namespace_diagnostic_legacy(
    output: str, *, namespace: dict[str, object], control_prefix: Path,
    targets: tuple[Path, ...],
) -> tuple[dict[str, object], tuple[Path, ...]]:
    """Validate one bounded scanner envelope and return its exact owned mounts."""
    def reject(message: str) -> None:
        raise ValueError(f"held namespace diagnostic {message}")

    def bounded_text(value: object, label: str) -> str:
        if (
            type(value) is not str or not value or
            len(value) > _HELD_NAMESPACE_DIAGNOSTIC_MAX_TEXT or
            any(ord(character) < 32 or ord(character) == 127 for character in value)
        ):
            reject(f"has invalid {label}")
        return value

    def canonical_path(value: object, label: str) -> str:
        text = bounded_text(value, label)
        if not text.startswith("/"):
            reject(f"has non-absolute {label}")
        path = PurePosixPath(text)
        if str(path) != text or any(part in {".", ".."} for part in path.parts):
            reject(f"has non-canonical {label}")
        return text

    def positive_int(value: object, label: str, *, zero: bool = False) -> int:
        if type(value) is not int or value < (0 if zero else 1):
            reject(f"has invalid {label}")
        return value

    def metadata(value: object, label: str) -> None:
        if not isinstance(value, dict):
            reject(f"has invalid {label}")
        if value.get("status") == "ok":
            if set(value) != {"status", "device", "inode", "mode"}:
                reject(f"has invalid {label}")
            positive_int(value["device"], f"{label} device", zero=True)
            positive_int(value["inode"], f"{label} inode")
            positive_int(value["mode"], f"{label} mode", zero=True)
        elif value.get("status") == "error":
            if set(value) != {"status", "errno"}:
                reject(f"has invalid {label}")
            errno = positive_int(value["errno"], f"{label} errno")
            if errno > 4095:
                reject(f"has invalid {label} errno")
        else:
            reject(f"has invalid {label}")

    def path_record(value: object, expected: str, label: str) -> None:
        if not isinstance(value, dict) or set(value) != {
            "path", "exists", "lstat", "stat",
        }:
            reject(f"has invalid {label}")
        if canonical_path(value["path"], f"{label} path") != expected:
            reject(f"has mismatched {label} path")
        if type(value["exists"]) is not bool:
            reject(f"has invalid {label} existence")
        metadata(value["lstat"], f"{label} lstat")
        metadata(value["stat"], f"{label} stat")
        if value["exists"] != (value["stat"].get("status") == "ok"):
            reject(f"has inconsistent {label} existence")

    def mount_record(value: object, label: str) -> str:
        if not isinstance(value, dict) or set(value) != {
            "mount_id", "parent_id", "root", "mount_point", "major_minor",
            "filesystem", "source", "options", "truncated",
        }:
            reject(f"has invalid {label}")
        positive_int(value["mount_id"], f"{label} mount ID")
        positive_int(value["parent_id"], f"{label} parent ID", zero=True)
        canonical_path(value["root"], f"{label} root")
        point = canonical_path(value["mount_point"], f"{label} mount point")
        major_minor = bounded_text(value["major_minor"], f"{label} major minor")
        parts = major_minor.split(":")
        if len(parts) != 2 or not all(part.isdigit() for part in parts):
            reject(f"has invalid {label} major minor")
        bounded_text(value["filesystem"], f"{label} filesystem")
        bounded_text(value["source"], f"{label} source")
        options = value["options"]
        if not isinstance(options, dict) or set(options) != {"mount", "super"}:
            reject(f"has invalid {label} options")
        bounded_text(options["mount"], f"{label} mount options")
        bounded_text(options["super"], f"{label} super options")
        truncated = value["truncated"]
        permitted = {"filesystem", "source", "options.mount", "options.super"}
        if (
            type(truncated) is not list or len(truncated) > len(permitted) or
            any(type(item) is not str or item not in permitted for item in truncated) or
            truncated != sorted(set(truncated))
        ):
            reject(f"has invalid {label} truncation")
        return point

    if (
        type(output) is not str or
        len(output.encode("utf-8")) > _HELD_NAMESPACE_DIAGNOSTIC_MAX_BYTES
    ):
        reject("exceeds the output cap")
    try:
        diagnostic = json.loads(output)
    except json.JSONDecodeError as exc:
        raise ValueError("held namespace diagnostic is not JSON") from exc
    if not isinstance(diagnostic, dict) or set(diagnostic) != {
        "schema", "operation", "prefix", "targets", "mount_namespace", "root",
        "cwd", "paths", "mountinfo",
    }:
        reject("has invalid shape")
    if diagnostic["schema"] != "pdd-held-namespace-diagnostic-v1":
        reject("has invalid schema")
    if diagnostic["operation"] != "scan":
        reject("has invalid operation")
    expected_prefix = str(control_prefix)
    expected_targets = [str(path) for path in sorted(targets)]
    if canonical_path(diagnostic["prefix"], "prefix") != expected_prefix:
        reject("has mismatched prefix")
    reported_targets = diagnostic["targets"]
    if (
        type(reported_targets) is not list or
        len(reported_targets) > _HELD_NAMESPACE_DIAGNOSTIC_MAX_TARGETS or
        [canonical_path(value, "target") for value in reported_targets] != expected_targets
    ):
        reject("has mismatched targets")
    reported_namespace = diagnostic["mount_namespace"]
    if (
        not isinstance(reported_namespace, dict) or
        set(reported_namespace) != {"link", "inode"}
    ):
        reject("has invalid mount namespace")
    link = bounded_text(reported_namespace["link"], "mount namespace link")
    if not link.startswith("mnt:[") or not link.endswith("]") or not link[5:-1].isdigit():
        reject("has invalid mount namespace link")
    if (
        link != namespace.get("link") or
        positive_int(reported_namespace["inode"], "mount namespace inode") != namespace.get("inode")
    ):
        reject("has mismatched mount namespace")
    root = diagnostic["root"]
    if not isinstance(root, dict) or set(root) != {
        "link", "device", "inode", "mode", "mount_id",
    }:
        reject("has invalid root")
    canonical_path(root["link"], "root link")
    positive_int(root["device"], "root device", zero=True)
    positive_int(root["inode"], "root inode")
    positive_int(root["mode"], "root mode", zero=True)
    positive_int(root["mount_id"], "root mount ID")
    cwd = diagnostic["cwd"]
    if not isinstance(cwd, dict):
        reject("has invalid cwd")
    if cwd.get("status") == "ok":
        if set(cwd) != {"status", "path"}:
            reject("has invalid cwd")
        canonical_path(cwd["path"], "cwd path")
    elif cwd.get("status") == "error":
        if set(cwd) != {"status", "errno"}:
            reject("has invalid cwd")
        errno = positive_int(cwd["errno"], "cwd errno")
        if errno > 4095:
            reject("has invalid cwd errno")
    else:
        reject("has invalid cwd")
    paths = diagnostic["paths"]
    if not isinstance(paths, dict) or set(paths) != {"prefix", "targets"}:
        reject("has invalid paths")
    path_record(paths["prefix"], expected_prefix, "prefix")
    if type(paths["targets"]) is not list or len(paths["targets"]) != len(expected_targets):
        reject("has invalid target paths")
    for value, expected in zip(paths["targets"], expected_targets):
        path_record(value, expected, "target")
    mountinfo = diagnostic["mountinfo"]
    if not isinstance(mountinfo, dict) or set(mountinfo) != {"exact", "related"}:
        reject("has invalid mountinfo")
    exact = mountinfo["exact"]
    related = mountinfo["related"]
    if (
        type(exact) is not list or type(related) is not list or
        len(exact) > _HELD_NAMESPACE_DIAGNOSTIC_MAX_EXACT_MOUNTS or
        len(related) > _HELD_NAMESPACE_DIAGNOSTIC_MAX_RELATED_MOUNTS or
        (exact and related) or (not exact and not related)
    ):
        reject("has invalid mountinfo bounds")
    exact_points = [mount_record(value, "exact mount") for value in exact]
    if len({entry["mount_id"] for entry in exact}) != len(exact) or any(
        not _canonical_owned_mount_point(point, control_prefix, targets)
        for point in exact_points
    ):
        reject("has invalid exact mount ownership")
    related_points = [mount_record(value, "related mount") for value in related]
    if len({entry["mount_id"] for entry in related}) != len(related) or any(
        _canonical_owned_mount_point(point, control_prefix, targets)
        for point in related_points
    ):
        reject("has invalid related mounts")
    return diagnostic, tuple(Path(point) for point in sorted(exact_points))


def _parse_held_namespace_diagnostic(
    output: str, *, namespace: dict[str, object], holder: dict[str, object],
    control_prefix: Path, targets: tuple[Path, ...],
) -> tuple[dict[str, object], tuple[Path, ...]]:
    """Fail closed unless a complete inventory and bounded detail samples agree."""
    def reject(message: str) -> None:
        raise ValueError(f"held namespace diagnostic {message}")

    def text(value: object, label: str, *, detail: bool = False) -> str:
        maximum = (
            _HELD_NAMESPACE_DIAGNOSTIC_MAX_DETAIL_BYTES
            if detail else _HELD_NAMESPACE_DIAGNOSTIC_MAX_PATH_BYTES
        )
        if (
            type(value) is not str or not value or len(value.encode("utf-8")) > maximum
            or any(
                (ord(character) < 32 and character not in "\t\n")
                or ord(character) == 127 for character in value
            )
        ):
            reject(f"has invalid {label}")
        return value

    def path(value: object, label: str) -> str:
        value = text(value, label)
        candidate = PurePosixPath(value)
        if not value.startswith("/") or str(candidate) != value or any(
            part in {".", ".."} for part in candidate.parts
        ):
            reject(f"has non-canonical {label}")
        return value

    def integer(value: object, label: str, *, zero: bool = False) -> int:
        if type(value) is not int or value < (0 if zero else 1):
            reject(f"has invalid {label}")
        return value

    def identity(value: object, label: str) -> dict[str, int]:
        if not isinstance(value, dict) or set(value) != {"device", "inode", "mode", "mount_id"}:
            reject(f"has invalid {label}")
        return {
            "device": integer(value["device"], f"{label} device", zero=True),
            "inode": integer(value["inode"], f"{label} inode"),
            "mode": integer(value["mode"], f"{label} mode", zero=True),
            "mount_id": integer(value["mount_id"], f"{label} mount ID"),
        }

    def metadata(value: object, label: str) -> None:
        if not isinstance(value, dict):
            reject(f"has invalid {label}")
        if value.get("status") == "ok":
            if set(value) != {"status", "device", "inode", "mode"}:
                reject(f"has invalid {label}")
            integer(value["device"], f"{label} device", zero=True)
            integer(value["inode"], f"{label} inode")
            integer(value["mode"], f"{label} mode", zero=True)
            return
        if value.get("status") == "error" and set(value) == {"status", "errno"}:
            if integer(value["errno"], f"{label} errno") <= 4095:
                return
        reject(f"has invalid {label}")

    def path_record(value: object, expected: str, label: str) -> None:
        if not isinstance(value, dict) or set(value) != {"path", "exists", "lstat", "stat"}:
            reject(f"has invalid {label}")
        if path(value["path"], f"{label} path") != expected or type(value["exists"]) is not bool:
            reject(f"has mismatched {label}")
        metadata(value["lstat"], f"{label} lstat")
        metadata(value["stat"], f"{label} stat")
        if value["exists"] != (value["stat"].get("status") == "ok"):
            reject(f"has inconsistent {label} existence")

    def mount(value: object, label: str) -> tuple[str, int]:
        if not isinstance(value, dict) or set(value) != {
            "mount_id", "parent_id", "root", "mount_point", "major_minor",
            "filesystem", "source", "options", "truncated",
        }:
            reject(f"has invalid {label}")
        mount_id = integer(value["mount_id"], f"{label} mount ID")
        integer(value["parent_id"], f"{label} parent ID", zero=True)
        path(value["root"], f"{label} root")
        point = path(value["mount_point"], f"{label} mount point")
        major_minor = text(value["major_minor"], f"{label} major minor", detail=True)
        if len(major_minor.split(":")) != 2 or not all(
            part.isdigit() for part in major_minor.split(":")
        ):
            reject(f"has invalid {label} major minor")
        text(value["filesystem"], f"{label} filesystem", detail=True)
        text(value["source"], f"{label} source", detail=True)
        options = value["options"]
        if not isinstance(options, dict) or set(options) != {"mount", "super"}:
            reject(f"has invalid {label} options")
        text(options["mount"], f"{label} mount options", detail=True)
        text(options["super"], f"{label} super options", detail=True)
        permitted = {"filesystem", "source", "options.mount", "options.super"}
        truncated = value["truncated"]
        if (
            type(truncated) is not list or truncated != sorted(set(truncated))
            or any(type(item) is not str or item not in permitted for item in truncated)
        ):
            reject(f"has invalid {label} truncation")
        return point, mount_id

    if type(output) is not str or len(output.encode("utf-8")) > _HELD_NAMESPACE_DIAGNOSTIC_MAX_BYTES:
        reject("exceeds the output cap")
    try:
        diagnostic = json.loads(output)
    except json.JSONDecodeError as exc:
        raise ValueError("held namespace diagnostic is not JSON") from exc
    if not isinstance(diagnostic, dict) or set(diagnostic) != {
        "schema", "operation", "prefix", "targets", "mount_namespace", "root",
        "cwd", "paths", "mountinfo",
    }:
        reject("has invalid shape")
    if diagnostic["schema"] != "pdd-held-namespace-diagnostic-v1" or diagnostic["operation"] != "scan":
        reject("has invalid operation")
    expected_targets = [str(target) for target in sorted(targets)]
    if path(diagnostic["prefix"], "prefix") != str(control_prefix):
        reject("has mismatched prefix")
    reported_targets = diagnostic["targets"]
    if (
        type(reported_targets) is not list or len(reported_targets) > _HELD_NAMESPACE_DIAGNOSTIC_MAX_TARGETS
        or [path(value, "target") for value in reported_targets] != expected_targets
    ):
        reject("has mismatched targets")
    reported_namespace = diagnostic["mount_namespace"]
    if not isinstance(reported_namespace, dict) or set(reported_namespace) != {"link", "inode"}:
        reject("has invalid mount namespace")
    link = text(reported_namespace["link"], "mount namespace link")
    if (
        not link.startswith("mnt:[") or not link.endswith("]") or not link[5:-1].isdigit()
        or link != namespace.get("link")
        or integer(reported_namespace["inode"], "mount namespace inode") != namespace.get("inode")
    ):
        reject("has mismatched mount namespace")
    expected_root = None
    root_fields = ("root_device", "root_inode", "root_mode", "root_mnt_id")
    if all(field in holder for field in root_fields):
        expected_root = {
            "device": holder["root_device"], "inode": holder["root_inode"],
            "mode": holder["root_mode"], "mount_id": holder["root_mnt_id"],
        }
        expected_root = identity(expected_root, "captured root")
    root = diagnostic["root"]
    if not isinstance(root, dict) or set(root) != {"link", "expected", "actual", "matches"}:
        reject("has invalid root")
    path(root["link"], "root link")
    actual_root = identity(root["actual"], "actual root")
    if root["expected"] is None:
        if expected_root is not None or root["matches"] is not None:
            reject("has mismatched expected root")
    else:
        if identity(root["expected"], "expected root") != expected_root:
            reject("has mismatched expected root")
        if type(root["matches"]) is not bool or root["matches"] != (actual_root == expected_root):
            reject("has inconsistent root match")
    cwd = diagnostic["cwd"]
    if not isinstance(cwd, dict):
        reject("has invalid cwd")
    if cwd.get("status") == "ok" and set(cwd) == {"status", "path"}:
        path(cwd["path"], "cwd path")
    elif cwd.get("status") == "error" and set(cwd) == {"status", "errno"}:
        if integer(cwd["errno"], "cwd errno") > 4095:
            reject("has invalid cwd errno")
    else:
        reject("has invalid cwd")
    paths = diagnostic["paths"]
    if not isinstance(paths, dict) or set(paths) != {"prefix", "target_count", "targets"}:
        reject("has invalid paths")
    path_record(paths["prefix"], str(control_prefix), "prefix")
    if integer(paths["target_count"], "target count", zero=True) != len(expected_targets):
        reject("has mismatched target count")
    samples = paths["targets"]
    if type(samples) is not list or len(samples) > 16:
        reject("has invalid target samples")
    for record, expected in zip(samples, expected_targets[:16]):
        path_record(record, expected, "target")
    if len(samples) != min(16, len(expected_targets)):
        reject("has incomplete target samples")
    mountinfo = diagnostic["mountinfo"]
    if not isinstance(mountinfo, dict) or set(mountinfo) != {"mounts", "exact_count", "samples", "related"}:
        reject("has invalid mountinfo")
    mounts = mountinfo["mounts"]
    if type(mounts) is not list or len(mounts) > _HELD_NAMESPACE_DIAGNOSTIC_MAX_TARGETS:
        reject("has invalid mount inventory")
    mount_points = [path(value, "mount inventory") for value in mounts]
    if (
        mount_points != sorted(mount_points)
        or any(not _canonical_owned_mount_point(value, control_prefix, targets) for value in mount_points)
    ):
        reject("has invalid mount inventory")
    exact_count = integer(mountinfo["exact_count"], "exact count", zero=True)
    samples = mountinfo["samples"]
    related = mountinfo["related"]
    if type(samples) is not list or len(samples) > _HELD_NAMESPACE_DIAGNOSTIC_MAX_EXACT_MOUNTS:
        reject("has invalid mount samples")
    sample_keys = [mount(value, "mount sample") for value in samples]
    if (
        sample_keys != sorted(sample_keys)
        or [point for point, _mount_id in sample_keys] != mount_points[:len(sample_keys)]
    ):
        reject("has unordered mount samples")
    if (
        exact_count != len(mount_points)
        or len(sample_keys) != len(set(sample_keys))
        or len({mount_id for _point, mount_id in sample_keys}) != len(sample_keys)
        or len(samples) != min(16, exact_count)
    ):
        reject("has incomplete mount samples")
    if type(related) is not list or len(related) > _HELD_NAMESPACE_DIAGNOSTIC_MAX_RELATED_MOUNTS:
        reject("has invalid related mounts")
    related_keys = [mount(value, "related mount") for value in related]
    if mounts:
        if related:
            reject("has unrelated mount samples")
    elif not related_keys or any(_canonical_owned_mount_point(point, control_prefix, targets) for point, _mount_id in related_keys):
        reject("has invalid related mounts")
    return diagnostic, tuple(Path(value) for value in mount_points)


_HELD_NAMESPACE_SCAN_FAILURE_MARKER_PREFIX = "pdd-held-namespace-failure"
_HELD_NAMESPACE_SCAN_FAILURE_COMPONENT_PHASES = {
    "revalidator": frozenset({
        "control-parsing", "holder-validation", "pidfd", "namespace-pin",
        "root-pin", "scan-transport", "fd-inheritance", "exec",
    }),
    "scanner": frozenset({
        "transport", "payload", "namespace", "root", "mountinfo", "paths", "output",
    }),
}
_HELD_NAMESPACE_SCAN_FAILURE_EXCEPTION_CLASSES = frozenset({
    "jsondecodeerror", "oserror", "valueerror", "typeerror", "keyerror",
    "runtimeerror", "exception", "baseexception",
})
_HELD_NAMESPACE_SCAN_NSENTER_STDERR_CATEGORIES = (
    ("nsenter: reassociate to namespace ", "nsenter-reassociate-failed"),
    ("nsenter: failed to execute ", "nsenter-exec-failed"),
)


def _held_namespace_scan_stderr_category(line: str) -> str | None:
    """Classify exact child markers and anchored static nsenter failures."""
    marker = line.split(":")
    if (
        len(marker) == 4
        and marker[0] == _HELD_NAMESPACE_SCAN_FAILURE_MARKER_PREFIX
        and marker[1] in _HELD_NAMESPACE_SCAN_FAILURE_COMPONENT_PHASES
        and marker[2] in _HELD_NAMESPACE_SCAN_FAILURE_COMPONENT_PHASES[marker[1]]
        and marker[3] in _HELD_NAMESPACE_SCAN_FAILURE_EXCEPTION_CLASSES
    ):
        return line
    for prefix, category in _HELD_NAMESPACE_SCAN_NSENTER_STDERR_CATEGORIES:
        if line.startswith(prefix):
            return category
    if line.startswith("nsenter:"):
        return "nsenter-unclassified"
    return None


def _sanitized_held_namespace_scan_stderr(stderr: object) -> str:
    """Return bounded static child classifications without child-controlled detail."""
    if not isinstance(stderr, str):
        return "redacted"
    newest_categories = []
    size = 0
    for line in reversed(stderr.splitlines()[-8:]):
        category = _held_namespace_scan_stderr_category(line)
        if category is None or category in newest_categories:
            continue
        category_size = len(category.encode("ascii")) + bool(newest_categories)
        if size + category_size <= 256:
            newest_categories.append(category)
            size += category_size
    return ",".join(reversed(newest_categories)) or "redacted"


def _held_namespace_scan_child_returncode_category(returncode: object) -> str:
    """Format only a bounded nonzero process return code for cleanup diagnostics."""
    if type(returncode) is int and -255 <= returncode <= 255 and returncode != 0:
        return f"child-nonzero-returncode-{returncode}"
    return "child-nonzero-returncode-invalid"


@pytest.mark.parametrize(
    ("returncode", "expected"),
    (
        (-255, "child-nonzero-returncode--255"),
        (-9, "child-nonzero-returncode--9"),
        (1, "child-nonzero-returncode-1"),
        (255, "child-nonzero-returncode-255"),
        (0, "child-nonzero-returncode-invalid"),
        (-256, "child-nonzero-returncode-invalid"),
        (256, "child-nonzero-returncode-invalid"),
        (True, "child-nonzero-returncode-invalid"),
        ("2", "child-nonzero-returncode-invalid"),
    ),
)
def test_held_namespace_scan_child_returncode_category_is_bounded(
    returncode: object, expected: str,
) -> None:
    """Parent diagnostics expose only canonical bounded numeric child statuses."""
    assert _held_namespace_scan_child_returncode_category(returncode) == expected


def _held_namespace_scan_failure_marker(
    component: str, phase: str, exception_class: str,
) -> str:
    """Build one closed child marker for sanitizer contract tests."""
    return (
        f"{_HELD_NAMESPACE_SCAN_FAILURE_MARKER_PREFIX}:"
        f"{component}:{phase}:{exception_class}"
    )


def test_held_namespace_scan_stderr_sanitizer_classifies_only_exact_markers() -> None:
    """Only complete closed markers survive alongside dynamic child output."""
    revalidator_marker = _held_namespace_scan_failure_marker(
        "revalidator", "root-pin", "runtimeerror",
    )
    scanner_marker = _held_namespace_scan_failure_marker(
        "scanner", "mountinfo", "oserror",
    )
    stderr = (
        "Traceback (most recent call last): /private/token=secret\n"
        f"{revalidator_marker}\n"
        "RuntimeError: unexpected failure payload=/private/secret\n"
        f"{scanner_marker}\n"
    )

    classified = _sanitized_held_namespace_scan_stderr(stderr)

    assert classified == f"{revalidator_marker},{scanner_marker}"
    assert len(classified.encode("ascii")) <= 256
    assert "Traceback" not in classified
    assert "/private" not in classified
    assert "secret" not in classified


def test_held_namespace_scan_stderr_sanitizer_redacts_dynamic_child_content() -> None:
    """Unrecognized exception text cannot relay paths, payloads, or credentials."""
    stderr = (
        "Traceback (most recent call last):\n"
        "RuntimeError: unexpected failure path=/private/secret payload=token-value\n"
    )

    classified = _sanitized_held_namespace_scan_stderr(stderr)

    assert classified == "redacted"
    assert len(classified.encode("ascii")) <= 256
    assert "secret" not in classified
    assert "token-value" not in classified


def test_held_namespace_scan_stderr_sanitizer_rejects_marker_spoofing() -> None:
    """Marker prefixes, foreign tokens, and suffixes never classify."""
    marker = _held_namespace_scan_failure_marker(
        "scanner", "payload", "runtimeerror",
    )
    stderr = (
        f"attacker says {marker}\n"
        f"{marker} payload=/private/secret\n"
        "pdd-held-namespace-failure:scanner:bogus:runtimeerror\n"
        "pdd-held-namespace-failure:bogus:payload:runtimeerror\n"
        "pdd-held-namespace-failure:scanner:payload:bogus\n"
        "prefix nsenter: failed to execute /private/payload\n"
    )

    assert _sanitized_held_namespace_scan_stderr(stderr) == "redacted"


def test_held_namespace_scan_stderr_sanitizer_accepts_only_closed_marker_tokens() -> None:
    """Every component/phase/class token accepted by the sanitizer is closed."""
    for component, phases in _HELD_NAMESPACE_SCAN_FAILURE_COMPONENT_PHASES.items():
        for phase in phases:
            for exception_class in _HELD_NAMESPACE_SCAN_FAILURE_EXCEPTION_CLASSES:
                marker = _held_namespace_scan_failure_marker(
                    component, phase, exception_class,
                )
                assert _held_namespace_scan_stderr_category(marker) == marker


def test_held_namespace_scan_stderr_sanitizer_deduplicates_exact_markers() -> None:
    """Exact matching keeps each marker once without overlapping text ambiguity."""
    root_marker = _held_namespace_scan_failure_marker(
        "revalidator", "root-pin", "runtimeerror",
    )
    namespace_marker = _held_namespace_scan_failure_marker(
        "revalidator", "namespace-pin", "runtimeerror",
    )
    stderr = (
        f"{root_marker}\n"
        f"{namespace_marker}\n"
        f"{namespace_marker}\n"
    )

    assert _sanitized_held_namespace_scan_stderr(stderr) == (
        f"{root_marker},{namespace_marker}"
    )


def test_held_namespace_scan_stderr_sanitizer_prioritizes_terminal_categories() -> None:
    """Newest categories survive when all eight safe terminal lines exceed the cap."""
    categories = (
        *(
            _held_namespace_scan_failure_marker("scanner", phase, "runtimeerror")
            for phase in sorted(_HELD_NAMESPACE_SCAN_FAILURE_COMPONENT_PHASES["scanner"])
        ),
        _held_namespace_scan_failure_marker("revalidator", "exec", "oserror"),
    )
    stderr = "".join(f"{category}\n" for category in categories)

    classified = _sanitized_held_namespace_scan_stderr(stderr)

    assert classified == ",".join(categories[-4:])
    assert categories[-1] in classified
    assert categories[0] not in classified
    assert len(classified.encode("ascii")) <= 256


@pytest.mark.parametrize(
    ("stderr", "expected"),
    (
        (
            "nsenter: reassociate to namespace '/proc/self/fd/73' failed: "
            "Operation not permitted path=/private/secret",
            "nsenter-reassociate-failed",
        ),
        (
            "nsenter: failed to execute /private/secret/payload: No such file",
            "nsenter-exec-failed",
        ),
        (
            "nsenter: unexpected platform wording path=/private/secret",
            "nsenter-unclassified",
        ),
    ),
    ids=("reassociate", "execute", "unclassified"),
)
def test_held_namespace_scan_stderr_sanitizer_maps_anchored_nsenter_failures(
    stderr: str, expected: str,
) -> None:
    """Nsenter reports only one static class and never its dynamic path or payload."""
    classified = _sanitized_held_namespace_scan_stderr(stderr)

    assert classified == expected
    assert len(classified.encode("ascii")) <= 256
    assert "/private" not in classified
    assert "secret" not in classified
    assert "payload" not in classified


def _deferred_absent_is_proven(
    deferred: list[tuple[Path, str, bool]],
    remaining_scan: tuple[tuple[Path, ...], bool] | None,
    final_authoritative_mounts: tuple[Path, ...] | None,
) -> bool:
    """Accept stale-unmount output only with root-valid or final procfs absence."""
    root_valid_absence = (
        remaining_scan is not None and remaining_scan[1] and all(
            mount not in remaining_scan[0]
            for mount, _diagnostic, _ambiguous in deferred
        )
    )
    procfs_absence = final_authoritative_mounts is not None and all(
        mount not in final_authoritative_mounts
        for mount, _diagnostic, _ambiguous in deferred
    )
    if any(ambiguous for _mount, _diagnostic, ambiguous in deferred):
        return root_valid_absence
    return root_valid_absence or procfs_absence


def _ambiguous_absent_unmount_diagnostic(
    diagnostic: str, mount: Path,
) -> bool:
    """Match only C-locale util-linux output bound to the exact requested mount."""
    prefix = f"umount: {mount}: no mount point specified"
    return diagnostic in {prefix, prefix + "."}


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


def _saturate_descriptor_pipe(write_fd: int) -> None:
    """Fill one undrained pipe without assuming its kernel-selected capacity."""
    blocking = os.get_blocking(write_fd)
    chunk = b"x" * 65536
    os.set_blocking(write_fd, False)
    try:
        for _attempt in range(4096):
            try:
                os.write(write_fd, chunk)
            except BlockingIOError:
                return
        raise AssertionError("descriptor pipe did not reach capacity")
    finally:
        os.set_blocking(write_fd, blocking)


def _hold_validated_descriptor_result(
    result: object, ready_fd: int, release_fd: int,
) -> object:
    """Hold the authenticated helper result before its external handoff."""
    if os.write(ready_fd, b"R") != 1:
        raise RuntimeError("validated descriptor result was not announced")
    if os.read(release_fd, 1) != b"G":
        raise RuntimeError("validated descriptor result was not released")
    return result


def _close_stalled_observation_fds(
    owned_fds: tuple[int, ...], errors: list[str] | None = None,
) -> None:
    """Close every transferred lifecycle descriptor, recording non-EBADF failures."""
    for descriptor in owned_fds:
        if descriptor < 0:
            continue
        try:
            os.close(descriptor)
        except OSError as exc:
            if exc.errno != 9 and errors is not None:
                errors.append(f"close fd {descriptor} failed: {exc}")


def _fallback_stalled_observation_cleanup_impl(
    ownership: dict[str, object], owned_fds: tuple[int, ...], *,
    runner=subprocess.run, scanner=_root_proc_scan,
) -> tuple[int, ...]:
    """Boundedly remove every captured privileged resource after early observation loss."""
    errors = []
    held_namespace_diagnostics = []
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
    captured_fd_holders = tuple(
        holder for holder in captured_holders
        if holder.get("holder_kind") == "fd"
    )
    unit_action_failures = []

    def remaining() -> float:
        return deadline - time.monotonic()

    def command(argv: list[str], purpose: str, stdin: bytes | None = None):
        timeout = min(5, remaining())
        if timeout <= 0:
            errors.append(f"cleanup deadline expired before {purpose}")
            return None
        try:
            return runner(
                argv, check=False, capture_output=True, text=stdin is None,
                input=stdin, timeout=timeout,
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
                selection=_RootProcSelection(
                    (int(coordinator["pid"]),), root_holders=tuple(
                        holder for holder in captured_holders
                        if holder.get("holder_kind") == "fd"
                        and all(field in holder for field in (
                            "root_fd", "root_path", "root_device", "root_inode",
                            "root_mode", "root_mnt_id",
                        ))
                    ),
                ),
            )
        except BaseException as exc:  # pylint: disable=broad-exception-caught
            # Scanner failure is cleanup evidence, not a reason to abandon teardown.
            errors.append(f"privileged procfs scan failed: {type(exc).__name__}: {exc}")
            return None

    def teardown_exact_scope() -> None:
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
                    completed.stderr.strip()
                    or f"{purpose} returned {completed.returncode}"
                )

    def terminate_exact_coordinator() -> None:
        # Signal only a procfs-confirmed PID/start-time identity; a reused PID
        # is untouchable. Held mounts are already gone, so coordinator cleanup
        # can no longer invalidate paths needed by the authenticated unmount.
        scan = scan_owned()
        coordinator_present = scan is not None and any(
            _process_key(record) == expected_coordinator
            for record in scan["watched"]
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
                    waited, _status = os.waitpid(
                        int(coordinator["pid"]), os.WNOHANG,
                    )
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
    eligible_holders = (
        captured_fd_holders
        if ownership.get("require_fd_only_holder")
        else captured_holders
    )
    namespace_holder = None if scan is None else _select_captured_namespace_holder(
        scan, eligible_holders, namespace,
    )
    if holders and namespace_holder is None:
        errors.append("no live namespace holder matches the complete captured identity")

    def holder_context() -> _NamespaceHolderCommandContext:
        assert namespace_holder is not None
        return _NamespaceHolderCommandContext(
            control_prefix, captured_mounts,
            shutil.which("nsenter") or "/usr/bin/nsenter",
            shutil.which("umount") or "/usr/bin/umount",
            str(supervisor._trusted_tools().helper_python),
        )

    def holder_command_payload(operation: str, mount: Path | None = None) -> str:
        assert namespace_holder is not None
        return _namespace_holder_command_payload(
            namespace_holder, namespace, operation, mount=mount,
            context=holder_context(),
        )

    def holder_mount_scan() -> tuple[tuple[Path, ...], bool] | None:
        if namespace_holder is None:
            return (), False
        scan_targets = tuple(sorted(captured_mounts))
        try:
            payload = holder_command_payload("scan")
            scan_stdin = _held_namespace_scan_stdin(namespace_holder, holder_context())
            argv = [
                "sudo", "-n", str(supervisor._trusted_tools().helper_python),
                "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE, payload,
            ]
        except (OSError, RuntimeError, TypeError, ValueError) as exc:
            errors.append("held mount namespace scan construction failed: " + type(exc).__name__)
            return None
        completed = command(argv, "scan exact held mount namespace", scan_stdin)
        if completed is None or completed.returncode != 0:
            if completed is not None:
                stderr = (
                    completed.stderr.decode("utf-8", "replace")
                    if isinstance(completed.stderr, bytes) else completed.stderr
                )
                errors.append(
                    "held mount namespace scan failed: category="
                    + _held_namespace_scan_child_returncode_category(completed.returncode)
                    + " stderr_tail="
                    + _sanitized_held_namespace_scan_stderr(stderr)
                )
            return None
        try:
            output = (
                completed.stdout.decode("utf-8")
                if isinstance(completed.stdout, bytes) else completed.stdout
            )
            diagnostic, mounts = _parse_held_namespace_diagnostic(
                output, namespace=namespace, holder=namespace_holder,
                control_prefix=control_prefix, targets=scan_targets,
            )
        except (TypeError, ValueError) as exc:
            errors.append("held mount namespace scan was malformed: " + str(exc)[:256])
            return None
        if diagnostic["root"]["matches"] is False:
            errors.append("held mount namespace root identity mismatched")
        held_namespace_diagnostics.append(
            "held mount namespace diagnostic="
            + json.dumps(diagnostic, sort_keys=True, separators=(",", ":"))
        )
        return mounts, diagnostic["root"]["matches"] is True

    held_scan = holder_mount_scan()
    held_mounts = None if held_scan is None else held_scan[0]
    if held_mounts is not None:
        captured_mounts.update(held_mounts)
    deferred_absent_unmounts = []
    unmount_mounts = (
        held_mounts if held_scan is not None and held_scan[1] else captured_mounts
    )
    for mount in sorted(
        unmount_mounts, key=lambda path: (len(path.parts), str(path)), reverse=True,
    ):
        if namespace_holder is None:
            argv = ["sudo", "-n", "umount", str(mount)]
        else:
            try:
                payload = holder_command_payload("unmount", mount)
                argv = [
                    "sudo", "-n", str(supervisor._trusted_tools().helper_python),
                    "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE, payload,
                ]
            except (OSError, RuntimeError, TypeError, ValueError) as exc:
                errors.append("namespace unmount construction failed: " + type(exc).__name__)
                continue
        completed = command(argv, f"unmount {mount}")
        if completed is None or completed.returncode == 0:
            continue
        diagnostic = (completed.stderr or completed.stdout).strip()
        normalized_diagnostic = diagnostic.lower()
        ambiguous_absence = _ambiguous_absent_unmount_diagnostic(
            diagnostic, mount,
        )
        if (
            "not mounted" in normalized_diagnostic
            or "no such file" in normalized_diagnostic
            or ambiguous_absence
        ):
            deferred_absent_unmounts.append(
                (mount, diagnostic[:512], ambiguous_absence)
            )
        else:
            errors.append(diagnostic[:512] or f"cannot unmount {mount}")

    if ownership.get("require_fd_only_holder"):
        teardown_exact_scope()
        post_scope_scan = scan_owned()
        namespace_holder = (
            None if post_scope_scan is None
            else _select_captured_namespace_holder(
                post_scope_scan, captured_fd_holders, namespace,
            )
        )
        remaining_scan = holder_mount_scan()
        if (
            namespace_holder is None
            or namespace_holder.get("holder_kind") != "fd"
            or post_scope_scan is None
            or post_scope_scan["current_holders"]
            or remaining_scan is None
            or not remaining_scan[1]
            or remaining_scan[0]
        ):
            errors.append("exact FD-only namespace mount ownership was not preserved")
    else:
        remaining_scan = holder_mount_scan()
        teardown_exact_scope()
    remaining_held_mounts = None if remaining_scan is None else remaining_scan[0]
    if remaining_held_mounts:
        errors.append(
            "owned mounts remain in held namespace: "
            + ", ".join(str(path) for path in remaining_held_mounts)
        )
    terminate_exact_coordinator()
    for holder in ownership.get("external_holders", ()):
        expected = _process_key(holder)
        holder_scan = scanner(
            selection=_RootProcSelection((int(holder["pid"]),)),
        )
        if any(_process_key(record) == expected for record in holder_scan["watched"]):
            try:
                argv = [
                    "sudo", "-n", str(supervisor._trusted_tools().helper_python),
                    "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE,
                    _external_holder_termination_payload(holder, namespace),
                ]
            except (OSError, RuntimeError, TypeError, ValueError) as exc:
                errors.append("external holder termination construction failed: " + type(exc).__name__)
                completed = None
            else:
                completed = command(argv, "terminate exact external namespace holder")
            if completed is not None and completed.returncode != 0:
                errors.append(
                    completed.stderr.strip()
                    or "external namespace holder termination failed"
                )
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

    _close_stalled_observation_fds(owned_fds, errors)
    verification_deadline = min(deadline, time.monotonic() + 8)
    final_leaks = ["verification did not run"]
    final_authoritative_mounts: tuple[Path, ...] | None = None
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
        final_authoritative_mounts = _exact_namespace_mounts(
            scan, namespace, control_prefix, tuple(captured_mounts)
        )
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
    if deferred_absent_unmounts:
        if not _deferred_absent_is_proven(
            deferred_absent_unmounts, remaining_scan, final_authoritative_mounts,
        ):
                errors.extend(
                    diagnostic or f"cannot unmount {mount}"
                    for mount, diagnostic, _ambiguous in deferred_absent_unmounts
                )
    if errors:
        errors.extend(held_namespace_diagnostics)
        raise AssertionError("; ".join(errors))
    return tuple(-1 for _descriptor in owned_fds)


def _fallback_stalled_observation_cleanup(
    ownership: dict[str, object], owned_fds: tuple[int, ...], *,
    runner=subprocess.run, scanner=_root_proc_scan,
) -> tuple[int, ...]:
    """Close lifecycle descriptors even when fail-closed cleanup raises."""
    try:
        return _fallback_stalled_observation_cleanup_impl(
            ownership, owned_fds, runner=runner, scanner=scanner,
        )
    finally:
        _close_stalled_observation_fds(owned_fds)


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


def _run_root_proc_scanner_descriptor_fault_fixture(
    tmp_path: Path, fault: str,
) -> tuple[subprocess.CompletedProcess[str], Path, Path]:
    """Run the embedded scanner against a procfs fixture with one FD read fault."""
    pid = 4242
    proc = tmp_path / "proc"
    pid_dir = proc / str(pid)
    fd_directory = pid_dir / "fd"
    namespace_directory = pid_dir / "ns"
    fd_directory.mkdir(parents=True)
    namespace_directory.mkdir()
    namespace_target = pid_dir / "namespace-target"
    namespace_target.write_text("namespace", encoding="ascii")
    namespace_path = namespace_directory / "mnt"
    namespace_path.symlink_to(namespace_target)
    descriptor_target = pid_dir / "descriptor-target"
    descriptor_target.write_text("original", encoding="ascii")
    replacement_target = pid_dir / "replacement-target"
    replacement_target.write_text("replacement", encoding="ascii")
    descriptor = fd_directory / "3"
    descriptor.symlink_to(descriptor_target)
    (pid_dir / "stat").write_text(
        f"{pid} (fixture) S {' '.join(['0'] * 20)}\n", encoding="ascii",
    )
    (pid_dir / "cmdline").write_bytes(b"fixture\0")
    (pid_dir / "wchan").write_text("fixture\n", encoding="ascii")
    (pid_dir / "mountinfo").write_text(
        "42 0 0:42 / / rw - tmpfs tmpfs rw\n", encoding="ascii",
    )
    probe = tmp_path / "descriptor-fault-probe"
    namespace_inode = namespace_path.stat().st_ino
    if fault == "enoent":
        descriptor_fault = f"""
    if value=={str(descriptor)!r}:
        pathlib.Path(value).unlink()
        pathlib.Path(value).symlink_to({str(replacement_target)!r})
        pathlib.Path({str(probe)!r}).write_text('reused',encoding='ascii')
        raise FileNotFoundError(2,'descriptor changed',value)
"""
    elif fault == "permission":
        descriptor_fault = f"""
    if value=={str(descriptor)!r}:
        pathlib.Path({str(probe)!r}).write_text('denied',encoding='ascii')
        raise PermissionError(13,'descriptor denied',value)
"""
    else:
        raise ValueError(f"unknown descriptor fixture fault: {fault}")
    source = _ROOT_PROC_SCANNER_SOURCE.replace(
        "proc=pathlib.Path('/proc')", f"proc=pathlib.Path({str(proc)!r})",
    ).replace(
        "self_pid=os.getpid()",
        f"""self_pid=os.getpid()
_fixture_readlink=os.readlink
def fixture_readlink(path):
    value=os.fspath(path)
    if value=={str(namespace_path)!r}:
        return 'mnt:[{namespace_inode}]'
{descriptor_fault}    return _fixture_readlink(path)
os.readlink=fixture_readlink""",
    )
    payload = {
        "cgroup": "", "namespace": None, "targets": [], "target_prefix": "",
        "watch_pids": [pid], "scope_only": True, "root_holders": [],
    }
    completed = subprocess.run(
        [sys.executable, "-I", "-S", "-c", source, json.dumps(payload)],
        capture_output=True, text=True, check=False, timeout=5,
    )
    return completed, descriptor, probe


def test_root_proc_scanner_source_skips_enoent_reused_descriptor_entry(
    tmp_path: Path,
) -> None:
    """An ENOENT descriptor snapshot race does not make the scanner abort."""
    completed, descriptor, probe = _run_root_proc_scanner_descriptor_fault_fixture(
        tmp_path, "enoent",
    )

    assert probe.read_text(encoding="ascii") == "reused"
    assert descriptor.is_symlink()
    assert completed.returncode == 0, completed.stderr


def test_root_proc_scanner_source_rejects_non_enoent_descriptor_errors(
    tmp_path: Path,
) -> None:
    """Descriptor errors other than an enumeration snapshot race stay fatal."""
    completed, _descriptor, probe = _run_root_proc_scanner_descriptor_fault_fixture(
        tmp_path, "permission",
    )

    assert probe.read_text(encoding="ascii") == "denied"
    assert completed.returncode == 2
    assert (
        "root proc scanner failed: RuntimeError: "
        "read descriptor: pid=4242 fd=3: PermissionError: "
    ) in completed.stderr


def test_held_namespace_child_sources_use_closed_marker_states() -> None:
    """Both standalone child programs declare every parent-accepted marker token."""
    for source, component in (
        (_NSENTER_REVALIDATOR_SOURCE, "revalidator"),
        (_NAMESPACE_MOUNT_SCANNER_SOURCE, "scanner"),
    ):
        assert "sys.excepthook=uncaught" in source
        assert f"COMPONENT='{component}'" in source
        for phase in _HELD_NAMESPACE_SCAN_FAILURE_COMPONENT_PHASES[component]:
            assert f"PHASE='{phase}'" in source
        for exception_class in _HELD_NAMESPACE_SCAN_FAILURE_EXCEPTION_CLASSES:
            assert f"'{exception_class}'" in source


def test_held_namespace_child_sources_emit_exact_markers_and_preserve_system_exit() -> None:
    """Uncaught children never relay traceback detail while explicit exits remain exact."""
    revalidator = subprocess.run(
        [sys.executable, "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE, "{}"],
        capture_output=True, text=True, check=False, timeout=5,
    )
    scanner = subprocess.run(
        [sys.executable, "-I", "-S", "-c", _NAMESPACE_MOUNT_SCANNER_SOURCE],
        capture_output=True, text=True, check=False, timeout=5,
    )
    static_exit = subprocess.run(
        [sys.executable, "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE],
        capture_output=True, text=True, check=False, timeout=5,
    )

    assert revalidator.stderr == _held_namespace_scan_failure_marker(
        "revalidator", "holder-validation", "keyerror",
    ) + "\n"
    assert scanner.stderr == _held_namespace_scan_failure_marker(
        "scanner", "transport", "runtimeerror",
    ) + "\n"
    assert "Traceback" not in revalidator.stderr + scanner.stderr
    assert static_exit.stderr == "diagnostic transport invariant\n"


def test_nsenter_revalidator_ignores_only_closed_disallowed_fds() -> None:
    """The fd-directory iterator's transient FD cannot weaken transport inheritance."""
    assert "import errno,fcntl" in _NSENTER_REVALIDATOR_SOURCE
    assert """for descriptor in opened:
            if descriptor>2 and descriptor not in allowed:
                try:
                    os.set_inheritable(descriptor,False)
                except OSError as error:
                    if error.errno==errno.EBADF:
                        continue
                    raise
        for descriptor in allowed:
            os.set_inheritable(descriptor,True)""" in _NSENTER_REVALIDATOR_SOURCE


def test_held_namespace_scan_uses_authenticated_sealed_fd_transport() -> None:
    """The complete scan inventory is stdin-fed and never becomes an argv item."""
    prefix = Path("/p")
    targets = {
        prefix / ("😀" * 253 + f"{index:03d}" + "x" * 6)
        for index in range(_HELD_NAMESPACE_DIAGNOSTIC_MAX_TARGETS)
    }
    assert all(len(str(target).encode("utf-8")) == 1024 for target in targets)
    context = _NamespaceHolderCommandContext(
        prefix, targets, "/usr/bin/nsenter", "/usr/bin/umount", sys.executable,
    )
    holder = {
        "holder_kind": "current", "pid": 1, "start_time": "1",
        "namespace": "mnt:[1]", "namespace_inode": 1,
    }

    scan_stdin = _held_namespace_scan_stdin(holder, context)
    control = _namespace_holder_command_payload(
        holder, {"link": "mnt:[1]", "inode": 1}, "scan", context=context,
    )

    assert len(scan_stdin) > 128 * 1024
    assert len(scan_stdin) <= _HELD_NAMESPACE_SCAN_PAYLOAD_MAX_BYTES
    assert _HELD_NAMESPACE_DIAGNOSTIC_MAX_BYTES >= (
        2 * _HELD_NAMESPACE_DIAGNOSTIC_MAX_TARGETS
        * _HELD_NAMESPACE_DIAGNOSTIC_MAX_PATH_BYTES
        * _HELD_NAMESPACE_JSON_ESCAPED_BYTES_PER_UTF8_BYTE
    )
    assert all(str(target).encode("utf-8") not in control.encode("utf-8") for target in targets)
    assert len(control.encode("utf-8")) < 128 * 1024
    control_record = json.loads(control)
    assert control_record["scan_bytes"] == len(scan_stdin)
    assert control_record["scan_sha256"] == hashlib.sha256(scan_stdin).hexdigest()
    assert "scan_payload" not in control_record


@pytest.mark.skipif(not sys.platform.startswith("linux"), reason="requires Linux memfd seals")
def test_held_namespace_scan_memfd_is_sealed_and_only_transport_fds_inherit(
    tmp_path: Path,
) -> None:
    """The revalidator preserves a sealed, non-argv max-cardinality inventory."""
    prefix = Path("/p")
    targets = {
        prefix / ("😀" * 253 + f"{index:03d}" + "x" * 6)
        for index in range(_HELD_NAMESPACE_DIAGNOSTIC_MAX_TARGETS)
    }
    namespace_path = Path("/proc/self/ns/mnt")
    namespace = {"link": os.readlink(namespace_path), "inode": namespace_path.stat().st_ino}
    stat_fields = Path("/proc/self/stat").read_text(encoding="ascii").rsplit(")", 1)[1].split()
    holder = {
        "holder_kind": "current", "pid": os.getpid(), "start_time": stat_fields[19],
        "namespace": namespace["link"], "namespace_inode": namespace["inode"],
    }
    capture = tmp_path / "capture-nsenter.py"
    capture.write_text(
        f"#!{sys.executable} -I\n"
        """import fcntl,hashlib,json,os,sys
argv=sys.argv
scan_ref=next(value for value in argv if value.startswith('/proc/self/fd/'))
scan_fd=int(scan_ref.rsplit('/',1)[1])
seals=fcntl.fcntl(scan_fd,fcntl.F_GET_SEALS)
try:
 os.write(scan_fd,b'x'); mutation='accepted'
except OSError: mutation='rejected'
inheritable=[]
for entry in os.listdir('/proc/self/fd'):
 try:
  descriptor=int(entry)
  if descriptor>2 and os.get_inheritable(descriptor): inheritable.append(descriptor)
 except OSError: pass
os.lseek(scan_fd,0,os.SEEK_SET)
data=os.read(scan_fd,2*1024*1024)
print(json.dumps({'argv':argv,'scan_fd':scan_fd,'seals':seals,'mutation':mutation,
 'inheritable':sorted(inheritable),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}))
""",
        encoding="utf-8",
    )
    capture.chmod(0o755)
    context = _NamespaceHolderCommandContext(
        prefix, targets, str(capture), "/usr/bin/umount", sys.executable,
    )
    scan_stdin = _held_namespace_scan_stdin(holder, context)
    control = _namespace_holder_command_payload(holder, namespace, "scan", context=context)

    completed = subprocess.run(
        [sys.executable, "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE, control],
        input=scan_stdin, capture_output=True, check=False, timeout=10,
    )

    assert completed.returncode == 0, completed.stderr.decode("utf-8", "replace")
    captured = json.loads(completed.stdout)
    import fcntl  # pylint: disable=import-outside-toplevel
    required = (
        getattr(fcntl, "F_SEAL_WRITE") | getattr(fcntl, "F_SEAL_GROW")
        | getattr(fcntl, "F_SEAL_SHRINK") | getattr(fcntl, "F_SEAL_SEAL")
    )
    assert captured["seals"] & required == required
    assert captured["mutation"] == "rejected"
    assert captured["bytes"] == len(scan_stdin)
    assert captured["sha256"] == hashlib.sha256(scan_stdin).hexdigest()
    def canonical_fd_reference(value: str, prefix: str) -> int:
        """Parse one fixed-role canonical FD argument."""
        assert value.startswith(prefix)
        descriptor = value.removeprefix(prefix)
        assert descriptor.isascii() and descriptor.isdecimal()
        number = int(descriptor)
        assert number > 2 and descriptor == str(number)
        return number

    argv = captured["argv"]
    assert len(argv) == 12
    assert argv[0] == str(capture)
    namespace_descriptor = canonical_fd_reference(argv[1], "--mount=/proc/self/fd/")
    root_descriptor = canonical_fd_reference(argv[2], "--root=/proc/self/fd/")
    assert argv[3:9] == [
        "--", sys.executable, "-I", "-S", "-c", _NAMESPACE_MOUNT_SCANNER_SOURCE,
    ]
    scan_descriptor = canonical_fd_reference(argv[9], "/proc/self/fd/")
    assert argv[10:] == [str(len(scan_stdin)), hashlib.sha256(scan_stdin).hexdigest()]
    assert captured["scan_fd"] == scan_descriptor
    expected_transport_descriptors = {
        namespace_descriptor, root_descriptor, scan_descriptor,
    }
    assert len(expected_transport_descriptors) == 3
    assert captured["inheritable"] == sorted(expected_transport_descriptors)
    assert all(str(target) not in captured["argv"] for target in targets)


@pytest.mark.skipif(
    not sys.platform.startswith("linux"), reason="requires Linux memfd transport",
)
@pytest.mark.parametrize(
    ("raw", "expected_category"),
    (
        (b"[]", b"pdd-held-namespace-failure:scanner:payload:runtimeerror"),
        (b'{"operation":"scan"}\n', b"pdd-held-namespace-failure:scanner:payload:runtimeerror"),
        (b"x" * (_HELD_NAMESPACE_SCAN_PAYLOAD_MAX_BYTES + 1),
         b"pdd-held-namespace-failure:scanner:transport:runtimeerror"),
    ),
    ids=("malformed", "trailing", "oversized"),
)
def test_namespace_scanner_rejects_exact_eof_trailing_oversized_and_malformed_frames(
    raw: bytes, expected_category: bytes,
) -> None:
    """The inner scanner reads a bounded exact frame instead of argv text."""
    descriptor = getattr(os, "memfd_create")(
        "pdd-scanner-frame", getattr(os, "MFD_CLOEXEC"),
    )
    try:
        os.write(descriptor, raw)
        os.lseek(descriptor, 0, os.SEEK_SET)
        completed = subprocess.run(
            [
                sys.executable, "-I", "-S", "-c", _NAMESPACE_MOUNT_SCANNER_SOURCE,
                f"/proc/self/fd/{descriptor}", str(len(raw)),
                hashlib.sha256(raw).hexdigest(),
            ],
            pass_fds=(descriptor,), capture_output=True, check=False, timeout=10,
        )
        assert completed.returncode != 0
        assert completed.stderr == expected_category + b"\n"
    finally:
        os.close(descriptor)


@pytest.mark.skipif(
    not sys.platform.startswith("linux"), reason="requires Linux memfd transport",
)
def test_namespace_scanner_rejects_truncated_canonical_frame() -> None:
    """A shorter FD than its authenticated canonical frame metadata fails closed."""
    canonical = json.dumps(
        {"expected_root": None, "operation": "scan", "prefix": "/p", "targets": []},
        sort_keys=True, separators=(",", ":"),
    ).encode("utf-8")
    descriptor = getattr(os, "memfd_create")(
        "pdd-truncated-scanner-frame", getattr(os, "MFD_CLOEXEC"),
    )
    try:
        os.write(descriptor, canonical[:-1])
        os.lseek(descriptor, 0, os.SEEK_SET)
        completed = subprocess.run(
            [
                sys.executable, "-I", "-S", "-c", _NAMESPACE_MOUNT_SCANNER_SOURCE,
                f"/proc/self/fd/{descriptor}", str(len(canonical)),
                hashlib.sha256(canonical).hexdigest(),
            ],
            pass_fds=(descriptor,), capture_output=True, check=False, timeout=10,
        )
        assert completed.returncode != 0
        assert completed.stderr == (
            b"pdd-held-namespace-failure:scanner:transport:runtimeerror\n"
        )
    finally:
        os.close(descriptor)


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not all(hasattr(os, name) for name in ("memfd_create", "MFD_ALLOW_SEALING")),
    reason="requires Linux sealed memfd transport",
)
def test_namespace_scanner_accepts_authenticated_frame_and_records_paths(
    tmp_path: Path,
) -> None:
    """A sealed canonical frame records existing and absent concrete paths."""
    import fcntl  # pylint: disable=import-outside-toplevel

    prefix = tmp_path / "scanner-paths"
    prefix.mkdir()
    existing = prefix / "existing"
    existing.write_text("present", encoding="utf-8")
    absent = prefix / "absent"
    targets = tuple(sorted((existing, absent)))
    namespace_path = Path("/proc/self/ns/mnt")
    namespace = {
        "link": os.readlink(namespace_path), "inode": namespace_path.stat().st_ino,
    }
    root_descriptor = os.open(
        "/proc/self/root", getattr(os, "O_PATH") | os.O_CLOEXEC,
    )
    try:
        root_metadata = os.fstat(root_descriptor)
        root_mount_ids = [
            line.partition(":")[2].strip()
            for line in Path(f"/proc/self/fdinfo/{root_descriptor}").read_text(
                encoding="ascii",
            ).splitlines()
            if line.startswith("mnt_id:")
        ]
    finally:
        os.close(root_descriptor)
    assert len(root_mount_ids) == 1 and root_mount_ids[0].isdigit()
    expected_root = {
        "device": root_metadata.st_dev, "inode": root_metadata.st_ino,
        "mode": root_metadata.st_mode, "mount_id": int(root_mount_ids[0]),
    }
    raw = json.dumps(
        {
            "expected_root": expected_root, "operation": "scan",
            "prefix": str(prefix), "targets": [str(path) for path in targets],
        }, sort_keys=True, separators=(",", ":"),
    ).encode("utf-8")
    descriptor = getattr(os, "memfd_create")(
        "pdd-scanner-success",
        getattr(os, "MFD_CLOEXEC") | getattr(os, "MFD_ALLOW_SEALING"),
    )
    try:
        os.write(descriptor, raw)
        fcntl.fcntl(
            descriptor, getattr(fcntl, "F_ADD_SEALS"),
            getattr(fcntl, "F_SEAL_WRITE") | getattr(fcntl, "F_SEAL_GROW")
            | getattr(fcntl, "F_SEAL_SHRINK") | getattr(fcntl, "F_SEAL_SEAL"),
        )
        os.lseek(descriptor, 0, os.SEEK_SET)
        completed = subprocess.run(
            [
                sys.executable, "-I", "-S", "-c", _NAMESPACE_MOUNT_SCANNER_SOURCE,
                f"/proc/self/fd/{descriptor}", str(len(raw)), hashlib.sha256(raw).hexdigest(),
            ],
            pass_fds=(descriptor,), capture_output=True, check=False, timeout=10,
        )
    finally:
        os.close(descriptor)

    assert completed.returncode == 0, completed.stderr.decode("utf-8", "replace")
    assert completed.stderr == b""
    diagnostic, _mounts = _parse_held_namespace_diagnostic(
        completed.stdout.decode("utf-8"), namespace=namespace,
        holder={
            "root_device": expected_root["device"],
            "root_inode": expected_root["inode"],
            "root_mode": expected_root["mode"],
            "root_mnt_id": expected_root["mount_id"],
        }, control_prefix=prefix, targets=targets,
    )
    records = diagnostic["paths"]
    assert records["prefix"]["stat"]["status"] == "ok"
    target_records = {record["path"]: record for record in records["targets"]}
    assert set(target_records) == {str(existing), str(absent)}
    assert target_records[str(existing)]["stat"]["status"] == "ok"
    assert target_records[str(absent)]["lstat"]["status"] == "error"
    assert target_records[str(absent)]["stat"]["status"] == "error"


def _valid_mountinfo_optional_fields(fields: tuple[str, ...]) -> bool:
    """Mirror the forward-compatible Linux mountinfo optional-field grammar."""
    for field in fields:
        tag, separator, value = field.partition(":")
        if (
            not tag or not tag.replace("_", "a").replace("-", "a").isalnum()
            or not tag[0].isalpha() or (separator and (not value or ":" in value))
        ):
            return False
        if tag in {"shared", "master", "propagate_from"} and (
            separator != ":" or not value.isdigit() or int(value) <= 0
        ):
            return False
    return True


def _unescape_documented_mountinfo_field(value: str) -> str:
    """Mirror the scanner's limited Linux mountinfo escape alphabet."""
    result = []
    index = 0
    escapes = {"040": " ", "011": "\t", "012": "\n", "134": "\\"}
    while index < len(value):
        if value[index] != "\\":
            result.append(value[index])
            index += 1
            continue
        escaped = value[index + 1:index + 4]
        if escaped not in escapes:
            raise ValueError("invalid mountinfo escape")
        result.append(escapes[escaped])
        index += 4
    return "".join(result)


def test_mountinfo_optional_field_grammar_accepts_unknown_fields_and_rejects_malformed() -> None:
    """Unknown well-formed tags remain forward compatible while known tags are strict."""
    assert _valid_mountinfo_optional_fields(
        ("shared:10", "master:11", "propagate_from:12", "unbindable")
    )
    assert _valid_mountinfo_optional_fields(("private", "vendor-tag:opaque", "unbindable"))
    for fields in (("shared:0",), ("1private",), ("unknown:",), ("shared:1:2",)):
        assert not _valid_mountinfo_optional_fields(fields)
    assert _unescape_documented_mountinfo_field(r"a\040b\011c\012d\134e") == "a b\tc\nd\\e"
    with pytest.raises(ValueError, match="invalid mountinfo escape"):
        _unescape_documented_mountinfo_field(r"a\041b")


def test_held_namespace_diagnostic_parser_is_strict_bounded_and_actionable() -> None:
    """The held-namespace envelope is portable, bounded, and fails closed."""
    prefix = Path("/tmp/pdd-scope-owned")
    targets = tuple(sorted(
        prefix / "binds" / f"{index:03d}-{'nested-' * 20}mount"
        for index in range(130)
    ))
    holder = {
        "root_device": 1, "root_inode": 2, "root_mode": 0o40755,
        "root_mnt_id": 42,
    }

    def metadata() -> dict[str, object]:
        return {"status": "ok", "device": 1, "inode": 2, "mode": 0o40700}

    def path_record(path: Path) -> dict[str, object]:
        return {
            "path": str(path), "exists": True,
            "lstat": metadata(), "stat": metadata(),
        }

    def mount(point: Path, mount_id: int) -> dict[str, object]:
        return {
            "mount_id": mount_id, "parent_id": 1, "root": "/",
            "mount_point": str(point), "major_minor": "0:42",
            "filesystem": "tmpfs", "source": "tmpfs",
            "options": {"mount": "rw", "super": "rw"}, "truncated": [],
        }

    diagnostic = {
        "schema": "pdd-held-namespace-diagnostic-v1", "operation": "scan",
        "prefix": str(prefix), "targets": [str(target) for target in targets],
        "mount_namespace": {"link": "mnt:[11]", "inode": 11},
        "root": {
            "link": "/", "expected": {
                "device": 1, "inode": 2, "mode": 0o40755, "mount_id": 42,
            }, "actual": {
                "device": 1, "inode": 2, "mode": 0o40755, "mount_id": 42,
            }, "matches": True,
        },
        "cwd": {"status": "ok", "path": "/"}, "paths": {
            "prefix": path_record(prefix), "target_count": len(targets),
            "targets": [path_record(target) for target in targets[:16]],
        },
        "mountinfo": {
            "mounts": [str(target) for target in targets], "exact_count": len(targets),
            "samples": [mount(target, index + 43) for index, target in enumerate(targets[:16])],
            "related": [],
        },
    }
    raw = json.dumps(diagnostic, sort_keys=True, separators=(",", ":"))
    parsed, mounts = _parse_held_namespace_diagnostic(
        raw, namespace={"link": "mnt:[11]", "inode": 11},
        holder=holder, control_prefix=prefix, targets=targets,
    )
    assert parsed == diagnostic
    assert mounts == targets

    stacked_inventory = (targets[0], targets[0], *targets[1:])
    stacked = json.loads(raw)
    stacked["mountinfo"] = {
        "mounts": [str(target) for target in stacked_inventory],
        "exact_count": len(stacked_inventory),
        "samples": [
            mount(target, index + 43)
            for index, target in enumerate(stacked_inventory[:16])
        ],
        "related": [],
    }
    _parsed, mounts = _parse_held_namespace_diagnostic(
        json.dumps(stacked), namespace={"link": "mnt:[11]", "inode": 11},
        holder=holder, control_prefix=prefix, targets=targets,
    )
    assert mounts == stacked_inventory

    root_mismatch = json.loads(raw)
    root_mismatch["root"]["actual"]["inode"] = 3
    root_mismatch["root"]["matches"] = False
    parsed, mounts = _parse_held_namespace_diagnostic(
        json.dumps(root_mismatch), namespace={"link": "mnt:[11]", "inode": 11},
        holder=holder, control_prefix=prefix, targets=targets,
    )
    assert parsed["root"]["matches"] is False and mounts == targets

    no_exact = json.loads(raw)
    no_exact["mountinfo"] = {
        "mounts": [], "exact_count": 0, "samples": [],
        "related": [mount(Path("/"), 44)],
    }
    _parsed, mounts = _parse_held_namespace_diagnostic(
        json.dumps(no_exact), namespace={"link": "mnt:[11]", "inode": 11},
        holder=holder, control_prefix=prefix, targets=targets,
    )
    assert mounts == ()

    malformed = []
    malformed.append("not-json")
    malformed.append(json.dumps(diagnostic | {"unexpected": True}))
    wrong_namespace = json.loads(raw)
    wrong_namespace["mount_namespace"]["inode"] = 12
    malformed.append(json.dumps(wrong_namespace))
    mixed_mounts = json.loads(raw)
    mixed_mounts["mountinfo"]["related"] = [mount(Path("/"), 999)]
    malformed.append(json.dumps(mixed_mounts))
    missing_related = json.loads(raw)
    missing_related["mountinfo"] = {
        "mounts": [], "exact_count": 0, "samples": [], "related": [],
    }
    malformed.append(json.dumps(missing_related))
    unordered_samples = json.loads(raw)
    unordered_samples["mountinfo"]["samples"] = list(reversed(
        unordered_samples["mountinfo"]["samples"]
    ))
    malformed.append(json.dumps(unordered_samples))
    for count in (len(targets) - 1, len(targets) + 1):
        inconsistent_count = json.loads(raw)
        inconsistent_count["mountinfo"]["exact_count"] = count
        malformed.append(json.dumps(inconsistent_count))
    unordered_duplicate_inventory = json.loads(json.dumps(stacked))
    unordered_duplicate_inventory["mountinfo"]["mounts"][:3] = [
        str(targets[0]), str(targets[1]), str(targets[0]),
    ]
    malformed.append(json.dumps(unordered_duplicate_inventory))
    mismatched_stacked_samples = json.loads(json.dumps(stacked))
    mismatched_stacked_samples["mountinfo"]["samples"][1]["mount_point"] = str(targets[1])
    malformed.append(json.dumps(mismatched_stacked_samples))
    duplicate_sample_id = json.loads(raw)
    duplicate_sample_id["mountinfo"]["samples"][1]["mount_id"] = (
        duplicate_sample_id["mountinfo"]["samples"][0]["mount_id"]
    )
    malformed.append(json.dumps(duplicate_sample_id))
    malformed.append("x" * (_HELD_NAMESPACE_DIAGNOSTIC_MAX_BYTES + 1))
    for value in malformed:
        with pytest.raises(ValueError, match="held namespace diagnostic"):
            _parse_held_namespace_diagnostic(
                value, namespace={"link": "mnt:[11]", "inode": 11},
                holder=holder, control_prefix=prefix, targets=targets,
            )


def _fallback_held_scan_diagnostic(
    prefix: Path, targets: tuple[Path, ...], holder: dict[str, object],
    mounts: tuple[Path, ...], *, root_matches: bool,
) -> str:
    """Build one authenticated held-root inventory for fallback cleanup tests."""
    expected_root = {
        "device": int(holder["root_device"]), "inode": int(holder["root_inode"]),
        "mode": int(holder["root_mode"]), "mount_id": int(holder["root_mnt_id"]),
    }
    actual_root = dict(expected_root)
    if not root_matches:
        actual_root["inode"] += 1

    def missing(path: Path) -> dict[str, object]:
        error = {"status": "error", "errno": 2}
        return {
            "path": str(path), "exists": False, "lstat": error, "stat": error,
        }

    def mount_record(path: Path, mount_id: int) -> dict[str, object]:
        return {
            "mount_id": mount_id, "parent_id": 1, "root": "/",
            "mount_point": str(path), "major_minor": "0:42",
            "filesystem": "tmpfs", "source": "tmpfs",
            "options": {"mount": "rw", "super": "rw"}, "truncated": [],
        }

    inventory = tuple(sorted(mounts))
    return json.dumps({
        "schema": "pdd-held-namespace-diagnostic-v1", "operation": "scan",
        "prefix": str(prefix), "targets": [str(path) for path in targets],
        "mount_namespace": {
            "link": str(holder["namespace"]), "inode": holder["namespace_inode"],
        },
        "root": {
            "link": "/", "expected": expected_root, "actual": actual_root,
            "matches": root_matches,
        },
        "cwd": {"status": "ok", "path": "/"},
        "paths": {
            "prefix": missing(prefix), "target_count": len(targets),
            "targets": [missing(path) for path in targets[:16]],
        },
        "mountinfo": {
            "mounts": [str(path) for path in inventory], "exact_count": len(inventory),
            "samples": [
                mount_record(path, 43 + index)
                for index, path in enumerate(inventory[:16])
            ],
            "related": [] if inventory else [mount_record(Path("/"), 99)],
        },
    }, sort_keys=True)


def _fallback_fd_holder() -> dict[str, object]:
    """Return the complete captured identity of an FD-only held namespace owner."""
    return {
        "holder_kind": "fd", "pid": 22, "start_time": "100", "fd": 9,
        "fd_path": "/proc/22/fd/9", "fd_link": "mnt:[11]", "fd_inode": 11,
        "root_fd": 10, "root_path": "/proc/22/fd/10", "root_device": 1,
        "root_inode": 2, "root_mode": 0o40755, "root_mnt_id": 42,
        "namespace": "mnt:[11]", "namespace_inode": 11,
    }


def test_fallback_fd_holder_accepts_root_valid_empty_held_inventory(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An authenticated empty FD-held inventory proves stale outer mounts absent."""
    prefix = tmp_path / "pdd-scope-owned"
    stale = prefix / "binds" / "stale"
    holder = _fallback_fd_holder()
    ownership = {
        "unit": "pdd-validator-test.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": prefix, "namespace": {"link": "mnt:[11]", "inode": 11},
        "namespace_holder": holder, "coordinator": {"pid": 1, "start_time": "1"},
        "mount_points": [stale], "require_fd_only_holder": True,
    }
    commands = []
    scans = 0
    monkeypatch.setattr(
        supervisor, "_trusted_tools", lambda: SimpleNamespace(helper_python=Path("/trusted/python")),
    )

    def scanner(**_kwargs):
        nonlocal scans
        scans += 1
        return {
            "watched": [], "identities": [], "cgroup_exists": False,
            "mount_holders": [], "current_holders": [],
            "fd_holders": [holder] if scans <= 2 else [],
        }

    def runner(argv, **kwargs):
        commands.append(argv)
        if "systemctl" in argv and "show" in argv:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        if _NSENTER_REVALIDATOR_SOURCE in argv:
            payload = json.loads(argv[-1])
            assert payload["operation"] == "scan"
            request = json.loads(kwargs["input"])
            return SimpleNamespace(
                returncode=0,
                stdout=_fallback_held_scan_diagnostic(
                    prefix, tuple(Path(path) for path in request["targets"]), holder, (),
                    root_matches=True,
                ),
                stderr="",
            )
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    assert _fallback_stalled_observation_cleanup(
        ownership, (), runner=runner, scanner=scanner,
    ) == ()
    operations = [
        json.loads(argv[-1])["operation"]
        for argv in commands if _NSENTER_REVALIDATOR_SOURCE in argv
    ]
    assert operations == ["scan", "scan"]


def test_fallback_fd_only_cleanup_prefers_captured_fd_holder(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """FD-only cleanup must not depend on a short-lived current holder."""
    prefix = tmp_path / "pdd-scope-owned"
    stale = prefix / "binds" / "stale"
    fd_holder = _fallback_fd_holder()
    current_holder = {
        "holder_kind": "current", "pid": 11, "start_time": "99",
        "namespace": "mnt:[11]", "namespace_inode": 11,
    }
    ownership = {
        "unit": "pdd-validator-test.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": prefix, "namespace": {"link": "mnt:[11]", "inode": 11},
        "namespace_holder": current_holder,
        "namespace_holders": [current_holder, fd_holder],
        "coordinator": {"pid": 1, "start_time": "1"},
        "mount_points": [stale], "require_fd_only_holder": True,
    }
    scans = 0
    selected_holders = []
    monkeypatch.setattr(
        supervisor, "_trusted_tools",
        lambda: SimpleNamespace(helper_python=Path("/trusted/python")),
    )

    def scanner(**_kwargs):
        nonlocal scans
        scans += 1
        return {
            "watched": [], "identities": [], "cgroup_exists": False,
            "mount_holders": [],
            "current_holders": [current_holder] if scans == 1 else [],
            "fd_holders": [fd_holder] if scans <= 2 else [],
        }

    def runner(argv, **kwargs):
        if "systemctl" in argv and "show" in argv:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        if _NSENTER_REVALIDATOR_SOURCE in argv:
            payload = json.loads(argv[-1])
            selected_holders.append(payload["holder"]["holder_kind"])
            assert payload["holder"] == fd_holder
            request = json.loads(kwargs["input"])
            return SimpleNamespace(
                returncode=0,
                stdout=_fallback_held_scan_diagnostic(
                    prefix, tuple(Path(path) for path in request["targets"]),
                    fd_holder, (), root_matches=True,
                ),
                stderr="",
            )
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    assert _fallback_stalled_observation_cleanup(
        ownership, (), runner=runner, scanner=scanner,
    ) == ()
    assert selected_holders == ["fd", "fd"]


def test_fallback_fd_holder_unmounts_stacked_nested_held_inventory_exactly(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Held-root cleanup preserves stacked layers and unmounts nested paths first."""
    prefix = tmp_path / "pdd-scope-owned"
    stale = prefix / "binds" / "stale"
    shared = prefix / "binds" / "shared"
    nested = shared / "nested"
    holder = _fallback_fd_holder()
    ownership = {
        "unit": "pdd-validator-test.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": prefix, "namespace": {"link": "mnt:[11]", "inode": 11},
        "namespace_holder": holder, "coordinator": {"pid": 1, "start_time": "1"},
        "mount_points": [stale], "require_fd_only_holder": True,
    }
    unmounts = []
    scans = 0
    held_inventories = iter(((shared, shared, nested), ()))
    monkeypatch.setattr(
        supervisor, "_trusted_tools", lambda: SimpleNamespace(helper_python=Path("/trusted/python")),
    )

    def scanner(**_kwargs):
        nonlocal scans
        scans += 1
        return {
            "watched": [], "identities": [], "cgroup_exists": False,
            "mount_holders": [], "current_holders": [],
            "fd_holders": [holder] if scans <= 2 else [],
        }

    def runner(argv, **kwargs):
        if "systemctl" in argv and "show" in argv:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        if _NSENTER_REVALIDATOR_SOURCE in argv:
            payload = json.loads(argv[-1])
            if payload["operation"] == "unmount":
                unmounts.append(payload["mount"])
                return SimpleNamespace(returncode=0, stdout="", stderr="")
            request = json.loads(kwargs["input"])
            return SimpleNamespace(
                returncode=0,
                stdout=_fallback_held_scan_diagnostic(
                    prefix, tuple(Path(path) for path in request["targets"]), holder,
                    next(held_inventories), root_matches=True,
                ),
                stderr="",
            )
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    assert _fallback_stalled_observation_cleanup(
        ownership, (), runner=runner, scanner=scanner,
    ) == ()
    assert unmounts == [str(nested), str(shared), str(shared)]


@pytest.mark.parametrize("mode", ("root-mismatch", "unavailable"))
def test_fallback_fd_holder_empty_untrusted_scan_keeps_stale_unmounts(
    tmp_path: Path, mode: str, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Root-invalid or unavailable scans cannot prove a stale mount is absent."""
    prefix = tmp_path / "pdd-scope-owned"
    stale = prefix / "binds" / "stale"
    holder = _fallback_fd_holder()
    ownership = {
        "unit": "pdd-validator-test.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": prefix, "namespace": {"link": "mnt:[11]", "inode": 11},
        "namespace_holder": holder, "coordinator": {"pid": 1, "start_time": "1"},
        "mount_points": [stale],
    }
    unmounts = []
    scans = 0
    monkeypatch.setattr(
        supervisor, "_trusted_tools", lambda: SimpleNamespace(helper_python=Path("/trusted/python")),
    )

    def scanner(**_kwargs):
        nonlocal scans
        scans += 1
        return {
            "watched": [], "identities": [], "cgroup_exists": False,
            "mount_holders": [], "current_holders": [],
            "fd_holders": [holder] if scans <= 2 else [],
        }

    def runner(argv, **kwargs):
        if "systemctl" in argv and "show" in argv:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        if _NSENTER_REVALIDATOR_SOURCE in argv:
            payload = json.loads(argv[-1])
            if payload["operation"] == "unmount":
                unmounts.append(payload["mount"])
                return SimpleNamespace(
                    returncode=1, stdout="",
                    stderr=f"umount: {stale}: no mount point specified.",
                )
            if mode == "unavailable":
                return SimpleNamespace(returncode=2, stdout="", stderr="scanner unavailable")
            request = json.loads(kwargs["input"])
            return SimpleNamespace(
                returncode=0,
                stdout=_fallback_held_scan_diagnostic(
                    prefix, tuple(Path(path) for path in request["targets"]), holder, (),
                    root_matches=False,
                ),
                stderr="",
            )
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    with pytest.raises(AssertionError, match="no mount point specified") as raised:
        _fallback_stalled_observation_cleanup(
            ownership, (), runner=runner, scanner=scanner,
        )
    assert unmounts == [str(stale)]
    if mode == "root-mismatch":
        assert "root identity mismatched" in str(raised.value)
    else:
        assert "held mount namespace scan failed" in str(raised.value)


@pytest.mark.parametrize("failure", ("construction", "nonzero", "malformed", "transport"))
def test_held_namespace_scan_failures_continue_cleanup_and_final_verification(
    tmp_path: Path, failure: str, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Failed diagnostic scans retain unmount and final-verification ownership."""
    prefix = tmp_path / "pdd-scope-owned"
    mount = prefix / "binds" / "writable"
    namespace = {"link": "mnt:[11]", "inode": 11}
    holder = {
        "holder_kind": "current", "pid": 22, "start_time": "100",
        "namespace": "mnt:[11]", "namespace_inode": 11,
    }
    ownership = {
        "unit": "pdd-validator-test.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": prefix, "namespace": namespace,
        "namespace_holder": holder, "coordinator": {"pid": 1, "start_time": "1"},
        "mount_points": [mount],
    }
    external = holder | {"pid": 33, "start_time": "101"}
    if failure == "transport":
        ownership["external_holders"] = [external]
    commands = []
    scans = 0
    monkeypatch.setattr(
        supervisor, "_trusted_tools", lambda: SimpleNamespace(helper_python=Path("/trusted/python")),
    )
    if failure == "construction":
        original_payload = _namespace_holder_command_payload

        def reject_scan_payload(*args, **kwargs):
            if args[2] == "scan":
                raise ValueError("injected diagnostic construction failure")
            return original_payload(*args, **kwargs)

        monkeypatch.setattr(sys.modules[__name__], "_namespace_holder_command_payload", reject_scan_payload)

    def scanner(**kwargs):
        nonlocal scans
        scans += 1
        selection = kwargs.get("selection")
        return {
                "watched": [external] if selection and selection.watch_pids == (33,) else [],
                "identities": [], "cgroup_exists": False,
                "mount_holders": [], "fd_holders": [],
            "current_holders": [holder] if scans <= 2 else [],
        }

    def runner(argv, **_kwargs):
        commands.append(argv)
        if "systemctl" in argv and "show" in argv:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        if _NSENTER_REVALIDATOR_SOURCE in argv:
            payload = json.loads(argv[-1])
            if payload["operation"] == "scan":
                if failure == "nonzero":
                    return SimpleNamespace(
                        returncode=2, stdout="",
                        stderr=(
                            "Traceback payload=/secret\n"
                            "pdd-held-namespace-failure:scanner:mountinfo:runtimeerror\n"
                        ),
                    )
                if failure == "transport":
                    return SimpleNamespace(
                        returncode=2, stdout=b"", stderr=(
                            b"pdd-held-namespace-failure:revalidator:scan-transport:runtimeerror\n"
                        ),
                    )
                return SimpleNamespace(returncode=0, stdout="[]", stderr="")
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    with pytest.raises(AssertionError) as raised:
        _fallback_stalled_observation_cleanup(
            ownership, (), runner=runner, scanner=scanner,
        )
    message = str(raised.value)
    operations = [
        json.loads(argv[-1])["operation"]
        for argv in commands if _NSENTER_REVALIDATOR_SOURCE in argv
    ]
    assert "unmount" in operations
    assert any("show" in argv for argv in commands)
    if failure == "nonzero":
        assert (
            "category=child-nonzero-returncode-2 stderr_tail="
            "pdd-held-namespace-failure:scanner:mountinfo:runtimeerror"
        ) in message
        assert "Traceback" not in message and "/secret" not in message
    elif failure == "malformed":
        assert "held mount namespace scan was malformed" in message
    elif failure == "transport":
        assert (
            "category=child-nonzero-returncode-2 stderr_tail="
            "pdd-held-namespace-failure:revalidator:scan-transport:runtimeerror"
        ) in message
        assert "terminate" in operations
    else:
        assert "held mount namespace scan construction failed" in message


@pytest.mark.parametrize(
    ("stderr", "later_present", "root_matches", "succeeds"),
    (
        ("not mounted", False, True, True),
        ("no such file", False, True, True),
        ("ambiguous-period", False, True, True),
        ("ambiguous-period", False, False, False),
        ("ambiguous-period", True, True, False),
    ),
    ids=("not-mounted", "enoent", "exact-root-empty", "root-mismatch", "nonempty"),
)
def test_proven_absent_unmount_failures_are_deferred_only_after_later_scan(
    tmp_path: Path, stderr: str, later_present: bool, root_matches: bool,
    succeeds: bool, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Only later namespace absence proof can discharge known stale-unmount output."""
    prefix = tmp_path / "pdd-scope-owned"
    target = prefix / "binds" / "writable"
    namespace = {"link": "mnt:[11]", "inode": 11}
    holder = _fallback_fd_holder()
    ownership = {
        "unit": "pdd-validator-test.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": prefix, "namespace": namespace,
        "namespace_holder": holder, "coordinator": {"pid": 1, "start_time": "1"},
        "mount_points": [target], "require_fd_only_holder": True,
    }
    monkeypatch.setattr(
        supervisor, "_trusted_tools", lambda: SimpleNamespace(helper_python=Path("/trusted/python")),
    )

    scan_outputs = [
        _fallback_held_scan_diagnostic(
            prefix, (target,), holder, (target,), root_matches=True,
        ),
        _fallback_held_scan_diagnostic(
            prefix, (target,), holder, (target,) if later_present else (),
            root_matches=root_matches,
        ),
    ]
    scans = 0

    def scanner(**_kwargs):
        nonlocal scans
        scans += 1
        return {
            "watched": [], "identities": [], "cgroup_exists": False,
            "mount_holders": [], "current_holders": [],
            "fd_holders": [holder] if scans <= 2 else [],
        }

    def runner(argv, **_kwargs):
        if "systemctl" in argv and "show" in argv:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        if _NSENTER_REVALIDATOR_SOURCE in argv:
            payload = json.loads(argv[-1])
            if payload["operation"] == "scan":
                return SimpleNamespace(returncode=0, stdout=scan_outputs.pop(0), stderr="")
            unmount_stderr = (
                f"umount: {target}: no mount point specified."
                if stderr == "ambiguous-period" else stderr
            )
            return SimpleNamespace(returncode=1, stdout="", stderr=unmount_stderr)
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    if succeeds:
        assert _fallback_stalled_observation_cleanup(
            ownership, (), runner=runner, scanner=scanner,
        ) == ()
    else:
        with pytest.raises(AssertionError, match="no mount point specified"):
            _fallback_stalled_observation_cleanup(
                ownership, (), runner=runner, scanner=scanner,
            )


def test_root_mismatched_scan_is_never_deferred_absence_proof() -> None:
    """A scan from a mismatched root cannot discharge an otherwise stale unmount."""
    deferred = [(Path("/p/binds/mount"), "not mounted", False)]

    assert not _deferred_absent_is_proven(deferred, ((), False), None)
    assert _deferred_absent_is_proven(deferred, ((), True), None)
    assert _deferred_absent_is_proven(deferred, ((), False), ())


def test_ambiguous_unmount_classification_is_bound_to_exact_mount() -> None:
    """Only exact C-locale util-linux output for this mount is ambiguous absence."""
    mount = Path("/p/binds/mount")
    assert _ambiguous_absent_unmount_diagnostic(
        "umount: /p/binds/mount: no mount point specified.", mount,
    )
    assert _ambiguous_absent_unmount_diagnostic(
        "umount: /p/binds/mount: no mount point specified", mount,
    )
    for diagnostic in (
        "no mount point specified.",
        "umount: /p/binds/other: no mount point specified.",
        "umount: /p/binds/mount: no mount point specified..",
        "umount: /p/binds/mount: not mounted",
        "prefix umount: /p/binds/mount: no mount point specified.",
    ):
        assert not _ambiguous_absent_unmount_diagnostic(diagnostic, mount)


def test_ambiguous_unmount_proof_classification_survives_diagnostic_truncation() -> None:
    """A long stored diagnostic cannot downgrade root-proof requirements."""
    mount = Path("/p/binds") / ("x" * 700)
    diagnostic = f"umount: {mount}: no mount point specified."
    deferred = [(mount, diagnostic[:512], True)]

    assert not _deferred_absent_is_proven(deferred, None, ())
    assert not _deferred_absent_is_proven(deferred, ((), False), ())
    assert _deferred_absent_is_proven(deferred, ((), True), None)


def test_fdinfo_mount_id_parser_normalizes_whitespace_and_rejects_ambiguity() -> None:
    """All fdinfo mount-ID protocols accept whitespace but require one positive value."""
    def parse(lines: list[str]) -> int:
        values = [
            line.partition(":")[2].strip()
            for line in lines if line.startswith("mnt_id:")
        ]
        if len(values) != 1 or not values[0].isdigit() or int(values[0]) <= 0:
            raise ValueError("invalid mount ID")
        return int(values[0])

    assert parse(["flags:\t0100000", "mnt_id:\t42"]) == 42
    assert parse(["mnt_id:  42  "]) == 42
    for lines in ([], ["mnt_id:"], ["mnt_id: 0"], ["mnt_id: 4", "mnt_id: 5"]):
        with pytest.raises(ValueError, match="invalid mount ID"):
            parse(lines)


def test_root_proc_scanner_forwards_scope_only_mode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Initial lifecycle capture can avoid an exhaustive host procfs walk."""
    captured = {}

    def scanner_run(argv, **_kwargs):
        captured.update(json.loads(argv[-1]))
        return SimpleNamespace(returncode=0, stdout="{}", stderr="")

    monkeypatch.setattr(
        supervisor, "_trusted_tools",
        lambda: SimpleNamespace(helper_python=Path("/trusted/python")),
    )
    monkeypatch.setattr(subprocess, "run", scanner_run)

    _root_proc_scan(
        cgroup=Path("/sys/fs/cgroup/pdd.scope"),
        selection=_RootProcSelection((123,), scope_only=True),
    )

    assert captured["scope_only"] is True


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
    exact |= {
        "root_fd": 8, "root_path": "/proc/22/fd/8",
        "root_device": 10, "root_inode": 20, "root_mode": 0o40755,
        "root_mnt_id": 30,
    }
    reused = exact | {"start_time": "101"}
    raced = exact | {"fd": 8}
    substituted_root = exact | {"root_mnt_id": 31}
    assert _select_captured_namespace_holder(
        {"current_holders": [], "fd_holders": [reused]}, (exact,), namespace,
    ) is None
    assert _select_captured_namespace_holder(
        {"current_holders": [], "fd_holders": [raced]}, (exact,), namespace,
    ) is None
    assert _select_captured_namespace_holder(
        {"current_holders": [], "fd_holders": [substituted_root]},
        (exact,), namespace,
    ) is None
    assert _select_captured_namespace_holder(
        {"current_holders": [], "fd_holders": [exact]}, (exact,), namespace,
    ) == exact
    assert _namespace_entry_path(exact, namespace) == "/proc/22/fd/7"
    assert _namespace_root_entry_path(exact) == "/proc/22/fd/8"
    with pytest.raises(ValueError, match="root descriptor path"):
        _namespace_root_entry_path(exact | {"root_path": "/proc/22/fd/9"})


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not hasattr(os, "pidfd_open"),
    reason="requires Linux pidfd namespace revalidation",
)
def test_namespace_holder_unmount_payload_and_nsenter_argv_are_exact(
    tmp_path: Path,
) -> None:
    """The held-root protocol sends one nonempty mount argument into nsenter."""
    raw = Path("/proc/self/stat").read_text(encoding="ascii")
    fields = raw[raw.rfind(")") + 2:].split()
    namespace_path = Path("/proc/self/ns/mnt")
    namespace = {
        "link": os.readlink(namespace_path), "inode": namespace_path.stat().st_ino,
    }
    namespace_descriptor = os.open(namespace_path, os.O_RDONLY | os.O_CLOEXEC)
    root_descriptor = os.open(
        "/proc/self/root", getattr(os, "O_PATH") | os.O_CLOEXEC,
    )
    try:
        root_metadata = os.fstat(root_descriptor)
        root_mount_ids = [
            line.partition(":")[2].strip() for line in Path(f"/proc/self/fdinfo/{root_descriptor}").read_text(
                encoding="ascii",
            ).splitlines() if line.startswith("mnt_id:")
        ]
        assert len(root_mount_ids) == 1 and root_mount_ids[0].isdigit() and int(root_mount_ids[0]) > 0
        root_mnt_id = int(root_mount_ids[0])
        holder = {
            "holder_kind": "fd", "pid": os.getpid(), "start_time": fields[19],
            "namespace": namespace["link"], "namespace_inode": namespace["inode"],
            "fd": namespace_descriptor,
            "fd_path": f"/proc/{os.getpid()}/fd/{namespace_descriptor}",
            "fd_link": os.readlink(f"/proc/self/fd/{namespace_descriptor}"),
            "fd_inode": os.fstat(namespace_descriptor).st_ino,
            "root_fd": root_descriptor,
            "root_path": f"/proc/{os.getpid()}/fd/{root_descriptor}",
            "root_device": root_metadata.st_dev, "root_inode": root_metadata.st_ino,
            "root_mode": root_metadata.st_mode, "root_mnt_id": root_mnt_id,
        }
        control = tmp_path / "pdd-scope-owned"
        mount = control / "binds" / "writable"
        capture = tmp_path / "capture-nsenter-argv"
        capture.write_text(
            "#!/usr/bin/env python3\nimport json,sys\nprint(json.dumps(sys.argv))\n",
            encoding="utf-8",
        )
        capture.chmod(0o755)

        payload = json.loads(_namespace_holder_command_payload(
            holder, namespace, "unmount", mount=mount,
            context=_NamespaceHolderCommandContext(
                control, {mount}, str(capture), "/bin/umount", sys.executable,
            ),
        ))

        assert payload == {
            "holder": holder, "namespace": namespace, "nsenter": str(capture),
            "umount": "/bin/umount", "python": sys.executable,
            "operation": "unmount", "mount": str(mount),
        }
        completed = subprocess.run(
            [sys.executable, "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE,
             json.dumps(payload, sort_keys=True, separators=(",", ":"))],
            capture_output=True, text=True, check=False, timeout=5,
        )
        assert completed.returncode == 0, completed.stderr
        argv = json.loads(completed.stdout)
        assert argv[0] == str(capture)
        assert argv[1].startswith("--mount=/proc/self/fd/")
        assert argv[2].startswith("--root=/proc/self/fd/")
        assert argv[3:] == ["--", "/bin/umount", str(mount)]
        payload["mount"] = ""
        rejected = subprocess.run(
            [sys.executable, "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE,
             json.dumps(payload, sort_keys=True, separators=(",", ":"))],
            capture_output=True, text=True, check=False, timeout=5,
        )
        assert rejected.returncode != 0
        assert rejected.stderr == _held_namespace_scan_failure_marker(
            "revalidator", "exec", "runtimeerror",
        ) + "\n"
        host_root = os.open("/", getattr(os, "O_PATH") | os.O_CLOEXEC)
        try:
            host_metadata = os.fstat(host_root)
            assert (host_metadata.st_dev, host_metadata.st_ino) == (
                root_metadata.st_dev, root_metadata.st_ino,
            )
            substituted = holder | {
                "root_fd": host_root,
                "root_path": f"/proc/{os.getpid()}/fd/{host_root}",
                "root_device": host_metadata.st_dev,
                "root_inode": host_metadata.st_ino,
                "root_mode": host_metadata.st_mode,
                "root_mnt_id": root_mnt_id + 1,
            }
            substitution = json.loads(_namespace_holder_command_payload(
                substituted, namespace, "unmount", mount=mount,
                context=_NamespaceHolderCommandContext(
                    control, {mount}, str(capture), "/bin/umount", sys.executable,
                ),
            ))
            rejected = subprocess.run(
                [sys.executable, "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE,
                 json.dumps(substitution, sort_keys=True, separators=(",", ":"))],
                capture_output=True, text=True, check=False, timeout=5,
            )
            assert rejected.returncode != 0
            assert rejected.stderr == _held_namespace_scan_failure_marker(
                "revalidator", "root-pin", "runtimeerror",
            ) + "\n"
        finally:
            os.close(host_root)
    finally:
        os.close(root_descriptor)
        os.close(namespace_descriptor)


def test_external_holder_termination_requires_complete_pidfd_identity() -> None:
    """Termination binds canonical complete holder data to a pidfd, never a PID."""
    namespace = {"link": "mnt:[11]", "inode": 11}
    holder = {
        "holder_kind": "fd", "pid": 2_147_483_647, "start_time": "100",
        "namespace": "mnt:[1]", "namespace_inode": 1,
        "fd": 7, "fd_path": "/proc/2147483647/fd/7",
        "fd_link": "mnt:[11]", "fd_inode": 11,
    }

    expected = {
        "holder": holder, "namespace": namespace, "operation": "terminate",
    }
    payload = _external_holder_termination_payload(holder, namespace)

    assert payload == json.dumps(expected, sort_keys=True, separators=(",", ":"))
    assert payload == (
        '{"holder":{"fd":7,"fd_inode":11,"fd_link":"mnt:[11]",'
        '"fd_path":"/proc/2147483647/fd/7","holder_kind":"fd",'
        '"namespace":"mnt:[1]","namespace_inode":1,"pid":2147483647,'
        '"start_time":"100"},"namespace":{"inode":11,"link":"mnt:[11]"},'
        '"operation":"terminate"}'
    )
    accepted = subprocess.run(
        [sys.executable, "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE, payload],
        capture_output=True, text=True, check=False, timeout=5,
    )
    assert "diagnostic transport invariant" not in accepted.stderr
    noncanonical = json.dumps(expected, sort_keys=True)
    assert noncanonical != payload
    rejected = subprocess.run(
        [sys.executable, "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE, noncanonical],
        capture_output=True, text=True, check=False, timeout=5,
    )
    assert rejected.returncode != 0
    assert rejected.stderr == "diagnostic transport invariant\n"
    with pytest.raises(ValueError, match="descriptor"):
        _external_holder_termination_payload(
            {key: value for key, value in holder.items() if key != "fd_path"},
            namespace,
        )
    assert "os.kill(" not in _NSENTER_REVALIDATOR_SOURCE
    assert _NSENTER_REVALIDATOR_SOURCE.index("os.pidfd_open") < (
        _NSENTER_REVALIDATOR_SOURCE.index("identity()!=start_time")
    )
    assert "signal.pidfd_send_signal" in _NSENTER_REVALIDATOR_SOURCE


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not hasattr(os, "pidfd_open")
    or not hasattr(signal, "pidfd_send_signal"),
    reason="requires Linux pidfd signaling",
)
def test_external_holder_pidfd_rejects_reuse_then_terminates_and_reaps() -> None:
    """A stale identity is untouched; the exact pidfd identity is reaped."""

    def fork_holder() -> int:
        child = os.fork()
        if child == 0:
            signal.pause()
            os._exit(125)
        return child

    def current_holder(pid: int) -> tuple[dict[str, object], dict[str, object]]:
        raw = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
        fields = raw[raw.rfind(")") + 2:].split()
        namespace_path = Path(f"/proc/{pid}/ns/mnt")
        link = os.readlink(namespace_path)
        inode = namespace_path.stat().st_ino
        namespace = {"link": link, "inode": inode}
        return ({
            "holder_kind": "current", "pid": pid, "start_time": fields[19],
            "namespace": link, "namespace_inode": inode,
        }, namespace)

    def invoke(holder: dict[str, object], namespace: dict[str, object]):
        return subprocess.run(
            [sys.executable, "-I", "-S", "-c", _NSENTER_REVALIDATOR_SOURCE,
             _external_holder_termination_payload(holder, namespace)],
            capture_output=True, text=True, check=False, timeout=5,
        )

    stale_pid = fork_holder()
    exact_pid = fork_holder()
    try:
        stale, stale_namespace = current_holder(stale_pid)
        stale["start_time"] = str(int(stale["start_time"]) + 1)
        rejected = invoke(stale, stale_namespace)
        assert rejected.returncode != 0
        assert os.waitpid(stale_pid, os.WNOHANG) == (0, 0)

        exact, exact_namespace = current_holder(exact_pid)
        terminated = invoke(exact, exact_namespace)
        assert terminated.returncode == 0, terminated.stderr
        waited, status = os.waitpid(exact_pid, 0)
        assert waited == exact_pid and os.waitstatus_to_exitcode(status) == -signal.SIGTERM
        exact_pid = -1
    finally:
        for pid in (stale_pid, exact_pid):
            if pid <= 0:
                continue
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                os.waitpid(pid, 0)
            except ChildProcessError:
                pass


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
    coordinator_scan_observed_open_fd = False

    def runner(*args, **_kwargs):
        commands.append(args[0])
        if args[0][2:4] == ["systemctl", "stop"]:
            return SimpleNamespace(returncode=5, stdout="", stderr="already removed")
        if args[0][2:4] == ["systemctl", "show"]:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    coordinator_record = {"pid": coordinator, "start_time": "unit-test"}
    selections = []

    def scanner(
        *, cgroup=None, namespace=None, targets=(), target_prefix=None,
        selection=_RootProcSelection(),
    ):
        del cgroup, namespace, targets, target_prefix
        nonlocal calls, coordinator_scan_observed_open_fd
        calls += 1
        selections.append(selection)
        if calls <= 3:
            if calls == 1:
                os.fstat(read_fd)
                coordinator_scan_observed_open_fd = True
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
    assert coordinator_scan_observed_open_fd
    with pytest.raises(ChildProcessError):
        os.waitpid(coordinator, os.WNOHANG)
    assert selections and selections[0] == _RootProcSelection((coordinator,))
    assert commands == [
        ["sudo", "-n", "umount",
         str(tmp_path / "pdd-scope-owned" / "binds" / "nested")],
        ["sudo", "-n", "systemctl", "kill", "--kill-whom=all",
         "--signal=SIGKILL", "pdd-validator-test.scope"],
        ["sudo", "-n", "systemctl", "stop", "pdd-validator-test.scope"],
        ["sudo", "-n", "systemctl", "reset-failed", "pdd-validator-test.scope"],
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


def test_stalled_cleanup_closes_observer_fds_after_teardown_exception(
    tmp_path: Path,
) -> None:
    """Transferred descriptors close even when exact teardown raises unexpectedly."""
    read_fd, write_fd = os.pipe()
    os.close(write_fd)
    ownership = {
        "unit": "pdd-validator-action-error.scope",
        "cgroup": tmp_path / "cgroup",
        "control_prefix": tmp_path / "pdd-scope-owned",
        "namespace": {"link": "mnt:[1]", "inode": 1},
        "namespace_holder": {
            "holder_kind": "current", "pid": 999999,
            "start_time": "100", "namespace": "mnt:[1]",
            "namespace_inode": 1,
        },
        "coordinator": {"pid": 999999, "start_time": "100"},
        "mount_points": [],
    }

    def runner(_argv, **_kwargs):
        os.fstat(read_fd)
        raise RuntimeError("injected teardown failure")

    with pytest.raises(RuntimeError, match="injected teardown failure"):
        _fallback_stalled_observation_cleanup(
            ownership, (read_fd,), runner=runner,
        )
    with pytest.raises(OSError):
        os.fstat(read_fd)


def test_stalled_cleanup_unmounts_before_coordinator_reap_deletes_paths(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Held mounts are removed before coordinator cleanup deletes their paths."""
    prefix = tmp_path / "pdd-scope-owned"
    mount = prefix / "binds" / "writable"
    mount.mkdir(parents=True)
    namespace = {"link": "mnt:[11]", "inode": 11}
    coordinator = {
        "holder_kind": "current", "pid": 999999, "start_time": "100",
        "namespace": "mnt:[11]", "namespace_inode": 11,
    }
    ownership = {
        "unit": "pdd-validator-order.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": prefix, "namespace": namespace,
        "namespace_holder": coordinator, "coordinator": coordinator,
        "mount_points": [mount],
    }
    read_fd, write_fd = os.pipe()
    os.close(write_fd)
    coordinator_alive = True
    mounted = True
    events = []

    monkeypatch.setattr(
        supervisor, "_trusted_tools",
        lambda: SimpleNamespace(helper_python=Path("/trusted/python")),
    )

    def scanner(**_kwargs):
        records = [coordinator] if coordinator_alive else []
        return {
            "watched": records, "identities": records,
            "current_holders": records, "fd_holders": [],
            "mount_holders": [], "cgroup_exists": False,
        }

    def runner(argv, **_kwargs):
        nonlocal mounted
        if "systemctl" in argv and "show" in argv:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        if _NSENTER_REVALIDATOR_SOURCE in argv:
            operation = json.loads(argv[-1])["operation"]
            assert coordinator_alive
            assert mount.exists()
            os.fstat(read_fd)
            events.append(operation)
            if operation == "unmount":
                mounted = False
                return SimpleNamespace(returncode=0, stdout="", stderr="")
            return SimpleNamespace(
                returncode=0, stdout="mounted" if mounted else "absent", stderr="",
            )
        if "umount" in argv:
            events.append("plain-unmount-after-reap")
            return SimpleNamespace(returncode=32, stdout="", stderr="no such file")
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    def terminate(pid: int, sent: signal.Signals) -> None:
        nonlocal coordinator_alive
        assert pid == coordinator["pid"] and sent == signal.SIGTERM
        assert mounted is False
        coordinator_alive = False
        shutil.rmtree(prefix)
        events.append("coordinator-reaped-paths")

    def waitpid(pid: int, _options: int) -> tuple[int, int]:
        assert pid == coordinator["pid"]
        return (0, 0) if coordinator_alive else (pid, 0)

    def parse_diagnostic(raw: str, **_kwargs):
        return ({"root": {"matches": True}}, (mount,) if raw == "mounted" else ())

    monkeypatch.setattr(os, "kill", terminate)
    monkeypatch.setattr(os, "waitpid", waitpid)
    monkeypatch.setattr(
        sys.modules[__name__], "_parse_held_namespace_diagnostic", parse_diagnostic,
    )

    assert _fallback_stalled_observation_cleanup(
        ownership, (read_fd,), runner=runner, scanner=scanner,
    ) == (-1,)
    assert events == ["scan", "unmount", "scan", "coordinator-reaped-paths"]
    with pytest.raises(OSError):
        os.fstat(read_fd)


def test_stalled_cleanup_unmounts_before_destructive_scope_actions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Authenticated held cleanup finishes before systemd can delete backing paths."""
    prefix = tmp_path / "pdd-scope-owned"
    mount = prefix / "binds" / "writable"
    mount.mkdir(parents=True)
    namespace = {"link": "mnt:[11]", "inode": 11}
    coordinator = {
        "holder_kind": "current", "pid": 999999, "start_time": "100",
        "namespace": "mnt:[11]", "namespace_inode": 11,
    }
    ownership = {
        "unit": "pdd-validator-scope-order.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": prefix, "namespace": namespace,
        "namespace_holder": coordinator, "coordinator": coordinator,
        "mount_points": [mount],
    }
    read_fd, write_fd = os.pipe()
    os.close(write_fd)
    coordinator_alive = True
    mounted = True
    held_cleanup_complete = False
    events = []

    monkeypatch.setattr(
        supervisor, "_trusted_tools",
        lambda: SimpleNamespace(helper_python=Path("/trusted/python")),
    )

    def scanner(**_kwargs):
        records = [coordinator] if coordinator_alive else []
        return {
            "watched": records, "identities": records,
            "current_holders": records, "fd_holders": [],
            "mount_holders": [], "cgroup_exists": False,
        }

    def runner(argv, **_kwargs):
        nonlocal held_cleanup_complete, mounted
        if "systemctl" in argv and "show" in argv:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        if "systemctl" in argv:
            action = argv[3]
            events.append(f"scope-{action}")
            if action == "kill":
                mounted = False
                shutil.rmtree(prefix)
                assert held_cleanup_complete
            return SimpleNamespace(returncode=0, stdout="", stderr="")
        if _NSENTER_REVALIDATOR_SOURCE in argv:
            operation = json.loads(argv[-1])["operation"]
            assert coordinator_alive
            assert mount.exists()
            os.fstat(read_fd)
            events.append(operation)
            if operation == "unmount":
                mounted = False
                return SimpleNamespace(returncode=0, stdout="", stderr="")
            if mounted:
                return SimpleNamespace(returncode=0, stdout="mounted", stderr="")
            held_cleanup_complete = True
            return SimpleNamespace(returncode=0, stdout="absent", stderr="")
        raise AssertionError(f"unexpected command: {argv}")

    def terminate(pid: int, sent: signal.Signals) -> None:
        nonlocal coordinator_alive
        assert pid == coordinator["pid"] and sent == signal.SIGTERM
        assert held_cleanup_complete and not mounted and not prefix.exists()
        coordinator_alive = False
        events.append("coordinator-reaped")

    def waitpid(pid: int, _options: int) -> tuple[int, int]:
        assert pid == coordinator["pid"]
        return (0, 0) if coordinator_alive else (pid, 0)

    def parse_diagnostic(raw: str, **_kwargs):
        return ({"root": {"matches": True}}, (mount,) if raw == "mounted" else ())

    monkeypatch.setattr(os, "kill", terminate)
    monkeypatch.setattr(os, "waitpid", waitpid)
    monkeypatch.setattr(
        sys.modules[__name__], "_parse_held_namespace_diagnostic", parse_diagnostic,
    )

    assert _fallback_stalled_observation_cleanup(
        ownership, (read_fd,), runner=runner, scanner=scanner,
    ) == (-1,)
    assert events == [
        "scan", "unmount", "scan", "scope-kill", "scope-stop",
        "scope-reset-failed", "coordinator-reaped",
    ]
    with pytest.raises(OSError):
        os.fstat(read_fd)


def test_stalled_cleanup_uses_captured_fd_holder_before_and_after_scope_teardown(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A captured external FD holder authenticates the complete cleanup lifecycle."""
    prefix = tmp_path / "pdd-scope-owned"
    mount = prefix / "binds" / "writable"
    mount.mkdir(parents=True)
    namespace = {"link": "mnt:[11]", "inode": 11}
    coordinator = {"pid": 777777, "start_time": "100"}
    current_holder = {
        "holder_kind": "current", "pid": 999999, "start_time": "101",
        "namespace": "mnt:[11]", "namespace_inode": 11,
    }
    fd_holder = {
        "holder_kind": "fd", "pid": 888888, "start_time": "102", "fd": 73,
        "fd_path": "/proc/888888/fd/73", "fd_link": "mnt:[11]", "fd_inode": 11,
        "root_fd": 74, "root_path": "/proc/888888/fd/74",
        "root_device": 1, "root_inode": 2, "root_mode": 0o40755,
        "root_mnt_id": 42, "namespace": "mnt:[11]", "namespace_inode": 11,
    }
    ownership = {
        "unit": "pdd-validator-holder-switch.scope", "cgroup": tmp_path / "cgroup",
        "control_prefix": prefix, "namespace": namespace,
        "namespace_holder": fd_holder,
        "namespace_holders": [current_holder, fd_holder],
        "coordinator": coordinator, "mount_points": [mount],
        "external_holders": [fd_holder], "require_fd_only_holder": True,
    }
    read_fd, write_fd = os.pipe()
    os.close(write_fd)
    coordinator_alive = True
    fd_holder_alive = True
    current_holder_alive = True
    scope_torn_down = False
    mounted = True
    events = []

    monkeypatch.setattr(
        supervisor, "_trusted_tools",
        lambda: SimpleNamespace(helper_python=Path("/trusted/python")),
    )

    def scanner(**_kwargs):
        identities = []
        watched = []
        if coordinator_alive:
            identities.append(coordinator)
            watched.append(coordinator)
        if current_holder_alive:
            identities.append(current_holder)
            watched.append(current_holder)
        if fd_holder_alive:
            identities.append(fd_holder)
            watched.append(fd_holder)
        return {
            "watched": watched, "identities": identities,
            "current_holders": [current_holder] if current_holder_alive else [],
            "fd_holders": [fd_holder] if fd_holder_alive else [],
            "mount_holders": [], "cgroup_exists": False,
        }

    def runner(argv, **_kwargs):
        nonlocal current_holder_alive, fd_holder_alive, mounted, scope_torn_down
        if "systemctl" in argv and "show" in argv:
            return SimpleNamespace(returncode=0, stdout="not-found\n", stderr="")
        if "systemctl" in argv:
            events.append(f"scope-{argv[3]}")
            if argv[3] == "kill":
                scope_torn_down = True
                current_holder_alive = False
            return SimpleNamespace(returncode=0, stdout="", stderr="")
        if _NSENTER_REVALIDATOR_SOURCE in argv:
            payload = json.loads(argv[-1])
            operation = payload["operation"]
            holder_kind = payload["holder"]["holder_kind"]
            events.append(f"{holder_kind}-{operation}")
            os.fstat(read_fd)
            if operation == "terminate":
                assert holder_kind == "fd" and scope_torn_down
                fd_holder_alive = False
                return SimpleNamespace(returncode=0, stdout="", stderr="")
            if holder_kind == "current":
                assert current_holder_alive and not scope_torn_down
            else:
                assert holder_kind == "fd" and fd_holder_alive
            if operation == "unmount":
                mounted = False
                return SimpleNamespace(returncode=0, stdout="", stderr="")
            return SimpleNamespace(
                returncode=0, stdout="mounted" if mounted else "absent", stderr="",
            )
        raise AssertionError(f"unexpected command: {argv}")

    def terminate(pid: int, sent: signal.Signals) -> None:
        nonlocal coordinator_alive
        assert pid == coordinator["pid"] and sent == signal.SIGTERM
        assert scope_torn_down and not current_holder_alive and not mounted
        coordinator_alive = False
        events.append("coordinator-reaped")

    def waitpid(pid: int, _options: int) -> tuple[int, int]:
        if pid == coordinator["pid"]:
            return (0, 0) if coordinator_alive else (pid, 0)
        assert pid == fd_holder["pid"]
        return (0, 0) if fd_holder_alive else (pid, 0)

    def parse_diagnostic(raw: str, **_kwargs):
        return ({"root": {"matches": True}}, (mount,) if raw == "mounted" else ())

    monkeypatch.setattr(os, "kill", terminate)
    monkeypatch.setattr(os, "waitpid", waitpid)
    monkeypatch.setattr(
        sys.modules[__name__], "_parse_held_namespace_diagnostic", parse_diagnostic,
    )

    assert _fallback_stalled_observation_cleanup(
        ownership, (read_fd,), runner=runner, scanner=scanner,
    ) == (-1,)
    assert events == [
        "fd-scan", "fd-unmount", "scope-kill", "scope-stop",
        "scope-reset-failed", "fd-scan", "coordinator-reaped", "fd-terminate",
    ]
    with pytest.raises(OSError):
        os.fstat(read_fd)


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
                selection=_RootProcSelection(watch_pids, scope_only=True),
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
                    target_prefix=target_prefix,
                    selection=_RootProcSelection(watch_pids, scope_only=True),
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
            scan = _root_proc_scan(selection=_RootProcSelection((pid,)))
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
        monkeypatch.setattr(supervisor, "_fresh_supervision_token", lambda: token)
        monkeypatch.setattr(supervisor.tempfile, "tempdir", str(tmp_path))
        scratch = tmp_path / "stalled-candidate-scratch"
        scratch.mkdir()
        read_fd, write_fd = os.pipe()
        _saturate_descriptor_pipe(write_fd)
        lifecycle_ready_read, lifecycle_ready_write = os.pipe()
        lifecycle_release_read, lifecycle_release_write = os.pipe()
        report = tmp_path / "stalled-observation-reader.json"
        program = (
            "import os;data=b'x'*262144;offset=0\n"
            "while offset<len(data): offset+=os.write(198,data[offset:])"
        )
        descriptor_result = supervisor._descriptor_result

        def gated_descriptor_result(*args, **kwargs):
            result = descriptor_result(*args, **kwargs)
            return _hold_validated_descriptor_result(
                result, lifecycle_ready_write, lifecycle_release_read,
            )

        monkeypatch.setattr(supervisor, "_descriptor_result", gated_descriptor_result)
        coordinator = os.fork()
        if coordinator == 0:
            os.close(read_fd)
            os.close(lifecycle_ready_read)
            os.close(lifecycle_release_write)
            exit_status = 0
            try:
                result, surviving = run_supervised(
                    [sys.executable, "-c", program], cwd=scratch, timeout=10,
                    env=candidate_environment, writable_roots=(scratch,),
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
                os.close(lifecycle_ready_write)
                os.close(lifecycle_release_read)
            os._exit(exit_status)
        os.close(write_fd)
        write_fd = -1
        os.close(lifecycle_ready_write)
        lifecycle_ready_write = -1
        os.close(lifecycle_release_read)
        lifecycle_release_read = -1
        details = None
        fallback_done = False
        external_reaper = None
        try:
            ready, _, _ = select.select([lifecycle_ready_read], [], [], 10)
            assert ready, "validated descriptor result was not observable"
            assert os.read(lifecycle_ready_read, 1) == b"R"

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
                scan = _root_proc_scan(
                    selection=_RootProcSelection(
                        (coordinator,), scope_only=True,
                    ),
                )
                if case == "initial-scan-failure":
                    raise AssertionError("injected initial scan failure")
                return scan

            def early_failure_cleanup() -> None:
                nonlocal details, read_fd, write_fd, fallback_done
                nonlocal lifecycle_ready_read, lifecycle_release_write
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
                    owned_fds = (
                        read_fd, write_fd, lifecycle_ready_read,
                        lifecycle_release_write,
                    )
                    read_fd = write_fd = -1
                    lifecycle_ready_read = lifecycle_release_write = -1
                    assert _fallback_stalled_observation_cleanup(
                        details, owned_fds,
                    ) == (-1,) * len(owned_fds)
                finally:
                    fallback_done = True

            if case in {"initial-scan-failure", "initial-watched-assertion-failure"}:
                with pytest.raises(AssertionError, match="injected initial"):
                    _run_stalled_observation_setup(
                        initial_scan, assert_initial_coordinator, early_failure_cleanup,
                    )
                assert fallback_done and details is not None
                assert read_fd == -1 and write_fd == -1
                assert lifecycle_ready_read == -1
                assert lifecycle_release_write == -1
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
import json,os,pathlib,signal,sys
target=json.loads(sys.argv[1])
pid=target.get('pid'); start_time=target.get('start_time')
namespace=target.get('namespace')
if (type(pid) is not int or pid<=0 or type(start_time) is not str or
        not start_time.isdigit() or type(namespace) is not dict or
        set(namespace)!={'link','inode'} or type(namespace['link']) is not str or
        type(namespace['inode']) is not int or namespace['inode']<=0):
    raise SystemExit('invalid target identity')
try: target_pidfd=os.pidfd_open(pid,0)
except ProcessLookupError: raise SystemExit('target exited')
proc=pathlib.Path('/proc')/str(pid)
def identity():
    raw=(proc/'stat').read_text(encoding='ascii')
    closing=raw.rfind(')'); fields=raw[closing+2:].split()
    if closing<2 or len(fields)<=19 or not fields[19].isdigit(): raise RuntimeError('invalid target stat')
    return fields[19]
def validate_target():
    namespace_path=proc/'ns'/'mnt'
    if (identity()!=start_time or os.readlink(namespace_path)!=namespace['link'] or
            namespace_path.stat().st_ino!=namespace['inode']):
        raise RuntimeError('target identity changed during holder capture')
def mnt_id(fd):
    values=[line.partition(':')[2].strip() for line in pathlib.Path('/proc/self/fdinfo',str(fd)).read_text(encoding='ascii').splitlines() if line.startswith('mnt_id:')]
    if len(values)!=1 or not values[0].isdigit() or int(values[0])<=0:
        raise RuntimeError('invalid root descriptor mount ID')
    return int(values[0])
validate_target()
descriptor=os.open(proc/'ns'/'mnt',os.O_RDONLY|os.O_CLOEXEC)
root_descriptor=os.open(proc/'root',os.O_PATH|os.O_CLOEXEC)
root_metadata=os.fstat(root_descriptor)
if (os.readlink(f'/proc/self/fd/{descriptor}')!=namespace['link'] or
        os.fstat(descriptor).st_ino!=namespace['inode']):
    raise RuntimeError('captured namespace descriptor changed')
root_mount_id=mnt_id(root_descriptor)
validate_target()
raw=open(f'/proc/{os.getpid()}/stat',encoding='ascii').read()
fields=raw[raw.rfind(')')+2:].split()
print(json.dumps({'pid':os.getpid(),'start_time':fields[19],
                  'fd':descriptor,'root_fd':root_descriptor,
                  'root_device':root_metadata.st_dev,
                  'root_inode':root_metadata.st_ino,
                  'root_mode':root_metadata.st_mode,
                  'root_mnt_id':root_mount_id}),flush=True)
os.close(target_pidfd)
signal.pause()
"""
                external_reaper = subprocess.Popen(
                    [
                        "sudo", "-n", str(supervisor._trusted_tools().helper_python),
                        "-I", "-S", "-c", holder_source,
                        json.dumps({
                            "pid": details["namespace_holder"]["pid"],
                            "start_time": details["namespace_holder"]["start_time"],
                            "namespace": details["namespace"],
                        }, sort_keys=True),
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
                details["external_reapers"] = [external_reaper]
                holder_deadline = time.monotonic() + 8
                holder_record = None
                while time.monotonic() < holder_deadline:
                    holder_scan = _root_proc_scan(
                        namespace=details["namespace"],
                        targets=tuple(Path(path) for path in details["mount_points"]),
                        target_prefix=Path(str(details["control_prefix"])),
                        selection=_RootProcSelection((int(holder_ready["pid"]),)),
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
                holder_record |= {
                    "root_fd": holder_ready["root_fd"],
                    "root_path": (
                        f"/proc/{holder_ready['pid']}/fd/{holder_ready['root_fd']}"
                    ),
                    "root_device": holder_ready["root_device"],
                    "root_inode": holder_ready["root_inode"],
                    "root_mode": holder_ready["root_mode"],
                    "root_mnt_id": holder_ready["root_mnt_id"],
                }
                details["namespace_holders"].append(holder_record)
                details["external_holders"] = [holder_record]
                details["require_fd_only_holder"] = True
                owned_fds = (
                    read_fd, write_fd, lifecycle_ready_read,
                    lifecycle_release_write,
                )
                read_fd = write_fd = -1
                lifecycle_ready_read = lifecycle_release_write = -1
                try:
                    assert _fallback_stalled_observation_cleanup(
                        details, owned_fds,
                    ) == (-1,) * len(owned_fds)
                finally:
                    fallback_done = True
                assert external_reaper.poll() is not None
                assert read_fd == -1 and write_fd == -1
                assert lifecycle_ready_read == -1
                assert lifecycle_release_write == -1
                return
            assert os.write(lifecycle_release_write, b"G") == 1
            os.close(lifecycle_release_write)
            lifecycle_release_write = -1
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline:
                waited, status = os.waitpid(coordinator, os.WNOHANG)
                if waited == coordinator:
                    assert status == 0
                    break
                time.sleep(.05)
            else:
                raise AssertionError("stalled observation coordinator did not exit")
            assert os.read(lifecycle_ready_read, 1) == b""
            os.close(lifecycle_ready_read)
            lifecycle_ready_read = -1
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
                    owned_fds = (
                        read_fd, write_fd, lifecycle_ready_read,
                        lifecycle_release_write,
                    )
                    read_fd = write_fd = -1
                    lifecycle_ready_read = lifecycle_release_write = -1
                    assert _fallback_stalled_observation_cleanup(
                        details, owned_fds,
                    ) == (-1,) * len(owned_fds)
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
            for descriptor in (
                lifecycle_ready_read, lifecycle_ready_write,
                lifecycle_release_read, lifecycle_release_write,
            ):
                if descriptor >= 0:
                    os.close(descriptor)
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
        env=_credential_free_environment(tmp_path), writable_roots=(tmp_path,),
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


def test_descriptor_stall_fixture_saturates_the_exact_pipe() -> None:
    """The hosted cleanup fixture cannot depend on a kernel pipe-size default."""
    read_fd, write_fd = os.pipe()
    try:
        _saturate_descriptor_pipe(write_fd)
        os.set_blocking(write_fd, False)
        with pytest.raises(BlockingIOError):
            os.write(write_fd, b"x")
    finally:
        os.close(read_fd)
        os.close(write_fd)


def test_validated_descriptor_result_gate_precedes_external_handoff() -> None:
    """The helper-owned scope remains held before the bounded observer write."""
    ready_read, ready_write = os.pipe()
    release_read, release_write = os.pipe()
    returned = []
    worker = threading.Thread(
        target=lambda: returned.append(
            _hold_validated_descriptor_result(
                object(), ready_write, release_read,
            )
        ),
    )
    try:
        worker.start()
        readable, _, _ = select.select([ready_read], [], [], 1)
        assert readable and os.read(ready_read, 1) == b"R"
        assert not returned
        assert os.write(release_write, b"G") == 1
        worker.join(timeout=1)
        assert not worker.is_alive() and len(returned) == 1
        source = inspect.getsource(supervisor._run_playwright_descriptor_supervised)
        assert source.index("_descriptor_result(") < source.index(
            "_write_all_descriptor_bytes("
        )
    finally:
        for descriptor in (ready_read, ready_write, release_read, release_write):
            os.close(descriptor)


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
    monkeypatch.setattr(
        supervisor,
        "_stop_scope",
        lambda *_args: (_ for _ in ()).throw(RuntimeError("scope cleanup failed")),
    )
    monkeypatch.setattr(
        supervisor,
        "_cleanup_staging",
        lambda _plan: (_ for _ in ()).throw(RuntimeError("mount cleanup failed")),
    )
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
    assert result.termination.failure_phases == (
        supervisor.InfrastructureFailurePhase.CANDIDATE_EXECUTION,
        supervisor.InfrastructureFailurePhase.SCOPE_CLEANUP,
        supervisor.InfrastructureFailurePhase.MOUNT_CLEANUP,
    )
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
        env=_credential_free_environment(tmp_path), writable_roots=(tmp_path,),
    )
    assert result.returncode == 0
    assert surviving is False
    assert not (tmp_path / "churn").exists()
