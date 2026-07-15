"""Adversarial tests for complete protected subprocess supervision."""

import os
import hashlib
import inspect
import json
import math
import signal
import shutil
import stat
import subprocess
import sys
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
    ):
        path = directory / name
        path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        path.chmod(0o755)
        tools[name] = str(path)
    monkeypatch.setattr(shutil, "which", lambda name, path=None: tools.get(name))
    return tools


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
        "launch_policy": {"linux_wasm_trap_handler_disabled": True},
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
    assert argv[:3] == [str(plan.tools.sudo), "-n", "-E"]
    bwrap = json.loads(argv[-4])
    assert {"--unshare-pid", "--unshare-net", "--unshare-cgroup"} <= set(bwrap)
    assert "--unshare-user" not in bwrap
    separator = bwrap.index("--")
    assert bwrap.index("--bind") < separator < bwrap.index("--reuid")
    assert bwrap[bwrap.index("--reuid") + 1] == "1234"
    assert bwrap[bwrap.index("--regid") + 1] == "2345"
    assert bwrap.index("--proc") < separator
    assert bwrap[bwrap.index("--ro-bind") + 1] in json.loads(argv[-5])


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

    argv, _profile = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_bindings=((copied, manifest_destination),),
    )

    bwrap = json.loads(argv[-4])
    sources = json.loads(argv[-3])
    destination_index = bwrap.index(str(manifest_destination))
    assert bwrap[destination_index - 2] == "--ro-bind"
    placeholder = bwrap[destination_index - 1]
    tokens = json.loads(argv[-5])
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

    argv, _profile = _sandbox_command(
        ["/bin/true"],
        (scratch,),
        writable_bindings=((scratch, Path("/tmp")),),
    )

    bwrap = json.loads(argv[-4])
    sources = json.loads(argv[-3])
    destination_index = len(bwrap) - 1 - bwrap[::-1].index("/tmp")
    assert bwrap[destination_index - 2] == "--bind"
    assert destination_index < bwrap.index("--ro-bind")
    placeholder = bwrap[destination_index - 1]
    writable_roots = json.loads(argv[-7])
    writable_specs = json.loads(argv[-6])
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

    argv, _profile = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_roots=(native, native),
        readable_bindings=((native, native),),
    )

    bwrap = json.loads(argv[-4])
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

    argv, _profile = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_bindings=((copied_loader, host_loader),),
        immutable_binding_proofs=(proof,),
    )

    bwrap = json.loads(argv[-4])
    sources = json.loads(argv[-3])
    destination_index = bwrap.index(str(host_loader))
    assert bwrap.count(str(host_loader)) == 1
    assert sources[json.loads(argv[-5]).index(bwrap[destination_index - 1])] == str(
        copied_loader.resolve()
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
    argv, plan = _sandbox_command(
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
    validated_uid, validated_gid = namespace["_validated_candidate_identity"](
        argv[-9], json.loads(argv[-4])
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
    bwrap = json.loads(argv[-4])
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
    command, _plan = _sandbox_command(
        ["/bin/true"],
        (tmp_path,),
        readable_bindings=((copied, protected),),
        immutable_binding_proofs=(proof,),
    )
    bwrap = json.loads(command[-4])
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
    argv, plan = _sandbox_command(
        ["/bin/true"], (scratch,), result_fifo=fifo, result_fd=198
    )

    assert plan.unit_name.startswith("pdd-validator-")
    assert argv[:3] == [str(plan.tools.sudo), "-n", "-E"]
    assert "-C" not in argv[:6]
    bwrap = json.loads(argv[-4])
    assert "--preserve-fds" not in bwrap
    observation_path = "/run/pdd-framework-observation"
    observation_index = bwrap.index(observation_path)
    assert bwrap[observation_index - 2] == "--bind"
    observation_token = bwrap[observation_index - 1]
    tokens = json.loads(argv[-5])
    sources = json.loads(argv[-3])
    assert sources[tokens.index(observation_token)] == str(fifo.resolve())
    assert str(channel) not in bwrap
    separator = bwrap.index("--")
    candidate_argv = bwrap[separator + 1:]
    assert str(fifo) not in candidate_argv
    wrapper = candidate_argv[candidate_argv.index("-c") + 1]
    assert "os.dup2(source,target)" in wrapper
    assert "os.open(path" in wrapper
    assert "result_fifo" not in plan.helper_source


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
        plan = SimpleNamespace(
            unit_name="pdd-validator-00000000000000000000000000000000.scope",
            tools=SimpleNamespace(),
        )
        return [sys.executable, "-c", helper, str(kwargs["control_directory"])], plan

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

    argv, _profile = _sandbox_command([str(interpreter)], (tmp_path,), cwd=tmp_path)
    bwrap = json.loads(argv[-4])
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

    argv, _profile = _sandbox_command(
        [str(candidate), "-c", "pass"], (workdir,), cwd=workdir
    )
    bwrap = json.loads(argv[-4])
    sources = json.loads(argv[-3])

    def bind_source(destination: Path) -> str:
        index = bwrap.index(str(destination))
        assert bwrap[index - 2] == "--ro-bind"
        placeholder = bwrap[index - 1]
        tokens = json.loads(argv[-5])
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

    assert argv[:4] == [tools["sudo"], "-n", "-E", tools["systemd-run"]]
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
    assert "(candidate_cgroup/'cgroup.procs').write_text(str(pid)" in helper
    assert helper.index("(candidate_cgroup/'cgroup.procs').write_text(str(pid)") < helper.index(
        "os.write(release_write,b'1')"
    )
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
    assert json.loads(argv[-1])["timeout"] == 17
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
    assert helper.index("mount_lines=") < helper.index("ready")
    assert "@PDD-CGROUP@" in plan.bwrap_argv
    cgroup_source = plan.bwrap_argv.index("@PDD-CGROUP@")
    assert plan.bwrap_argv[cgroup_source - 1] == "--ro-bind"
    assert plan.bwrap_argv[cgroup_source + 1] == "/sys/fs/cgroup"


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
        plan = SimpleNamespace(
            unit_name="pdd-validator-00000000000000000000000000000000.scope",
            tools=SimpleNamespace(),
        )
        return [sys.executable, "-c", helper, str(kwargs["control_directory"])], plan

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


def test_live_processes_rejects_reused_pid_identity(monkeypatch) -> None:
    monkeypatch.setattr("pdd.sync_core.supervisor._process_identity", lambda _pid: "new")
    monkeypatch.setattr(os, "kill", lambda *_args: None)
    assert _live_processes({123: "old"}) == set()


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
