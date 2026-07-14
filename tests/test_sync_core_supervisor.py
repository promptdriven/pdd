"""Adversarial tests for complete protected subprocess supervision."""

import os
import json
import math
import shutil
import subprocess
import sys
import time
from pathlib import Path

import pytest

from pdd.sync_core import supervisor
from pdd.sync_core.supervisor import (
    SupervisorLimits,
    _linked_libraries,
    _limited_command,
    _live_processes,
    _private_result_command,
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


def test_private_result_wrapper_unlinks_channel_before_candidate(
    tmp_path: Path,
) -> None:
    """Exercise the pre-exec channel handoff without a Linux sandbox."""
    channel = tmp_path / "channel"
    channel.mkdir(mode=0o700)
    fifo = channel / "result.fifo"
    os.mkfifo(fifo, mode=0o600)
    read_fd = os.open(fifo, os.O_RDONLY | os.O_NONBLOCK)
    result_fd = 17
    candidate = [
        sys.executable,
        "-c",
        f"import os;os.write({result_fd},b'trusted-result')",
    ]

    completed = subprocess.run(
        _private_result_command(candidate, fifo, result_fd),
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    try:
        assert completed.returncode == 0, completed.stderr
        assert not fifo.exists()
        assert os.read(read_fd, 1024) == b"trusted-result"
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
    tokens = json.loads(argv[-5])
    assert sources[tokens.index(placeholder)] == str(scratch.resolve())


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


def test_linux_sandbox_opens_and_unlinks_checker_fifo_before_candidate(
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
    fifo = channel / "checker.fifo"
    os.mkfifo(fifo)
    argv, plan = _sandbox_command(
        ["/bin/true"], (tmp_path,), result_fifo=fifo, result_fd=198
    )

    assert plan.unit_name.startswith("pdd-validator-")
    assert argv[:3] == [str(plan.tools.sudo), "-n", "-E"]
    assert "-C" not in argv[:6]
    bwrap = json.loads(argv[-4])
    assert "--preserve-fds" not in bwrap
    assert json.loads(argv[-3])
    assert str(channel) in bwrap
    separator = bwrap.index("--")
    candidate_argv = bwrap[separator + 1:]
    assert str(fifo) in candidate_argv
    wrapper = candidate_argv[candidate_argv.index("-c") + 1]
    assert "os.open(path,os.O_WRONLY);os.unlink(path)" in wrapper
    assert candidate_argv.index(str(fifo)) < candidate_argv.index("/bin/true")


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
    assert "--property=MemoryMax=2147483648" in argv
    assert "--property=MemorySwapMax=0" in argv
    assert "--property=TasksMax=128" in argv
    assert "--property=OOMPolicy=kill" in argv
    assert "--property=KillMode=control-group" in argv
    assert plan.bwrap_argv[0] == tools["bwrap"]


def test_linux_sandbox_releases_candidate_only_after_scope_probe(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The privileged helper must configure the aggregate cgroup before release."""
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

    _argv, plan = _sandbox_command([sys.executable, "-c", "pass"], (tmp_path,))
    helper = plan.helper_source

    compile(helper, "<privileged-scope-helper>", "exec")
    assert "cgroup.procs" not in helper
    assert "memory.max" not in helper
    assert "ready" in helper and "start" in helper
    assert helper.index("start") < helper.index("os.fork()")
    assert "result.json" in helper and "finish" in helper
    assert "@PDD-CGROUP@" in plan.bwrap_argv
    cgroup_source = plan.bwrap_argv.index("@PDD-CGROUP@")
    assert plan.bwrap_argv[cgroup_source - 1] == "--ro-bind"
    assert plan.bwrap_argv[cgroup_source + 1] == "/sys/fs/cgroup"


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


def test_scope_probe_requires_systemd_and_kernel_limits_before_release(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Accept a scope only when systemd and cgroup-v2 report every hard limit."""
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_linux_tools(tmp_path, monkeypatch)
    tools = supervisor._trusted_tools()
    cgroup = tmp_path / "scope-cgroup"
    cgroup.mkdir()
    values = {
        "memory.max": "2147483648", "memory.swap.max": "0",
        "memory.oom.group": "1", "pids.max": "128",
        "memory.events": "oom 3\noom_kill 2\n",
        "pids.events": "max 4\n",
    }
    for name, value in values.items():
        (cgroup / name).write_text(value, encoding="ascii")
    properties = {
        "LoadState": "loaded", "ActiveState": "active",
        "ControlGroup": "/system.slice/example.scope",
        "MemoryMax": "2147483648", "MemorySwapMax": "0",
        "TasksMax": "128", "OOMPolicy": "kill",
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

    assert actual_cgroup == cgroup
    assert memory["oom_kill"] == 2
    assert pids["max"] == 4
    properties["KillMode"] = "process"
    with pytest.raises(RuntimeError, match="properties unverified"):
        supervisor._probe_scope(plan, SupervisorLimits())


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
        "show", "kill", "stop", "reset-failed", "show",
    ]
    assert all(unit in command for command in commands)
    assert commands[1][:3] == ["kill", "--kill-whom=all", "--signal=SIGKILL"]


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
        writable_roots=(scratch,), writable_files=(result_channel,),
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


def test_file_size_limit_uses_output_budget() -> None:
    limits = SupervisorLimits(max_output_bytes=1234, max_writable_bytes=987654)
    command = _limited_command(["/bin/true"], limits)
    assert "1234" in command
    assert "987654" not in command[1:7]


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
