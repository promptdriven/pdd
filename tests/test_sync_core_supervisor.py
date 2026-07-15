"""Adversarial tests for complete protected subprocess supervision."""

import os
import json
import math
import shutil
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path

import pytest

from pdd.sync_core import supervisor
from pdd.sync_core.supervisor import (
    SupervisorLimits,
    TerminationKind,
    _linked_libraries,
    _limited_command,
    _live_processes,
    _private_result_command,
    _subprocess_status_handoff,
    _runtime_roots,
    _sandbox_library_path,
    _sandbox_command,
    _supervised_result,
    _termination_evidence,
    _runtime_directories,
    run_supervised,
)
from pdd.sync_core.signer_process import run_signer


def _mock_trusted_tools(
    monkeypatch: pytest.MonkeyPatch, *, missing: frozenset[str] = frozenset(),
    unsafe: dict[str, Path] | None = None,
) -> None:
    """Install explicit synthetic identities for command-construction tests."""
    unsafe = unsafe or {}

    def identity(name: str):
        if name in missing:
            raise RuntimeError(
                "protected sandbox requires a trusted root-owned executable"
            )
        if name in unsafe:
            return supervisor._executable_identity(unsafe[name])
        path = Path(f"/usr/bin/{name}")
        return supervisor._ExecutableIdentity(
            path, (1, len(name), 0o755, 0, len(name), 1),
            name.ljust(64, "0")[:64],
        )

    monkeypatch.setattr(supervisor, "_trusted_tool", identity)
    monkeypatch.setattr(supervisor, "_trusted_helper_python", lambda: identity("python3"))
    monkeypatch.setattr(supervisor, "_trusted_helper_runtime_roots", lambda _identity: ())


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


def test_candidate_environment_launcher_preserves_exact_exit_and_environment(
    tmp_path: Path,
) -> None:
    """The post-drop handoff must exec the child without xargs exit remapping."""
    environment_file = tmp_path / "candidate-env"
    candidate = [
        sys.executable,
        "-c",
        "import os;raise SystemExit(5 if os.environ.get('ONLY') == 'value' "
        "and 'HOSTILE' not in os.environ else 6)",
    ]
    environment_file.write_bytes(
        b"ONLY=value\0" + b"\0".join(item.encode("utf-8") for item in candidate)
    )

    completed = subprocess.run(
        [
            sys.executable,
            "-I",
            "-S",
            "-c",
            supervisor._candidate_environment_launcher(),
            str(environment_file),
        ],
        env={"HOSTILE": "must-not-propagate"},
        capture_output=True,
        text=True,
        check=False,
    )

    assert completed.returncode == 5
    assert completed.stdout == ""
    assert completed.stderr == ""


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

    roots = _runtime_roots([str(candidate_python), "-c", "pass"], workdir)

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
        _runtime_roots(command, workdir)
        raise RuntimeError("protected candidate runtime unavailable")

    monkeypatch.setattr(supervisor, "_sandbox_command", fail_closed)
    result, surviving = run_supervised(
        [str(candidate_python), "-c", "pass"], cwd=workdir, timeout=1,
        env={}, writable_roots=(workdir,),
    )

    assert result.returncode == 125
    assert result.stderr == "protected candidate runtime unavailable"
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
    helper_encodings = tmp_path / "system-python" / "encodings"
    helper_encodings.mkdir(parents=True)
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    monkeypatch.setattr(supervisor, "_SUPERVISOR_EXECUTABLE", Path("/usr/bin/python"))
    _mock_trusted_tools(monkeypatch)
    monkeypatch.setattr(
        supervisor,
        "_trusted_helper_runtime_roots",
        lambda _identity: (helper_encodings,),
        raising=False,
    )
    monkeypatch.setattr(shutil, "which", lambda name: f"/usr/bin/{name}")
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )
    argv, profile = _sandbox_command(["/bin/true"], (tmp_path,))
    assert profile is None
    assert argv[:3] == ["/usr/bin/sudo", "-n", "--"]
    assert argv[3:10] == [
        "/usr/bin/unshare", "--mount", "--propagation", "private",
        "--wd", "/", "/usr/bin/python3",
    ]
    assert argv[10:12] == ["-I", "-S"]
    assert "-E" not in argv
    bwrap = json.loads(argv[-2])
    helper = argv[argv.index("-c") + 1]
    compile(helper, "<privileged-helper>", "exec")
    assert "subprocess.run([mount,'--bind'" in helper
    assert "subprocess.run([umount,str(target)]" in helper
    assert "subprocess.run(argv,check=False,env=helper_env)" in helper
    assert all(
        line in helper for line in _subprocess_status_handoff().splitlines()
    )
    assert "SystemExit(result.returncode" not in helper
    assert "@PDD-CANDIDATE-ENV@" in bwrap
    helper_index = bwrap.index(str(helper_encodings))
    assert bwrap[helper_index - 2] == "--ro-bind"
    assert "/usr/bin/xargs" in bwrap and "/usr/bin/env" in bwrap
    assert "['mount'" not in helper and "['umount'" not in helper
    assert {"--unshare-pid", "--unshare-net", "--unshare-cgroup"} <= set(bwrap)
    assert "--unshare-user" not in bwrap
    separator = bwrap.index("--")
    assert bwrap.index("--bind") < separator < bwrap.index("--reuid")
    candidate_argv = bwrap[separator + 1:]
    assert candidate_argv[candidate_argv.index("--") + 1] == "/usr/bin/python3"
    assert "/usr/bin/xargs" not in candidate_argv
    assert "/usr/bin/env" not in candidate_argv
    launcher = candidate_argv[candidate_argv.index("-c") + 1]
    compile(launcher, "<candidate-environment-launcher>", "exec")
    assert "os.execve(command[0],command,environment)" in launcher
    assert bwrap[bwrap.index("--reuid") + 1] == "1234"
    assert bwrap[bwrap.index("--regid") + 1] == "2345"
    assert bwrap.index("--proc") < separator
    assert bwrap[bwrap.index("--ro-bind") + 1].startswith("@FD:")


def test_linux_sandbox_fails_closed_without_private_mount_namespace_tool(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Protected staging must not fall back to the host mount namespace."""
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    _mock_trusted_tools(monkeypatch, missing=frozenset({"unshare"}))
    monkeypatch.setattr(
        shutil, "which",
        lambda name: None if name == "unshare" else f"/usr/bin/{name}",
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )

    with pytest.raises(RuntimeError, match="trusted root-owned executable"):
        _sandbox_command(["/bin/true"], (tmp_path,))


def test_runtime_closure_measures_unshare_and_excludes_it_from_candidate_roots(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The namespace executable is measured but hidden from candidate roots."""
    unshare = tmp_path / "unshare"
    unshare.write_bytes(b"trusted-unshare")
    monkeypatch.setattr(
        shutil, "which", lambda name: str(unshare) if name == "unshare" else None
    )
    supervisor.released_runtime_closure_paths.cache_clear()
    try:
        closure = dict(supervisor.released_runtime_closure_paths())
        assert closure["sandbox/unshare"] == unshare.resolve()
        roots = _runtime_roots([sys.executable], tmp_path)
        assert unshare.resolve() not in roots
    finally:
        supervisor.released_runtime_closure_paths.cache_clear()


def test_privileged_helper_rejects_user_owned_path_shadow_tools(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Caller-owned executables must never cross the sudo boundary."""
    shadow = tmp_path / "unshare"
    shadow.write_text("malicious", encoding="utf-8")
    shadow.chmod(0o755)
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    _mock_trusted_tools(
        monkeypatch, unsafe={"unshare": shadow, "mount": shadow}
    )
    monkeypatch.setattr(
        shutil, "which",
        lambda name: str(shadow) if name in {"unshare", "mount"} else f"/usr/bin/{name}",
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )

    with pytest.raises(RuntimeError, match="protected executable"):
        _sandbox_command(["/bin/true"], (tmp_path,))


def test_privileged_helper_environment_is_fixed_and_candidate_independent() -> None:
    candidate = {
        "PATH": "/candidate/bin",
        "PYTHONPATH": "/candidate/hooks",
        "PYTHONHOME": "/candidate/python",
    }

    helper_environment = supervisor._privileged_helper_environment(candidate)

    assert helper_environment == {
        "HOME": "/root",
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/sbin:/usr/bin:/sbin:/bin",
    }


def test_privileged_helper_revalidates_bound_executable_identity(
    tmp_path: Path,
) -> None:
    executable = tmp_path / "tool"
    executable.write_bytes(b"first")
    executable.chmod(0o755)
    measured = supervisor._executable_identity(executable, require_root=False)
    executable.write_bytes(b"second")

    with pytest.raises(RuntimeError, match="identity changed"):
        supervisor._revalidate_executable(measured)


def test_privileged_helper_rejects_mode_change_before_exec(tmp_path: Path) -> None:
    executable = tmp_path / "tool"
    executable.write_bytes(b"trusted")
    executable.chmod(0o755)
    measured = supervisor._executable_identity(executable, require_root=False)
    executable.chmod(0o777)

    with pytest.raises(RuntimeError, match="identity changed"):
        supervisor._revalidate_executable(measured)


def test_executable_measurement_uses_descriptor_not_path_read(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    executable = tmp_path / "tool"
    executable.write_bytes(b"trusted")
    executable.chmod(0o755)
    monkeypatch.setattr(
        Path, "open",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("path read crossed identity boundary")
        ),
    )

    identity = supervisor._executable_identity(executable, require_root=False)

    assert identity.sha256


@pytest.mark.parametrize("swap", ["rename", "symlink"])
def test_privileged_helper_rejects_path_entry_swaps(
    tmp_path: Path, swap: str,
) -> None:
    executable = tmp_path / "tool"
    executable.write_bytes(b"trusted")
    executable.chmod(0o755)
    measured = supervisor._executable_identity(executable, require_root=False)
    original = tmp_path / "original"
    executable.rename(original)
    if swap == "symlink":
        executable.symlink_to(original)
    else:
        executable.write_bytes(b"replacement")
        executable.chmod(0o755)

    with pytest.raises(RuntimeError, match="identity changed"):
        supervisor._revalidate_executable(measured)


def test_linux_sandbox_maps_copied_runtime_to_manifest_destination(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(os, "getuid", lambda: 1234)
    monkeypatch.setattr(os, "getgid", lambda: 2345)
    _mock_trusted_tools(monkeypatch)
    monkeypatch.setattr(shutil, "which", lambda name: f"/usr/bin/{name}")
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

    bwrap = json.loads(argv[-2])
    sources = json.loads(argv[-1])
    destination_index = bwrap.index(str(manifest_destination))
    assert bwrap[destination_index - 2] == "--ro-bind"
    placeholder = bwrap[destination_index - 1]
    assert sources[int(placeholder.removeprefix("@FD:").removesuffix("@"))] == str(
        copied.resolve()
    )


def test_linux_sandbox_fails_closed_for_root_caller(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_trusted_tools(monkeypatch)
    monkeypatch.setattr(os, "getuid", lambda: 0)
    monkeypatch.setattr(shutil, "which", lambda name: f"/usr/bin/{name}")

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
    _mock_trusted_tools(monkeypatch)
    monkeypatch.setattr(shutil, "which", lambda name: f"/usr/bin/{name}")
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
    argv, profile = _sandbox_command(
        ["/bin/true"], (tmp_path,), result_fifo=fifo, result_fd=198
    )

    assert profile is None
    assert argv[:3] == ["/usr/bin/sudo", "-n", "--"]
    assert "-E" not in argv
    assert "-C" not in argv[:6]
    bwrap = json.loads(argv[-2])
    assert "--preserve-fds" not in bwrap
    assert json.loads(argv[-1])
    assert str(channel) in bwrap
    separator = bwrap.index("--")
    candidate_argv = bwrap[separator + 1:]
    protected_command = json.loads(argv[argv.index("-c") + 2])
    assert str(fifo) in protected_command
    wrapper = protected_command[protected_command.index("-c") + 1]
    assert "os.open(path,os.O_WRONLY);os.unlink(path)" in wrapper
    assert protected_command.index(str(fifo)) < protected_command.index("/bin/true")
    assert "@PDD-CANDIDATE-ENV@" in candidate_argv


def test_sandbox_directory_bind_provides_parent_for_nested_file(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    nested = tmp_path / "candidate-venv" / "bin"
    nested.mkdir(parents=True)
    interpreter = nested / "python"
    interpreter.write_text("python", encoding="utf-8")
    monkeypatch.setattr(sys, "platform", "linux")
    _mock_trusted_tools(monkeypatch)
    monkeypatch.setattr(shutil, "which", lambda name: f"/usr/bin/{name}")
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.released_runtime_closure_paths", lambda: ()
    )

    argv, _profile = _sandbox_command([str(interpreter)], (tmp_path,), cwd=tmp_path)
    bwrap = json.loads(argv[-2])
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
    _mock_trusted_tools(monkeypatch)
    monkeypatch.setattr(
        "pdd.sync_core.supervisor._SUPERVISOR_EXECUTABLE",
        executable_destination,
    )
    sandbox_tools = {
        "bwrap": "/usr/bin/bwrap",
        "sudo": "/usr/bin/sudo",
        "setpriv": "/usr/bin/setpriv",
        "unshare": "/usr/bin/unshare",
    }
    monkeypatch.setattr(
        shutil,
        "which",
        sandbox_tools.get,
    )
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
    bwrap = json.loads(argv[-2])
    sources = json.loads(argv[-1])

    def bind_source(destination: Path) -> str:
        index = bwrap.index(str(destination))
        assert bwrap[index - 2] == "--ro-bind"
        placeholder = bwrap[index - 1]
        assert placeholder.startswith("@FD:") and placeholder.endswith("@")
        return sources[int(placeholder[4:-1])]

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


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires Linux kernel namespace containment",
)
def test_sandboxed_launcher_preserves_exit_five_and_clears_inherited_env(
    tmp_path: Path,
) -> None:
    """Exercise the exact post-drop handoff inside the empty Linux root."""
    candidate = (
        "import os;raise SystemExit(5 if os.environ.get('ONLY') == 'value' "
        "and 'HOSTILE' not in os.environ else 6)"
    )
    result, surviving = run_supervised(
        [sys.executable, "-c", candidate],
        cwd=tmp_path,
        timeout=10,
        env={"ONLY": "value"},
        writable_roots=(tmp_path,),
    )

    assert result.returncode == 5, result.stderr
    assert surviving is False


def test_protected_runner_declares_finite_resource_limits() -> None:
    limits = SupervisorLimits()
    assert 0 < limits.max_output_bytes <= 16 * 1024 * 1024
    assert 0 < limits.max_writable_bytes <= 1024 * 1024 * 1024
    assert 0 < limits.max_memory_bytes <= 4 * 1024 * 1024 * 1024
    assert 0 < limits.max_cpu_seconds <= 600
    assert 0 < limits.max_processes <= 256


@pytest.mark.parametrize(
    ("returncode", "timed_out", "resource_limit", "kind", "field"),
    [
        (23, False, None, TerminationKind.EXIT, ("exit_code", 23)),
        (-9, False, None, TerminationKind.SIGNAL, ("signal_number", 9)),
        (0, True, None, TerminationKind.TIMEOUT, ("timeout_seconds", 7)),
        (
            0,
            False,
            "output-bytes",
            TerminationKind.RESOURCE_LIMIT,
            ("resource_limit", "output-bytes"),
        ),
        (
            -signal.SIGXCPU,
            False,
            None,
            TerminationKind.SIGNAL,
            ("signal_number", signal.SIGXCPU),
        ),
    ],
)
def test_termination_evidence_preserves_trusted_cause(
    returncode, timed_out, resource_limit, kind, field
) -> None:
    evidence = _termination_evidence(
        returncode,
        timed_out=timed_out,
        timeout_seconds=7,
        resource_limit=resource_limit,
    )

    assert evidence.kind is kind
    assert getattr(evidence, field[0]) == field[1]


@pytest.mark.parametrize("candidate_signal", [signal.SIGXCPU, signal.SIGXFSZ])
def test_candidate_self_resource_signal_is_only_observed_as_signal(
    candidate_signal: signal.Signals,
) -> None:
    """An untrusted child signal is not proof that a configured limit fired."""
    completed = subprocess.run(
        [
            sys.executable,
            "-c",
            "import os,signal;s=int(os.environ['signal_number']);"
            "signal.signal(s,signal.SIG_DFL);os.kill(os.getpid(),s)",
        ],
        env={**os.environ, "signal_number": str(int(candidate_signal))},
        capture_output=True,
        text=True,
        check=False,
    )
    evidence = _termination_evidence(
        completed.returncode,
        timed_out=False,
        timeout_seconds=7,
        resource_limit=None,
    )

    assert completed.returncode == -candidate_signal
    assert evidence.kind is TerminationKind.SIGNAL
    assert evidence.signal_number == candidate_signal
    assert evidence.resource_limit is None


@pytest.mark.parametrize("candidate_signal", [signal.SIGXCPU, signal.SIGXFSZ])
def test_staged_wrapper_preserves_nested_subprocess_signal(
    candidate_signal: signal.Signals,
) -> None:
    """Exercise the exact helper handoff after its nested subprocess.run call."""
    script = "\n".join((
        "import os,signal,subprocess,sys",
        "result=subprocess.run([sys.executable,'-c',"
        "'import os,signal,sys;s=int(sys.argv[1]);signal.signal(s,signal.SIG_DFL);"
        "os.kill(os.getpid(),s)',sys.argv[1]],"
        "check=False)",
        _subprocess_status_handoff(),
    ))

    completed = subprocess.run(
        [sys.executable, "-c", script, str(int(candidate_signal))],
        capture_output=True,
        text=True,
        check=False,
    )

    assert completed.returncode == -candidate_signal


def test_supervised_result_remains_subprocess_compatible() -> None:
    evidence = _termination_evidence(
        3, timed_out=False, timeout_seconds=7, resource_limit=None
    )
    result = _supervised_result(["checker"], 3, "out", "err", evidence)

    assert isinstance(result, subprocess.CompletedProcess)
    assert result.returncode == 3
    assert result.termination is evidence


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
        ["/bin/true"], cwd=tmp_path, timeout=1, env={},
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


def test_parallel_staged_and_signer_bwrap_do_not_share_host_mounts(
    tmp_path: Path,
) -> None:
    """Keep a staged sandbox live while a signer starts in a sibling process."""
    if not sys.platform.startswith("linux"):
        pytest.skip("requires Linux mount namespaces")
    required = ("bwrap", "sudo", "unshare", "mount", "umount", "setpriv")
    if any(shutil.which(tool) is None for tool in required):
        pytest.skip("requires the privileged Linux sandbox toolchain")
    if subprocess.run(
        ["sudo", "-n", "true"], capture_output=True, check=False,
    ).returncode != 0:
        pytest.skip("requires passwordless sudo")

    scratch = tmp_path / "scratch"
    scratch.mkdir()
    started = scratch / "candidate-started"
    outcome: list[tuple[subprocess.CompletedProcess[str], bool]] = []
    observed_mount_leak = threading.Event()
    sampling_done = threading.Event()

    def sample_parent_mounts() -> None:
        while not sampling_done.wait(0.001):
            if "pdd-binds-" in Path("/proc/self/mountinfo").read_text(
                encoding="utf-8"
            ):
                observed_mount_leak.set()

    def run_staged_candidate() -> None:
        outcome.append(run_supervised(
            [
                sys.executable, "-c",
                "import pathlib,sys,time; "
                "pathlib.Path(sys.argv[1]).write_text('started'); time.sleep(1.5)",
                str(started),
            ],
            cwd=scratch,
            timeout=10,
            env=dict(os.environ),
            writable_roots=(scratch,),
        ))

    sampler = threading.Thread(target=sample_parent_mounts)
    candidate = threading.Thread(target=run_staged_candidate)
    sampler.start()
    candidate.start()
    try:
        deadline = time.monotonic() + 10
        while not started.exists() and candidate.is_alive() and time.monotonic() < deadline:
            time.sleep(0.005)
        assert started.exists(), outcome

        signer = run_signer(
            (sys.executable, "-c", "print('signer-started')"), b"", timeout=5,
        )
        assert signer.returncode == 0, signer.stderr.decode(errors="replace")
        assert signer.stdout.strip() == b"signer-started"
    finally:
        candidate.join(timeout=15)
        sampling_done.set()
        sampler.join(timeout=2)

    assert not candidate.is_alive()
    assert outcome and outcome[0][0].returncode == 0, outcome
    assert outcome[0][1] is False
    assert not observed_mount_leak.is_set()
    assert "pdd-binds-" not in Path("/proc/self/mountinfo").read_text(
        encoding="utf-8"
    )


def test_privileged_helper_cannot_import_candidate_sitecustomize(
    tmp_path: Path,
) -> None:
    """Candidate Python hooks must not execute before the sandbox uid drop."""
    if not sys.platform.startswith("linux"):
        pytest.skip("requires Linux privileged sandbox startup")
    required = ("bwrap", "sudo", "unshare", "mount", "umount", "setpriv")
    if any(shutil.which(tool) is None for tool in required):
        pytest.skip("requires the privileged Linux sandbox toolchain")
    if subprocess.run(
        ["sudo", "-n", "true"], capture_output=True, check=False,
    ).returncode != 0:
        pytest.skip("requires passwordless sudo")

    hooks = tmp_path / "hooks"
    scratch = tmp_path / "scratch"
    hooks.mkdir()
    scratch.mkdir()
    sentinel = scratch / "root-hook-ran"
    (hooks / "sitecustomize.py").write_text(
        "import os, pathlib\n"
        f"if os.geteuid() == 0: pathlib.Path({str(sentinel)!r}).write_text('unsafe')\n",
        encoding="utf-8",
    )

    result, surviving = run_supervised(
        ["/bin/true"], cwd=scratch, timeout=10,
        env={"PATH": os.environ.get("PATH", ""), "PYTHONPATH": str(hooks)},
        writable_roots=(scratch,), readable_roots=(hooks,),
    )

    assert result.returncode == 0, result.stderr
    assert surviving is False
    assert not sentinel.exists()


def test_candidate_ld_preload_never_loads_in_root_setup_processes(
    tmp_path: Path,
) -> None:
    """A candidate loader hook may run only after the sandbox credential drop."""
    if not sys.platform.startswith("linux"):
        pytest.skip("requires Linux dynamic-loader and sudo boundaries")
    required = (
        "bwrap", "sudo", "unshare", "mount", "umount", "setpriv", "gcc",
    )
    if any(shutil.which(tool) is None for tool in required):
        pytest.skip("requires the privileged Linux sandbox toolchain and gcc")
    if subprocess.run(
        ["sudo", "-n", "true"], capture_output=True, check=False,
    ).returncode != 0:
        pytest.skip("requires passwordless sudo")

    scratch = tmp_path / "scratch"
    scratch.mkdir()
    sentinel = scratch / "root-preload-ran"
    source = tmp_path / "preload.c"
    library = scratch / "preload.so"
    source.write_text(
        "#include <fcntl.h>\n#include <unistd.h>\n"
        "__attribute__((constructor)) static void probe(void) {\n"
        f'  if (geteuid() == 0) {{ int fd=open("{sentinel}",O_CREAT|O_WRONLY,0600); '
        "if(fd>=0) close(fd); }\n}\n",
        encoding="utf-8",
    )
    subprocess.run(
        ["gcc", "-shared", "-fPIC", "-o", str(library), str(source)], check=True,
    )

    result, surviving = run_supervised(
        ["/bin/true"], cwd=scratch, timeout=10,
        env={"PATH": os.environ.get("PATH", ""), "LD_PRELOAD": str(library)},
        writable_roots=(scratch,),
    )

    assert result.returncode == 0, result.stderr
    assert surviving is False
    assert not sentinel.exists()
