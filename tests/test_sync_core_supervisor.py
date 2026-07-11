"""Adversarial tests for complete protected subprocess supervision."""

import os
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path

import pytest

from pdd.sync_core.supervisor import SupervisorLimits, _sandbox_command, run_supervised


def test_linux_sandbox_uses_privileged_namespace_setup_then_drops_uid(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(shutil, "which", lambda name: f"/usr/bin/{name}")
    monkeypatch.setattr(
        "pdd.sync_core.supervisor.subprocess.run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "", ""),
    )
    argv, profile = _sandbox_command(["/bin/true"], (tmp_path,))
    assert profile is None
    assert argv[:3] == ["sudo", "-n", "-E"]
    bwrap = json.loads(argv[-2])
    assert "--unshare-all" in bwrap
    separator = bwrap.index("--")
    assert bwrap.index("--bind") < separator < bwrap.index("--reuid")
    assert bwrap[bwrap.index("--reuid") + 1] == str(os.getuid())
    assert bwrap.index("--proc") < separator
    assert bwrap[bwrap.index("--ro-bind") + 1].startswith("@FD:")


def test_protected_runner_declares_finite_resource_limits() -> None:
    limits = SupervisorLimits()
    assert 0 < limits.max_output_bytes <= 16 * 1024 * 1024
    assert 0 < limits.max_writable_bytes <= 1024 * 1024 * 1024
    assert 0 < limits.max_memory_bytes <= 4 * 1024 * 1024 * 1024
    assert 0 < limits.max_cpu_seconds <= 600
    assert 0 < limits.max_processes <= 256


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
    assert surviving is True
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
    assert surviving is True
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
