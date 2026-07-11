"""Adversarial tests for complete protected subprocess supervision."""

import os
import shutil
import sys
import time
from pathlib import Path

import pytest

from pdd.sync_core.supervisor import _sandbox_command, run_supervised


def test_linux_sandbox_uses_network_namespace_without_loopback_setup(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    monkeypatch.setattr(shutil, "which", lambda name: f"/usr/bin/{name}")
    argv, profile = _sandbox_command(["/bin/true"], (tmp_path,))
    assert profile is None
    assert argv[:5] == ["unshare", "--user", "--map-root-user", "--net", "--"]
    assert "--unshare-net" not in argv


@pytest.mark.skipif(
    not (shutil.which("sandbox-exec") or shutil.which("bwrap")),
    reason="requires a real supported sandbox",
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
    not (shutil.which("sandbox-exec") or shutil.which("bwrap")),
    reason="requires a real supported sandbox",
)
def test_detached_descendant_cannot_escape_by_removing_marker(tmp_path: Path) -> None:
    marker = tmp_path / "escaped-without-marker"
    child = (
        "import os,sys,time; os.environ.pop('PDD_SUPERVISION_TOKEN', None); "
        "os.setsid(); os.close(1); os.close(2); time.sleep(1); "
        "open(sys.argv[1], 'w').write('escaped')"
    )
    parent = (
        "import subprocess,sys; "
        "subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]])"
    )
    result, surviving = run_supervised(
        [sys.executable, "-c", parent, child, str(marker)], cwd=tmp_path,
        timeout=10, env=dict(os.environ), writable_roots=(tmp_path,),
    )
    assert result.returncode == 0
    assert surviving is True
    time.sleep(1.2)
    assert not marker.exists()
