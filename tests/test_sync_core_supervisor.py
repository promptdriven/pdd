"""Adversarial tests for complete protected subprocess supervision."""

import os
import shutil
import sys
import time
from pathlib import Path

import pytest

from pdd.sync_core.supervisor import run_supervised


@pytest.mark.skipif(
    not (shutil.which("sandbox-exec") or shutil.which("bwrap")),
    reason="requires a real supported sandbox",
)
def test_detached_session_descendant_is_terminated(tmp_path: Path) -> None:
    marker = tmp_path / "escaped"
    child = (
        "import os,sys,time; os.setsid(); time.sleep(1); "
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
