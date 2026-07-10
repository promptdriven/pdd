"""Tests for the isolated-agent launch helpers."""

from __future__ import annotations

import sys
import threading

import pytest

from harness.runner.agent_launcher import (
    AgentLaunchError,
    FileAgentLauncher,
    launch_local_subprocess,
    run_worker_loop,
)


def test_launch_local_subprocess_runs_command(tmp_path):
    result = launch_local_subprocess(
        command=[sys.executable, "-c", "print('ok')"],
        cwd=tmp_path,
        env={},
        timeout_seconds=5,
    )
    assert result.returncode == 0
    assert result.stdout.strip() == "ok"
    assert result.launcher == "local"


def test_file_agent_launcher_dispatches_to_worker(tmp_path):
    launcher = FileAgentLauncher(tmp_path)
    results = []

    def _launch():
        results.append(
            launcher.launch(
                run_id="demo",
                command=[sys.executable, "-c", "print('worker-ok')"],
                cwd=tmp_path,
                env={},
                timeout_seconds=5,
            )
        )

    thread = threading.Thread(target=_launch, daemon=True)
    thread.start()
    run_worker_loop(tmp_path, once=True)
    thread.join(timeout=5)
    assert results
    result = results[0]
    assert result.returncode == 0
    assert result.stdout.strip() == "worker-ok"
    assert result.launcher == "container_worker"


def test_file_agent_launcher_times_out_when_worker_never_answers(tmp_path):
    launcher = FileAgentLauncher(tmp_path, poll_interval_seconds=0.01)
    with pytest.raises(AgentLaunchError, match="timed out waiting"):
        launcher.launch(
            run_id="demo",
            command=[sys.executable, "-c", "print('x')"],
            cwd=tmp_path,
            env={},
            timeout_seconds=0.01,
        )
