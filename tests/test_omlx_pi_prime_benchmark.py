"""Offline unit tests for the Pi/Prime benchmark helpers."""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path
from unittest.mock import Mock

import pytest


MODULE_PATH = (
    Path(__file__).parents[1] / "research" / "omlx-qwen38-pi-prime" / "benchmark.py"
)
SPEC = importlib.util.spec_from_file_location("pi_prime_benchmark", MODULE_PATH)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def test_build_schedule_balances_order() -> None:
    schedule = MODULE.build_schedule(("one", "two"), 2)
    assert schedule == [
        (1, "one", "pi"),
        (1, "one", "prime"),
        (1, "two", "prime"),
        (1, "two", "pi"),
        (2, "one", "prime"),
        (2, "one", "pi"),
        (2, "two", "pi"),
        (2, "two", "prime"),
    ]


def test_extract_usage_from_sse() -> None:
    payload = (
        'data: {"choices":[],"usage":{"prompt_tokens":12,"completion_tokens":3}}\n\n'
        "data: [DONE]\n\n"
    ).encode()
    assert MODULE.extract_usage(payload, "text/event-stream") == {
        "prompt_tokens": 12,
        "completion_tokens": 3,
    }


def test_proxy_cancels_active_upstream_responses(tmp_path: Path) -> None:
    proxy = MODULE.MeteringProxy(
        "http://127.0.0.1:8000", "secret", tmp_path / "proxy.jsonl"
    )
    response = Mock()
    proxy._register_response(response)
    proxy._cancel_active_responses()
    response.close.assert_called_once_with()
    proxy._unregister_response(response)
    assert not proxy._active_responses
    assert MODULE.TrackedThreadingHTTPServer.daemon_threads is True


def test_proxy_log_integrity_requires_one_terminal_per_request(tmp_path: Path) -> None:
    log_path = tmp_path / "proxy.jsonl"
    log_path.write_text(
        "\n".join(
            [
                json.dumps({"event": "request", "request_id": "one"}),
                json.dumps({"event": "response", "request_id": "one"}),
            ]
        )
        + "\n"
    )
    MODULE.assert_proxy_log_complete(log_path, MODULE.ProxyTotals(requests=1))


def test_write_model_config_contains_no_real_secret(tmp_path: Path) -> None:
    MODULE.write_model_config(tmp_path, 8123)
    payload = json.loads((tmp_path / "models.json").read_text())
    provider = payload["providers"]["omlx-benchmark"]
    assert provider["apiKey"] == "loopback-proxy"
    assert provider["baseUrl"] == "http://127.0.0.1:8123/v1"


def test_sandbox_profile_allows_only_proxy_network_and_scoped_writes(
    tmp_path: Path,
) -> None:
    workspace = tmp_path / "run" / "workspace"
    home = tmp_path / "run" / "home"
    daemon_socket = Path("/private/tmp/prime-bench-test.sock")
    temp_dir = tmp_path / "run" / "tmp"
    profile = MODULE.sandbox_profile(
        tmp_path / "run",
        workspace,
        home,
        tmp_path / "tools",
        temp_dir,
        8123,
        daemon_socket,
    )
    assert '(allow network-outbound (remote ip "localhost:8123"))' in profile
    assert f'(subpath "{workspace}")' in profile
    assert f'(subpath "{home}")' in profile
    for name in MODULE.TOOL_SUBDIRECTORIES:
        assert f'(subpath "{(tmp_path / "tools" / name).resolve()}")' in profile
    assert f'(subpath "{tmp_path / "tools"}")' not in profile
    assert f'(literal "{daemon_socket}")' in profile
    assert f'(local unix-socket (literal "{daemon_socket}"))' in profile
    assert f'(remote unix-socket (literal "{daemon_socket}"))' in profile
    worker_socket_dir = temp_dir / f"prime-agent-{MODULE.os.getuid()}"
    assert f'(local unix-socket (subpath "{worker_socket_dir}"))' in profile
    assert f'(remote unix-socket (subpath "{worker_socket_dir}"))' in profile
    assert '(allow network-bind (local ip "localhost:*"))' in profile
    assert '(allow network-inbound (local ip "localhost:*"))' in profile
    assert '(allow network-outbound (local ip "localhost:*"))' in profile
    assert "(allow system-socket" not in profile
    assert f'(literal "{daemon_socket}.lock")' in profile
    assert f'(subpath "{daemon_socket}.lock")' in profile
    assert "(deny network*)" in profile


def test_hidden_grader_boundary_rejects_overlap_with_read_root(tmp_path: Path) -> None:
    tool_root = tmp_path / "tools"
    for name in MODULE.TOOL_SUBDIRECTORIES:
        (tool_root / name).mkdir(parents=True)
    tasks_root = tool_root / "pi" / "tasks"
    tasks_root.mkdir()
    with pytest.raises(RuntimeError, match="overlaps"):
        MODULE.validate_hidden_grader_boundary(tasks_root, (), tool_root)


def test_run_cell_rejects_run_root_inside_tasks_root(tmp_path: Path) -> None:
    tasks_root = tmp_path / "tasks"
    task_dir = tasks_root / "task"
    (task_dir / "workspace").mkdir(parents=True)
    (task_dir / "checker.sh").write_text("#!/bin/sh\n")
    with pytest.raises(RuntimeError, match="overlaps hidden task/checker tree"):
        MODULE.run_cell(
            task="task",
            harness="pi",
            trial=1,
            tasks_root=tasks_root,
            run_base=tasks_root / "runs",
            executable=tmp_path / "pi",
            tool_root=tmp_path / "tools",
            api_key="unused",
            timeout_seconds=1,
        )


def test_prime_shutdown_timeout_forces_exact_survivors(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    socket = tmp_path / "prime.sock"
    socket.touch()
    ps_outputs = iter(
        [
            f"123 1 node {socket}\n124 123 worker\n",
            "",
        ]
    )
    lsof_outputs = iter(["123\n", ""])

    def fake_run(command: list[str], **_kwargs: object) -> Mock:
        if command[0] == "/usr/bin/sandbox-exec":
            raise MODULE.subprocess.TimeoutExpired(command, 35)
        if command[0] == "ps":
            return Mock(stdout=next(ps_outputs))
        if command[0] == "/usr/sbin/lsof":
            return Mock(stdout=next(lsof_outputs))
        raise AssertionError(command)

    def fake_kill(_pid: int, sig: int) -> None:
        if sig == 0:
            raise ProcessLookupError

    monkeypatch.setattr(MODULE.subprocess, "run", fake_run)
    monkeypatch.setattr(MODULE.os, "kill", fake_kill)
    result = MODULE.shutdown_prime_daemon(
        tmp_path / "prime" / "node_modules" / ".bin" / "prime-agent",
        socket,
        "(version 1)",
        tmp_path,
        {},
        tmp_path / "home",
        tmp_path / "temp",
    )
    assert result == {
        "targeted_shutdown": False,
        "forced_descendant_pids": [123, 124],
        "shutdown_error": "Targeted Prime daemon shutdown timed out after 35 seconds",
    }
