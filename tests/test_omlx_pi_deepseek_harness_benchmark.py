"""Offline unit tests for the Pi/DeepSeek Harness benchmark helpers."""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path
from unittest.mock import ANY, Mock

import pytest


MODULE_PATH = (
    Path(__file__).parents[1]
    / "research"
    / "omlx-qwen38-pi-deepseek-harness-2026-08-23"
    / "benchmark.py"
)
SPEC = importlib.util.spec_from_file_location("pi_dsh_benchmark", MODULE_PATH)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)

ANALYZE_PATH = MODULE_PATH.with_name("analyze.py")
ANALYZE_SPEC = importlib.util.spec_from_file_location("pi_dsh_analyze", ANALYZE_PATH)
assert ANALYZE_SPEC and ANALYZE_SPEC.loader
ANALYZE = importlib.util.module_from_spec(ANALYZE_SPEC)
sys.modules[ANALYZE_SPEC.name] = ANALYZE
ANALYZE_SPEC.loader.exec_module(ANALYZE)


def test_build_schedule_balances_order() -> None:
    schedule = MODULE.build_schedule(("one", "two"), 2)
    assert schedule == [
        (1, "one", "pi"),
        (1, "one", "dsh"),
        (1, "two", "dsh"),
        (1, "two", "pi"),
        (2, "one", "dsh"),
        (2, "one", "pi"),
        (2, "two", "pi"),
        (2, "two", "dsh"),
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


def test_write_pi_model_config_contains_no_real_secret(tmp_path: Path) -> None:
    MODULE.write_pi_model_config(tmp_path, 8123)
    payload = json.loads((tmp_path / "models.json").read_text())
    provider = payload["providers"]["omlx-benchmark"]
    assert provider["apiKey"] == "loopback-proxy"
    assert provider["baseUrl"] == "http://127.0.0.1:8123/v1"


def test_write_dsh_config_pins_proxy_model_and_fairness_controls(
    tmp_path: Path,
) -> None:
    patch = MODULE.write_dsh_config(tmp_path, 8123)
    settings = (tmp_path / "settings.yaml").read_text()
    overlay = patch.read_text()
    assert "baseURL: http://127.0.0.1:8123/v1" in settings
    assert f"id: {MODULE.MODEL_ID}" in settings
    assert "api: openai-completions" in settings
    assert "maxTokens: 32000" in settings
    assert "reasoning: medium" in settings
    assert "maxRetries: 0" in settings
    assert "supportsDeveloperRole: false" in settings
    assert "supportsReasoningEffort: false" in settings
    assert "thinkingFormat: qwen-chat-template" in settings
    assert "OMLX_BENCHMARK_API_KEY" in settings
    assert "loopback-proxy" not in settings
    assert "provider: omlx-benchmark" in overlay
    for row in ("tool-web", "tool-skill", "tool-subagent", "tool-workflow"):
        assert f"id: {row}" in overlay


def test_published_tool_locks_pin_actual_transport_versions() -> None:
    lock_root = MODULE_PATH.parent / "tool-lock"
    pi_lock = json.loads((lock_root / "pi" / "package-lock.json").read_text())
    dsh_lock = json.loads((lock_root / "dsh" / "package-lock.json").read_text())
    assert pi_lock["packages"]["node_modules/@mariozechner/pi-coding-agent"][
        "version"
    ] == MODULE.PI_VERSION
    assert pi_lock["packages"]["node_modules/@mariozechner/pi-ai"]["version"] == "0.73.1"
    assert dsh_lock["packages"]["node_modules/@deepseek-ai/dsh"][
        "version"
    ] == MODULE.DSH_VERSION
    assert dsh_lock["packages"]["node_modules/@earendil-works/pi-ai"][
        "version"
    ] == "0.82.1"


def test_sandbox_profile_allows_only_proxy_network_and_scoped_writes(
    tmp_path: Path,
) -> None:
    workspace = tmp_path / "run" / "workspace"
    home = tmp_path / "run" / "home"
    temp_dir = tmp_path / "run" / "tmp"
    profile = MODULE.sandbox_profile(
        tmp_path / "run",
        workspace,
        home,
        tmp_path / "tools",
        temp_dir,
        8123,
    )
    assert '(allow network-outbound (remote ip "localhost:8123"))' in profile
    assert f'(subpath "{workspace}")' in profile
    assert f'(subpath "{home}")' in profile
    for name in MODULE.TOOL_SUBDIRECTORIES:
        assert f'(subpath "{(tmp_path / "tools" / name).resolve()}")' in profile
    assert f'(subpath "{tmp_path / "tools"}")' not in profile
    assert "(deny network*)" in profile


def test_hidden_grader_boundary_rejects_overlap_with_read_root(tmp_path: Path) -> None:
    tool_root = tmp_path / "tools"
    for name in MODULE.TOOL_SUBDIRECTORIES:
        (tool_root / name).mkdir(parents=True)
    tasks_root = tool_root / "pi" / "tasks"
    tasks_root.mkdir()
    with pytest.raises(RuntimeError, match="overlaps"):
        MODULE.validate_hidden_grader_boundary(tasks_root, (), tool_root)


def test_root_separation_rejects_run_root_inside_readable_tool_root(
    tmp_path: Path,
) -> None:
    tool_root = tmp_path / "tools"
    for name in MODULE.TOOL_SUBDIRECTORIES:
        (tool_root / name).mkdir(parents=True)
    tasks_root = tmp_path / "tasks"
    tasks_root.mkdir()
    with pytest.raises(RuntimeError, match="Overlapping benchmark roots"):
        MODULE.validate_root_separation(
            tasks_root, tool_root, tool_root / "dsh" / "raw-runs"
        )


def test_checker_sandbox_denies_network_and_limits_writes(tmp_path: Path) -> None:
    task_dir = tmp_path / "tasks" / "one"
    workspace = tmp_path / "workspace"
    temp_dir = tmp_path / "checker-temp"
    profile = MODULE.checker_sandbox_profile(task_dir, workspace, temp_dir)
    assert "(deny network*)" in profile
    assert f'(subpath "{task_dir}")' in profile
    assert f'(subpath "{workspace}")' in profile
    assert f'(subpath "{temp_dir}")' in profile
    assert f'(subpath "{Path(sys.prefix).resolve()}")' in profile
    assert f'(subpath "{Path.home()}")' not in profile


def test_grade_task_invokes_current_python_directly(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    task_dir = tmp_path / "task"
    workspace = tmp_path / "workspace"
    (task_dir / "checker_data").mkdir(parents=True)
    workspace.mkdir()
    checker_temp = tmp_path / "checker-temp"
    checker_temp.mkdir()
    temporary_directory = Mock()
    temporary_directory.return_value.__enter__ = Mock(
        return_value=str(checker_temp)
    )
    temporary_directory.return_value.__exit__ = Mock(return_value=False)
    monkeypatch.setattr(
        MODULE, "tempfile", Mock(TemporaryDirectory=temporary_directory)
    )
    completed = Mock(returncode=0, stdout="SCORE: 1.0\n", stderr="")
    run = Mock(return_value=completed)
    monkeypatch.setattr(MODULE.subprocess, "run", run)
    result = MODULE.grade_task(task_dir, workspace)
    command = run.call_args.args[0]
    assert command[-2:] == [
        sys.executable,
        str(task_dir / "checker_data" / "run_score.py"),
    ]
    temporary_directory.assert_called_once_with(prefix="checker-", dir="/private/tmp")
    assert result["passed"] is True


def test_validate_tasks_rejects_unpinned_tree_before_checker(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    task = MODULE.DEFAULT_TASKS[0]
    task_dir = tmp_path / task
    task_dir.mkdir()
    grade = Mock()
    monkeypatch.setattr(MODULE, "sha256_tree", Mock(return_value="wrong"))
    monkeypatch.setattr(MODULE, "grade_task", grade)
    with pytest.raises(RuntimeError, match="Pinned task hash mismatch"):
        MODULE.validate_tasks(tmp_path, (task,))
    grade.assert_not_called()


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


def test_cleanup_marked_processes_targets_only_exact_cell(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        MODULE.subprocess,
        "run",
        lambda *_args, **_kwargs: Mock(
            stdout="123 node /tmp/cell-home\n456 node /tmp/other-home\n"
        ),
    )
    signals: list[tuple[int, int]] = []

    def fake_kill(pid: int, sig: int) -> None:
        signals.append((pid, sig))
        if sig == 0:
            raise ProcessLookupError

    monkeypatch.setattr(MODULE.os, "kill", fake_kill)
    assert MODULE.cleanup_marked_processes(("/tmp/cell-home",)) == [123]
    assert signals == [(123, MODULE.signal.SIGTERM), (123, 0)]


def test_set_memory_guard_posts_and_verifies() -> None:
    session = Mock()
    response = Mock()
    response.json.return_value = {"memory": {"memory_guard_tier": "balanced"}}
    session.post.return_value = response
    session.get.return_value = response
    MODULE.set_memory_guard_tier(session, "balanced")
    session.post.assert_called_once_with(
        f"{MODULE.BASE_URL}/admin/api/global-settings",
        json={"memory_guard_tier": "balanced"},
        timeout=30,
    )


def test_record_post_run_verification_is_secret_free(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text('{"model": "example"}\n')
    session = Mock()
    monkeypatch.setattr(MODULE, "wait_omlx_idle", Mock())
    monkeypatch.setattr(MODULE, "get_memory_guard_tier", Mock(return_value="balanced"))
    MODULE.record_post_run_verification(manifest_path, session, "secret")
    payload = json.loads(manifest_path.read_text())
    evidence = payload["post_run_verification"]
    assert evidence["memory_guard_final_tier"] == "balanced"
    assert evidence["two_consecutive_idle_samples"] is True
    assert evidence["active_requests"] == 0
    assert evidence["waiting_requests"] == 0
    assert "secret" not in manifest_path.read_text()


def test_restore_runtime_state_restores_balanced_after_idle_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    idle = Mock(side_effect=TimeoutError("still active"))
    restore = Mock()
    record = Mock()
    monkeypatch.setattr(MODULE, "wait_omlx_idle", idle)
    monkeypatch.setattr(MODULE, "set_memory_guard_tier", restore)
    monkeypatch.setattr(MODULE, "record_post_run_verification", record)
    with pytest.raises(RuntimeError, match="restored to balanced"):
        MODULE.restore_runtime_state(tmp_path / "manifest.json", Mock(), "secret")
    restore.assert_called_once_with(ANY, "balanced")
    record.assert_not_called()


def test_proxy_identity_requires_exact_model_and_serial_requests(tmp_path: Path) -> None:
    log_path = tmp_path / "proxy.jsonl"
    log_path.write_text(
        "\n".join(
            [
                json.dumps(
                    {
                        "event": "request",
                        "request_id": "one",
                        "method": "POST",
                        "path": "/v1/chat/completions",
                        "model": MODULE.MODEL_ID,
                        "started_at": 1.0,
                        "max_tokens": 32000,
                        "temperature": None,
                        "top_p": None,
                        "reasoning_effort": None,
                        "chat_template_kwargs": {"enable_thinking": True},
                        "tools": 4,
                    }
                ),
                json.dumps(
                    {
                        "event": "response",
                        "request_id": "one",
                        "finished_at": 2.0,
                    }
                ),
            ]
        )
        + "\n"
    )
    identity = MODULE.assert_proxy_identity(log_path)
    assert identity["verified"] is True
    assert identity["model"] == MODULE.MODEL_ID
    assert identity["max_tokens"] == [32000]


def test_smoke_gate_rejects_request_setting_drift() -> None:
    base = {
        "harness_result": {"timed_out": False, "returncode": 0},
        "proxy_totals": {"failures": 0},
        "grade": {"checker_exit": 0},
        "proxy_identity": {
            "verified": True,
            "max_tokens": [32000],
            "temperature": [None],
            "top_p": [None],
            "reasoning_effort": [None],
            "chat_template_kwargs": [{"enable_thinking": True}],
        },
    }
    pi = json.loads(json.dumps(base))
    dsh = json.loads(json.dumps(base))
    dsh["proxy_identity"]["max_tokens"] = [32768]
    with pytest.raises(RuntimeError, match="request settings differ"):
        MODULE.assert_smoke_gate({"pi": pi, "dsh": dsh})


def test_analyzer_rejects_incomplete_matrix() -> None:
    manifest = {
        "tasks": ["one"],
        "trials": 1,
        "model": MODULE.MODEL_ID,
        "task_hashes": {"one": "hash"},
        "post_run_verification": {
            "memory_guard_final_tier": "balanced",
            "two_consecutive_idle_samples": True,
            "active_requests": 0,
            "waiting_requests": 0,
        },
    }
    with pytest.raises(RuntimeError, match="Incomplete benchmark matrix"):
        ANALYZE.validate_rows([], manifest)


def test_analyzer_rejects_missing_restoration_evidence() -> None:
    with pytest.raises(RuntimeError, match="restoration evidence"):
        ANALYZE.validate_rows([], {"tasks": [], "trials": 0})


def test_analyzer_binds_checker_revalidation_to_original_grade() -> None:
    rows = [
        {
            "run_id": "01-one-pi",
            "grade": {"checker_exit": 0, "passed": True, "score": 1.0},
        }
    ]
    evidence = {
        "rows": 1,
        "all_scores_passes_and_exits_match_original": True,
        "interpreter_policy": "benchmark_orchestrator_sys.executable",
        "results": [
            {
                "run_id": "01-one-pi",
                "checker_exit": 0,
                "passed": True,
                "score": 0.5,
                "matched_original": True,
            }
        ],
    }
    with pytest.raises(RuntimeError, match="revalidation mismatch"):
        ANALYZE.validate_checker_revalidation(rows, evidence)


def test_analyzer_rejects_full_cell_request_setting_drift() -> None:
    manifest = {
        "tasks": ["one"],
        "trials": 1,
        "model": MODULE.MODEL_ID,
        "task_hashes": {"one": "hash"},
        "post_run_verification": {
            "memory_guard_final_tier": "balanced",
            "two_consecutive_idle_samples": True,
            "active_requests": 0,
            "waiting_requests": 0,
        },
    }
    rows = []
    for harness in ("pi", "dsh"):
        identity = {
            "verified": True,
            "serial_requests": True,
            "model": MODULE.MODEL_ID,
            "base_url": "http://127.0.0.1:8000",
            "path": "/v1/chat/completions",
            "completion_requests": 1,
            "tool_counts": ANALYZE.EXPECTED_TOOL_COUNTS[harness],
            **ANALYZE.EXPECTED_REQUEST_FIELDS,
        }
        rows.append(
            {
                "run_id": f"01-one-{harness}",
                "phase": "benchmark",
                "task": "one",
                "task_sha256": "hash",
                "harness": harness,
                "trial": 1,
                "model": MODULE.MODEL_ID,
                "proxy_identity": identity,
                "proxy_totals": {"requests": 1},
            }
        )
    rows[0]["proxy_identity"]["max_tokens"] = [32768]
    with pytest.raises(RuntimeError, match="request-setting drift"):
        ANALYZE.validate_rows(rows, manifest)


def test_analyzer_rejects_run_id_metadata_mismatch() -> None:
    manifest = {
        "tasks": ["one"],
        "trials": 1,
        "model": MODULE.MODEL_ID,
        "task_hashes": {"one": "hash"},
        "post_run_verification": {
            "memory_guard_final_tier": "balanced",
            "two_consecutive_idle_samples": True,
            "active_requests": 0,
            "waiting_requests": 0,
        },
    }
    rows = [
        {
            "run_id": f"01-one-{harness}",
            "phase": "benchmark",
            "task": "one",
            "task_sha256": "hash",
            "harness": harness,
            "trial": 2 if harness == "pi" else 1,
        }
        for harness in ("pi", "dsh")
    ]
    with pytest.raises(RuntimeError, match="Run ID metadata mismatch"):
        ANALYZE.validate_rows(rows, manifest)


def test_sanitizer_whitelists_result_fields() -> None:
    row = {
        "schema_version": 2,
        "run_id": "01-one-pi",
        "phase": "benchmark",
        "task": "one",
        "task_sha256": "hash",
        "harness": "pi",
        "trial": 1,
        "model": MODULE.MODEL_ID,
        "thinking": "medium",
        "timeout_seconds": 1200,
        "harness_result": {
            "returncode": 0,
            "timed_out": False,
            "wall_seconds": 1.0,
            "stdout_bytes": 1,
            "stderr_bytes": 2,
            "stderr_tail": "secret transcript path",
            "forced_residual_pids": [],
        },
        "proxy_totals": {"requests": 1},
        "proxy_identity": {"verified": True},
        "grade": {
            "checker_exit": 0,
            "score": 1.0,
            "passed": True,
            "output": "hidden checker text",
        },
        "changes": {"changed_files": 1},
        "finished_at": "2026-08-23T00:00:00-0700",
    }
    clean = ANALYZE.sanitize_row(row)
    assert "stderr_tail" not in clean["harness_result"]
    assert "output" not in clean["grade"]
