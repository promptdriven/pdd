from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
BENCH_DIR = REPO_ROOT / "research" / "agentic-config-benchmark"


def _load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


run_benchmark = _load_module("agentic_config_run_benchmark_integration", BENCH_DIR / "run_benchmark.py")


def _axis(tmp_path: Path, configs: list[dict], *, repeat_runs: int = 1) -> Path:
    axis = {
        "locked_invariants": {
            "task_id": "task-a",
            "seed": "seed-a",
            "visible_tests_sha256": "v",
            "hidden_verifier_sha256": "h",
            "materialized_repo_sha256": "r",
            "timeout_seconds": 60,
            "repeat_runs": repeat_runs,
        },
        "configs": configs,
        "scheduling_rules": {
            "thinking_eligible_reasoning_types": ["effort", "budget"],
        },
    }
    path = tmp_path / "axis.json"
    path.write_text(json.dumps(axis))
    return path


def _config(**overrides):
    config = {
        "label": "cell",
        "harness_id": "pdd-agentic-cli",
        "harness_version": "1.0.0",
        "model_id": "model-a",
        "thinking_enabled": False,
        "thinking_effort": None,
        "interactive_only": False,
        "reasoning_type": "none",
    }
    config.update(overrides)
    return config


def _outcome():
    return {
        "hidden_pass": None,
        "visible_pass": None,
        "failure_class": None,
        "cost_usd": None,
        "cost_source": "unavailable",
        "input_tokens": None,
        "output_tokens": None,
        "wall_clock_seconds": 0.0,
        "timed_out": False,
        "files_read_before_first_edit": None,
        "files_read_source": "unavailable",
        "wrong_file_edit_count": None,
        "raw_trace_path": None,
    }


def test_dry_run_writes_one_record_per_trial(tmp_path, monkeypatch):
    reports_dir = tmp_path / "reports"
    monkeypatch.setattr(run_benchmark, "REPORTS_DIR", reports_dir)
    monkeypatch.setattr(
        run_benchmark,
        "load_model_registry",
        lambda _path: {"model-a": {"interactive_only": False, "reasoning_type": "none"}},
    )

    run_benchmark.run_sweep(
        axis_path=_axis(tmp_path, [_config()], repeat_runs=2),
        dry_run=True,
        cell_filter=None,
        materialized_repo_path=None,
    )

    lines = list(reports_dir.glob("*.jsonl"))[0].read_text().splitlines()
    records = [json.loads(line) for line in lines]
    assert [record["repeat_run_index"] for record in records] == [0, 1]
    assert all(record["seed_locked"] == "seed-a" for record in records)


def test_real_run_checks_harness_before_scheduling(tmp_path, monkeypatch):
    monkeypatch.setattr(run_benchmark, "REPORTS_DIR", tmp_path / "reports")
    monkeypatch.setattr(run_benchmark, "load_model_registry", lambda _path: {})
    checked = {"value": False}

    def fake_check():
        checked["value"] = True
        raise SystemExit("missing harness")

    monkeypatch.setattr(run_benchmark, "_check_harness_command_available", fake_check)
    monkeypatch.setattr(run_benchmark, "invoke_harness", pytest.fail)

    with pytest.raises(SystemExit, match="missing harness"):
        run_benchmark.run_sweep(
            axis_path=_axis(tmp_path, [_config()]),
            dry_run=False,
            cell_filter=None,
            materialized_repo_path=None,
        )

    assert checked["value"] is True


def test_registry_interactive_only_skips_config_even_if_axis_says_false(tmp_path, monkeypatch):
    reports_dir = tmp_path / "reports"
    monkeypatch.setattr(run_benchmark, "REPORTS_DIR", reports_dir)
    monkeypatch.setattr(
        run_benchmark,
        "load_model_registry",
        lambda _path: {"model-a": {"interactive_only": True, "reasoning_type": "effort"}},
    )
    monkeypatch.setattr(run_benchmark, "invoke_harness", pytest.fail)

    run_benchmark.run_sweep(
        axis_path=_axis(tmp_path, [_config(interactive_only=False)]),
        dry_run=True,
        cell_filter=None,
        materialized_repo_path=None,
    )

    assert not list(reports_dir.glob("*.jsonl"))


def test_thinking_gate_uses_registry_reasoning_type(tmp_path, monkeypatch):
    reports_dir = tmp_path / "reports"
    monkeypatch.setattr(run_benchmark, "REPORTS_DIR", reports_dir)
    monkeypatch.setattr(
        run_benchmark,
        "load_model_registry",
        lambda _path: {"model-a": {"interactive_only": False, "reasoning_type": "none"}},
    )
    monkeypatch.setattr(run_benchmark, "invoke_harness", pytest.fail)

    run_benchmark.run_sweep(
        axis_path=_axis(tmp_path, [_config(thinking_enabled=True, thinking_effort="medium", reasoning_type="effort")]),
        dry_run=True,
        cell_filter=None,
        materialized_repo_path=None,
    )

    assert not list(reports_dir.glob("*.jsonl"))


def test_budget_reasoning_type_is_thinking_eligible(tmp_path, monkeypatch):
    reports_dir = tmp_path / "reports"
    monkeypatch.setattr(run_benchmark, "REPORTS_DIR", reports_dir)
    monkeypatch.setattr(
        run_benchmark,
        "load_model_registry",
        lambda _path: {"model-a": {"interactive_only": False, "reasoning_type": "budget"}},
    )
    calls = []

    def fake_invoke(**kwargs):
        calls.append(kwargs)
        return _outcome()

    monkeypatch.setattr(run_benchmark, "invoke_harness", fake_invoke)

    run_benchmark.run_sweep(
        axis_path=_axis(tmp_path, [_config(thinking_enabled=True, thinking_effort="medium")]),
        dry_run=True,
        cell_filter=None,
        materialized_repo_path=None,
    )

    assert len(calls) == 1


def test_all_axis_models_resolve_and_are_schedulable_in_real_registry():
    axis = json.loads((BENCH_DIR / "benchmark_config_axis.json").read_text())
    registry = run_benchmark.load_model_registry(REPO_ROOT / "pdd" / "data" / "llm_model.csv")
    eligible = set(axis["scheduling_rules"]["thinking_eligible_reasoning_types"])

    for config in axis["configs"]:
        model_meta = registry.get(config["model_id"])
        assert model_meta is not None, config["model_id"]
        assert model_meta["interactive_only"] is False
        if config["thinking_enabled"]:
            assert model_meta["reasoning_type"] in eligible
