from __future__ import annotations

import importlib.util
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
BENCH_DIR = REPO_ROOT / "research" / "agentic-config-benchmark"


def _load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


run_benchmark = _load_module("agentic_config_run_benchmark", BENCH_DIR / "run_benchmark.py")
generate_report = _load_module("agentic_config_generate_report", BENCH_DIR / "generate_report.py")


def _outcome(**overrides):
    outcome = {
        "hidden_pass": True,
        "visible_pass": True,
        "failure_class": None,
        "cost_usd": 0.25,
        "cost_source": "provider_usage_api",
        "input_tokens": 100,
        "output_tokens": 50,
        "wall_clock_seconds": 12.5,
        "timed_out": False,
        "files_read_before_first_edit": 3,
        "files_read_source": "transcript_tap",
        "wrong_file_edit_count": 0,
        "raw_trace_path": None,
    }
    outcome.update(overrides)
    return outcome


def test_compute_config_sha256_is_order_independent():
    first = run_benchmark.compute_config_sha256("h", "1", "m", True, "medium")
    second = run_benchmark.compute_config_sha256(
        harness_version="1",
        harness_id="h",
        thinking_effort="medium",
        thinking_enabled=True,
        model_id="m",
    )

    assert first == second
    assert len(first) == 64


def test_build_run_record_includes_config_identity_and_locked_seed():
    config = {
        "label": "baseline",
        "config_rank": 0,
        "harness_id": "pdd-agentic-cli",
        "harness_version": "1.0.0",
        "model_id": "model-a",
        "thinking_enabled": False,
        "thinking_effort": None,
        "is_default_baseline": True,
        "model_rank_score": 10,
        "model_rank_source": "static-prefix",
        "reasoning_type": "none",
    }
    locked = {
        "task_id": "task-a",
        "seed": "seed-a",
        "visible_tests_sha256": "v",
        "hidden_verifier_sha256": "h",
        "materialized_repo_sha256": "r",
        "timeout_seconds": 1800,
        "repeat_runs": 5,
    }

    record = run_benchmark.build_run_record(
        config=config,
        task_id="task-a",
        trial_index=3,
        locked=locked,
        outcome=_outcome(),
        model_registry={},
    )

    assert record["config_label"] == "baseline"
    assert record["config_rank"] == 0
    assert record["trial_index"] == 3
    assert record["repeat_run_index"] == 3
    assert record["seed_locked"] == "seed-a"
    assert record["hash_verified"] is True


def test_deepswe_metadata_is_recorded_with_caveat():
    config = {
        "label": "stronger",
        "harness_id": "pdd-agentic-cli",
        "harness_version": "1.0.0",
        "model_id": "model-a",
        "thinking_enabled": False,
        "thinking_effort": None,
        "model_rank_score": 1,
        "model_rank_source": "static-prefix",
    }
    registry = {
        "model-a": {
            "model_rank_score": 15400.0,
            "model_rank_source": "deepswe-solve-rate",
            "reasoning_type": "effort",
            "interactive_only": False,
        }
    }

    record = run_benchmark.build_run_record(
        config=config,
        task_id="task-a",
        trial_index=0,
        locked={},
        outcome=_outcome(),
        model_registry=registry,
    )

    assert record["model_rank_score"] == 15400.0
    assert record["external_deepswe_rank_score"] == 15400.0
    assert "DeepSWE harness" in record["deepswe_rank_caveat"]


def test_render_report_sorts_config_rank_zero_first():
    report = generate_report.render_report(
        {
            "stronger": {
                "config_label": "stronger",
                "config_rank": 2,
                "is_default_baseline": False,
                "model_id": "model-b",
                "thinking_enabled": False,
                "has_deepswe": False,
                "n_hidden_valid": 1,
                "hidden_pass_k": 1,
                "n_hidden_null": 0,
                "cost_usd_median": None,
                "wall_clock_seconds_p50": None,
                "timeout_count": 0,
                "wrong_edit_count": 0,
                "n": 1,
                "files_read_before_first_edit_p50": None,
            },
            "baseline": {
                "config_label": "baseline",
                "config_rank": 0,
                "is_default_baseline": True,
                "model_id": "model-a",
                "thinking_enabled": False,
                "has_deepswe": False,
                "n_hidden_valid": 1,
                "hidden_pass_k": 0,
                "n_hidden_null": 0,
                "cost_usd_median": None,
                "wall_clock_seconds_p50": None,
                "timeout_count": 0,
                "wrong_edit_count": 0,
                "n": 1,
                "files_read_before_first_edit_p50": None,
            },
        }
    )

    assert report.index("**baseline**") < report.index("stronger")


def test_axis_uses_real_model_registry_column_name_and_locks_seed():
    axis = json.loads((BENCH_DIR / "benchmark_config_axis.json").read_text())

    assert "seed" in axis["locked_invariants"]
    assert axis["model_registry_fields_used"][0] == "model"
