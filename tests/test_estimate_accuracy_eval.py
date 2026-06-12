import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest


def _load_eval_module():
    script = Path(__file__).resolve().parents[1] / "scripts" / "estimate_accuracy_eval.py"
    spec = importlib.util.spec_from_file_location("estimate_accuracy_eval", script)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_replay_actuals_compute_accuracy_without_live_execution(monkeypatch, capsys):
    module = _load_eval_module()
    root = Path(__file__).resolve().parents[1]
    cases = root / "tests" / "fixtures" / "estimate_accuracy" / "cases.jsonl"
    actuals = root / "tests" / "fixtures" / "estimate_accuracy" / "actuals.jsonl"

    estimate_payloads = {
        "tiny-generate": {
            "estimate": True,
            "input_tokens": 100,
            "predicted_output_tokens": 50,
            "estimated_cost": 0.0004,
            "unknown_cost": False,
        },
        "parser-generate": {
            "estimate": True,
            "input_tokens": 200,
            "predicted_output_tokens": 80,
            "estimated_cost": 0.00072,
            "unknown_cost": False,
        },
    }
    calls = []

    def fake_run_pdd(command, cwd):
        calls.append(command)
        assert "--force" not in command
        assert "--output-cost" not in command
        command_text = " ".join(command)
        if "tiny_function_python.prompt" in command_text:
            payload = estimate_payloads["tiny-generate"]
        else:
            payload = estimate_payloads["parser-generate"]
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=json.dumps(payload) + "\n",
            stderr="",
        )

    monkeypatch.setattr(module, "_run_pdd", fake_run_pdd)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "estimate_accuracy_eval.py",
            "--cases",
            str(cases),
            "--actuals",
            str(actuals),
            "--cwd",
            str(root),
        ],
    )

    assert module.main() == 0
    captured = capsys.readouterr()
    summary = json.loads(captured.out)

    assert len(calls) == 2
    assert summary["live_actuals"] is False
    assert summary["replay_actuals"] is True
    assert summary["passes_target"] is True
    assert summary["median_ape"] <= 0.15
    assert summary["p80_ape"] <= 0.15
    assert summary["p95_ape"] <= 0.25
    assert "using recorded actuals" in captured.err


def test_replay_actuals_loader_accepts_legacy_key_names():
    module = _load_eval_module()
    row = module._build_row(
        name="demo",
        estimate={
            "input_tokens": 100,
            "predicted_output_tokens": 50,
            "estimated_cost": 0.0004,
            "unknown_cost": False,
        },
        actual={"input_tokens": 100.0, "output_tokens": 40.0, "cost": 0.0005},
    )

    assert row["input_ape"] == 0.0
    assert row["output_ape"] == 0.25
    assert row["cost_ape"] == pytest.approx(0.2)


def test_fail_on_threshold_returns_nonzero_when_summary_fails(monkeypatch, tmp_path):
    module = _load_eval_module()
    cases = tmp_path / "cases.jsonl"
    actuals = tmp_path / "actuals.jsonl"
    cases.write_text(
        '{"name":"bad","command":["generate","bad.prompt"]}\n',
        encoding="utf-8",
    )
    actuals.write_text(
        '{"name":"bad","actual_input_tokens":100,"actual_output_tokens":100,"actual_cost":0.001}\n',
        encoding="utf-8",
    )

    def fake_run_pdd(command, cwd):
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=json.dumps(
                {
                    "estimate": True,
                    "input_tokens": 10,
                    "predicted_output_tokens": 10,
                    "estimated_cost": 0.0001,
                    "unknown_cost": False,
                }
            )
            + "\n",
            stderr="",
        )

    monkeypatch.setattr(module, "_run_pdd", fake_run_pdd)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "estimate_accuracy_eval.py",
            "--cases",
            str(cases),
            "--actuals",
            str(actuals),
            "--fail-on-threshold",
        ],
    )

    assert module.main() == 1
