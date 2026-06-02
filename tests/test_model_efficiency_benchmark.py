"""Smoke tests for the model-efficiency (M4) benchmark."""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
M4_ROOT = REPO_ROOT / "benchmarks" / "model_efficiency"
RUNNER = M4_ROOT / "pipelines" / "run_model_efficiency.py"


def test_m4_harness_smoke(tmp_path: Path) -> None:
    out = tmp_path / "m4"
    proc = subprocess.run(
        [
            sys.executable,
            str(RUNNER),
            "--harness-only",
            "--tasks",
            "email_validator",
            "--runs",
            "1",
            "--output-dir",
            str(out),
            "--json",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout
    manifest = json.loads(proc.stdout)
    assert manifest["milestone"] == 4
    assert manifest["summary"]["headline"].startswith("M4:")
    cells = manifest["cells"]
    assert len(cells) == 4  # 2 tiers × 2 arms × 1 run
    a1_cells = [c for c in cells if c["arm"] == "A1"]
    assert all(c["economics"]["test_source"] == "pdd_fixtures" for c in a1_cells)
    assert (out / "email_validator" / "A1.prompt").is_file()
    comp = manifest["core_comparison"]
    assert "budget_A1" in comp
    assert "smart_A0" in comp


def test_m4_metrics_module() -> None:
    sys.path.insert(0, str(M4_ROOT / "pipelines"))
    from metrics import aggregate_cells, generation_success  # noqa: E402

    cells = [
        {
            "tier": "budget",
            "arm": "A1",
            "economics": {
                "cost_usd": 0.1,
                "oracle_test_pass_rate": 1.0,
                "rounds_to_green": 1,
                "generation_success": True,
            },
        },
        {
            "tier": "smart",
            "arm": "A0",
            "economics": {
                "cost_usd": 0.5,
                "oracle_test_pass_rate": 0.5,
                "rounds_to_green": 3,
                "generation_success": False,
            },
        },
    ]
    assert generation_success(cells[0]["economics"]) is True
    agg = aggregate_cells(cells)
    assert agg["success_count"] == 1
    assert agg["cost_per_success"] == 0.6
