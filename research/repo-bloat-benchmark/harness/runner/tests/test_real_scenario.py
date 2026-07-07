"""Regression pin for the committed real scenario `pdd-find-section`.

Runs the §4.1.2 oracle-equivalence sweep against the committed scenario and
its committed, locked ladder manifests at the endpoint sizes — the same gate
the pilot must pass, so a drive-by edit to the scenario, the pool, or the
manifests fails here first. No model tokens; loopback only.
"""

import json
from pathlib import Path

from harness.runner.preflight import calibration_gate, oracle_equivalence_sweep

BENCH_ROOT = Path(__file__).resolve().parents[3]
SCENARIO_DIR = BENCH_ROOT / "scenarios" / "pdd-find-section"
DISTRACTORS_DIR = BENCH_ROOT / "distractors" / "pdd-find-section"


def test_committed_scenario_passes_oracle_gate_at_endpoints(tmp_path):
    result = oracle_equivalence_sweep(
        scenario_dir=SCENARIO_DIR,
        distractors_dir=DISTRACTORS_DIR,
        sizes=[1, 50],
        work_root=tmp_path,
    )
    assert result["pass"], json.dumps(result, indent=2)


def test_committed_manifests_cover_full_ladder():
    manifests = sorted(
        p.name for p in (DISTRACTORS_DIR / "manifests").glob("pdd-find-section.*.json")
    )
    assert manifests == [
        f"pdd-find-section.{s}x.json" for s in (10, 1, 20, 2, 50, 5)
    ] or {m.split(".")[1] for m in manifests} == {"1x", "2x", "5x", "10x", "20x", "50x"}
    assert (DISTRACTORS_DIR / "manifests.lock").is_file()


def test_seed_novelty_audit_is_committed_and_classified():
    audit = (SCENARIO_DIR / "seed_novelty.md").read_text(encoding="utf-8")
    assert "upstream_recall_caveat" in audit
    scenario = json.loads((SCENARIO_DIR / "scenario.json").read_text())
    assert scenario["upstream"]["pinned_commit"]
    assert (SCENARIO_DIR / "seed.patch").is_file()
    assert (SCENARIO_DIR / "core_files.txt").is_file()


def test_calibration_gate_still_green(tmp_path):
    assert calibration_gate(tmp_path)["pass"]
