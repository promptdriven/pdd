"""Regression pins for the committed real pilot scenarios.

Runs the §4.1.2 oracle-equivalence sweep against each committed scenario and
its committed, locked ladder manifests at the endpoint sizes — the same gate
the pilot must pass, so a drive-by edit to a scenario, a pool, or the
manifests fails here first. No model tokens; loopback only.
"""

import json
from pathlib import Path

import pytest

from harness.runner.preflight import calibration_gate, oracle_equivalence_sweep

BENCH_ROOT = Path(__file__).resolve().parents[3]
PILOT_SCENARIOS = (
    "pdd-find-section",
    "pdd-failure-classification",
    "pdd-language-extensions",
)


@pytest.mark.parametrize("scenario_id", PILOT_SCENARIOS)
def test_committed_scenario_passes_oracle_gate_at_endpoints(tmp_path, scenario_id):
    result = oracle_equivalence_sweep(
        scenario_dir=BENCH_ROOT / "scenarios" / scenario_id,
        distractors_dir=BENCH_ROOT / "distractors" / scenario_id,
        sizes=[1, 50],
        work_root=tmp_path,
    )
    assert result["pass"], json.dumps(result, indent=2)


@pytest.mark.parametrize("scenario_id", PILOT_SCENARIOS)
def test_committed_manifests_cover_full_ladder(scenario_id):
    distractors = BENCH_ROOT / "distractors" / scenario_id
    steps = {
        p.name.split(".")[1] for p in (distractors / "manifests").glob(f"{scenario_id}.*.json")
    }
    assert steps == {"1x", "2x", "5x", "10x", "20x", "50x"}
    assert (distractors / "manifests.lock").is_file()
    for manifest_path in (distractors / "manifests").glob(f"{scenario_id}.*.json"):
        manifest = json.loads(manifest_path.read_text())
        assert manifest["budget_met"], f"{manifest_path.name} budget not met"


@pytest.mark.parametrize("scenario_id", PILOT_SCENARIOS)
def test_seed_novelty_audit_is_committed_and_classified(scenario_id):
    scenario_dir = BENCH_ROOT / "scenarios" / scenario_id
    audit = (scenario_dir / "seed_novelty.md").read_text(encoding="utf-8")
    assert "upstream_recall_caveat" in audit or "`novel`" in audit
    scenario = json.loads((scenario_dir / "scenario.json").read_text())
    assert scenario["upstream"]["pinned_commit"]
    assert (scenario_dir / "seed.patch").is_file()
    assert (scenario_dir / "core_files.txt").is_file()
    assert (scenario_dir / "leak_denylist.txt").is_file()


@pytest.mark.parametrize("scenario_id", PILOT_SCENARIOS)
def test_pool_files_are_verbatim_upstream(scenario_id):
    """Regrow distractors must be the repo's own files, byte-for-byte."""
    pool = BENCH_ROOT / "scenarios" / scenario_id / "pool" / "src" / "pdd"
    repo_root = BENCH_ROOT.parents[1]
    for pool_file in pool.glob("*.py"):
        upstream = repo_root / "pdd" / pool_file.name
        assert upstream.is_file(), f"no upstream counterpart for {pool_file.name}"
        assert pool_file.read_bytes() == upstream.read_bytes(), (
            f"{scenario_id} pool file {pool_file.name} diverged from upstream"
        )


def test_calibration_gate_still_green(tmp_path):
    assert calibration_gate(tmp_path)["pass"]
