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


def _target_basenames() -> set[str]:
    names = set()
    for scenario_id in PILOT_SCENARIOS:
        scenario = json.loads(
            (BENCH_ROOT / "scenarios" / scenario_id / "scenario.json").read_text()
        )
        for target in scenario["target_files"]:
            names.add(Path(target).name)
    return names


@pytest.mark.parametrize("scenario_id", PILOT_SCENARIOS)
def test_pool_has_no_sibling_target_module(scenario_id):
    """A scenario's distractor pool must not ship another scenario's target
    module (which would leak the sibling's solved code — adversarial #5)."""
    targets = _target_basenames()
    pool = BENCH_ROOT / "scenarios" / scenario_id / "pool" / "src" / "pdd"
    for pool_file in pool.glob("*.py"):
        assert pool_file.name not in targets, (
            f"{scenario_id} pool ships target module {pool_file.name}"
        )


def test_no_scenario_denylist_string_leaks_into_any_agent_visible_tree():
    """No pilot scenario's leak-denylist string may appear in ANY scenario's
    agent-visible content (pool + generated distractors) — cross-scenario
    contamination guard (adversarial #5)."""
    denylists = {}
    for scenario_id in PILOT_SCENARIOS:
        lines = (BENCH_ROOT / "scenarios" / scenario_id / "leak_denylist.txt").read_text()
        denylists[scenario_id] = [
            l.strip() for l in lines.splitlines() if l.strip()
        ]
    visible_files = []
    for scenario_id in PILOT_SCENARIOS:
        visible_files += list(
            (BENCH_ROOT / "scenarios" / scenario_id / "pool").rglob("*.py")
        )
        visible_files += list(
            (BENCH_ROOT / "distractors" / scenario_id / "generated").rglob("*.py")
        )
    blobs = {f: f.read_text(encoding="utf-8", errors="replace") for f in visible_files}
    for owner, needles in denylists.items():
        for needle in needles:
            for path, blob in blobs.items():
                assert needle not in blob, (
                    f"denylist string from {owner} leaked into {path}"
                )


def test_calibration_gate_still_green(tmp_path):
    assert calibration_gate(tmp_path)["pass"]


def _declared_core_files(path: Path) -> set[str]:
    entries = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        item = line.split("#", 1)[0].strip()
        if item:
            entries.add(item)
    return entries


@pytest.mark.parametrize("scenario_id", PILOT_SCENARIOS)
def test_core_files_manifest_matches_core_tree(scenario_id):
    scenario_dir = BENCH_ROOT / "scenarios" / scenario_id
    declared = _declared_core_files(scenario_dir / "core_files.txt")
    actual = {
        path.relative_to(scenario_dir / "core").as_posix()
        for path in (scenario_dir / "core").rglob("*")
        if path.is_file()
    }
    assert declared == actual
