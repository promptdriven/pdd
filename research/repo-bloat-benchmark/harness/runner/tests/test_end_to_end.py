"""End-to-end pipeline test on the committed example scenario — no model
tokens, no network beyond loopback.

Exercises: manifest generation + lock → freeze check → sha-verified variant
materialization → git baseline → mock provider + real recording proxy →
scripted agent traffic (real file contents surfaced into requests) →
visible/hidden verification → attribution → trajectory → run record →
report. This is the §6.6 calibration principle applied to the whole pipeline.
"""

import json
from pathlib import Path

import pytest

from harness.distractors.generator import GenerationConfig, generate_manifest
from harness.distractors.manifest import ManifestWriter, write_lockfile
from harness.runner.report import generate_report
from harness.runner.runner import ExperimentRunner, RunConfig

SCENARIO_DIR = Path(__file__).resolve().parents[3] / "scenarios" / "example-pagination"


@pytest.fixture(scope="module")
def distractors_dir(tmp_path_factory):
    """Generate + freeze manifests for the example scenario (1x and 5x)."""
    out = tmp_path_factory.mktemp("distractors")
    scenario = json.loads((SCENARIO_DIR / "scenario.json").read_text())
    config = GenerationConfig(
        scenario_id=scenario["scenario_id"],
        core_root=SCENARIO_DIR / "core",
        pool_root=SCENARIO_DIR / "pool",
        target_file=scenario["target_files"][0],
        leak_denylist=tuple(scenario["leak_denylist"]),
        template_file_tokens=150,
    )
    writer = ManifestWriter(out)
    paths = [writer.write(generate_manifest(config, size)) for size in (1, 5)]
    write_lockfile(paths, out / "manifests.lock")
    return out


def _runner(tmp_path, distractors_dir, behavior):
    return ExperimentRunner(
        RunConfig(
            scenario_dir=SCENARIO_DIR,
            distractors_dir=distractors_dir,
            reports_dir=tmp_path / "reports",
            work_root=tmp_path / "work",
            arm="mock",
            mock_behavior=behavior,
        )
    )


def test_oracle_agent_passes_hidden_at_1x(tmp_path, distractors_dir):
    result = _runner(tmp_path, distractors_dir, "oracle").run_trial(1, 0)
    record = result.record
    assert record["visible_pass"]
    assert record["hidden_pass"]
    assert record["failure_class"] is None
    assert record["iterations_total"] >= 3
    assert record["input_tokens_per_run"] > 0
    assert record["distractor_tokens_on_disk"] == 0
    # Edit landed on the target, in scope.
    assert record["edit_classes"]["target"] == ["src/pager/pagination.py"]
    # Raw artifacts exist for third-party re-derivation.
    assert (result.report_dir / "context_snapshots.jsonl").is_file()
    assert (result.report_dir / "run_record.json").is_file()


def test_oracle_agent_passes_hidden_at_5x_with_penetration(tmp_path, distractors_dir):
    result = _runner(tmp_path, distractors_dir, "oracle").run_trial(5, 0)
    record = result.record
    assert record["hidden_pass"]
    # The mock agent read distractor files into context → penetration > 0.
    assert record["distractor_context_tokens_total"] > 0
    assert record["distractor_files_entered_context"] >= 1
    assert 0 < record["distractor_pool_coverage"] <= 1
    assert record["growth_shape"] in {"gradual", "step", "plateau", "sawtooth"}


def test_wrong_file_agent_classified(tmp_path, distractors_dir):
    result = _runner(tmp_path, distractors_dir, "wrong_file").run_trial(5, 0)
    record = result.record
    assert record["visible_pass"]  # nothing behavioral changed in core
    assert not record["hidden_pass"]
    assert record["failure_class"] == "wrong_file_edit"
    assert record["edit_classes"]["wrong_file"]
    assert record["wrong_file_edit_rate"] == 1.0


def test_noop_agent_is_hidden_contract_miss(tmp_path, distractors_dir):
    result = _runner(tmp_path, distractors_dir, "noop").run_trial(5, 0)
    record = result.record
    assert record["visible_pass"]
    assert not record["hidden_pass"]
    # The mock agent read the target into context, so not a localization miss.
    assert record["failure_class"] == "hidden_contract_miss"
    assert record["iterations_before_first_edit"] is None


def test_freeze_violation_refuses_to_run(tmp_path, distractors_dir):
    manifest_path = (
        distractors_dir / "manifests" / "example-pagination.5x.json"
    )
    original = manifest_path.read_text()
    manifest_path.write_text(original.replace("example-pagination", "example-pagination") + "\n")
    try:
        with pytest.raises(RuntimeError, match="freeze violation"):
            _runner(tmp_path, distractors_dir, "oracle").run_trial(5, 1)
    finally:
        manifest_path.write_text(original)


def test_report_renders_from_records(tmp_path, distractors_dir):
    runner = _runner(tmp_path, distractors_dir, "oracle")
    records = [runner.run_trial(size, 0).record for size in (1, 5)]
    report = generate_report(records)
    assert "`hidden_pass_rate`" in report
    assert "| Metric | 1x | 5x |" in report
    assert "Pre-registered thresholds" in report
