"""Tests for the standalone pre-run gates (design §4.1.2 + §6.6)."""

import json
from pathlib import Path

import pytest

from harness.distractors.generator import GenerationConfig, generate_manifest
from harness.distractors.manifest import ManifestWriter, write_lockfile
from harness.runner.preflight import (
    apply_oracle_edit,
    calibration_gate,
    main,
    oracle_equivalence_sweep,
)

SCENARIO_DIR = Path(__file__).resolve().parents[3] / "scenarios" / "example-pagination"


@pytest.fixture(scope="module")
def distractors_dir(tmp_path_factory):
    out = tmp_path_factory.mktemp("preflight-distractors")
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
    paths = [writer.write(generate_manifest(config, size)) for size in (1, 2)]
    write_lockfile(paths, out / "manifests.lock")
    return out


def test_sweep_passes_on_committed_scenario(tmp_path, distractors_dir):
    result = oracle_equivalence_sweep(
        scenario_dir=SCENARIO_DIR,
        distractors_dir=distractors_dir,
        sizes=[1, 2],
        work_root=tmp_path,
    )
    assert result["pass"], json.dumps(result, indent=2)
    for cell in result["cells"]:
        assert cell["hidden_tree_absent"]
        assert cell["core_identical_to_1x"]
        assert cell["baseline_visible_pass"]
        assert not cell["baseline_hidden_pass"]
        assert cell["oracle_visible_pass"]
        assert cell["oracle_hidden_pass"]
        assert cell["runtime_fingerprint"]["python"]


def test_sweep_fails_without_lockfile_entry(tmp_path, distractors_dir):
    lock = distractors_dir / "manifests.lock"
    original = lock.read_text()
    lock.write_text("{}\n")
    try:
        result = oracle_equivalence_sweep(
            scenario_dir=SCENARIO_DIR,
            distractors_dir=distractors_dir,
            sizes=[1],
            work_root=tmp_path,
        )
    finally:
        lock.write_text(original)
    assert not result["pass"]
    assert result["cells"][0]["manifest_locked"] is False


def test_sweep_fails_when_baseline_hidden_passes(tmp_path, distractors_dir, monkeypatch):
    """A scenario whose hidden verifier passes pre-fix must fail the gate."""
    import harness.runner.preflight as preflight

    monkeypatch.setattr(
        preflight._Verifier, "hidden_pass", lambda self, workdir: True
    )
    result = oracle_equivalence_sweep(
        scenario_dir=SCENARIO_DIR,
        distractors_dir=distractors_dir,
        sizes=[1],
        work_root=tmp_path,
    )
    assert not result["pass"]
    assert result["cells"][0]["baseline_hidden_pass"] is True


def test_apply_oracle_edit_requires_unique_target(tmp_path):
    target = tmp_path / "src"
    target.mkdir()
    (target / "m.py").write_text("x = 1\nx = 1\n")
    with pytest.raises(RuntimeError, match="occurs 2x"):
        apply_oracle_edit(tmp_path, {"file": "src/m.py", "old": "x = 1", "new": "x = 2"})


def test_calibration_gate_passes(tmp_path):
    result = calibration_gate(tmp_path)
    assert result["pass"], json.dumps(result, indent=2)
    checks = result["checks"]
    assert checks["usage_extracted_responses_sse"] is True
    assert checks["usage_extracted_chat_json"] is True
    assert checks["edit_tool_call_detected"] is True


def test_cli_end_to_end(tmp_path, distractors_dir, capsys):
    config_path = tmp_path / "experiment.json"
    config_path.write_text(
        json.dumps(
            {
                "scenario_dir": str(SCENARIO_DIR),
                "distractors_dir": str(distractors_dir),
                "reports_dir": str(tmp_path / "reports"),
                "work_root": str(tmp_path / "work"),
                "arm": "mock",
                "sizes": [1, 2],
                "trials": 1,
            }
        )
    )
    out_path = tmp_path / "preflight.json"
    exit_code = main(["--config", str(config_path), "--json", str(out_path)])
    assert exit_code == 0
    result = json.loads(out_path.read_text())
    assert result["pass"]
    assert "PREFLIGHT PASS" in capsys.readouterr().out
