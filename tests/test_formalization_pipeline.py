"""Smoke tests for benchmark-local A0→A1 writeback pipeline."""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

BENCHMARK_ROOT = Path(__file__).resolve().parents[1] / "benchmarks" / "formalization"
PIPELINE_DIR = BENCHMARK_ROOT / "pipelines"
PIPELINE = PIPELINE_DIR / "formalize_a1.py"
REPO_ROOT = Path(__file__).resolve().parents[1]

sys.path.insert(0, str(PIPELINE_DIR))
import writeback  # noqa: E402


def test_append_vocabulary_creates_block(tmp_path: Path) -> None:
    prompt = tmp_path / "A0.prompt"
    prompt.write_text("When input is valid, return True.\n", encoding="utf-8")
    written = writeback.append_vocabulary_definitions(
        prompt,
        ["valid: returns True when format checks pass"],
    )
    assert written == 1
    assert "<vocabulary>" in prompt.read_text(encoding="utf-8")


def test_formalize_a1_dry_run(tmp_path: Path) -> None:
    a0 = tmp_path / "A0.prompt"
    a0.write_text("make a function that validates email addresses safely\n", encoding="utf-8")
    a1 = tmp_path / "A1.prompt"
    proc = subprocess.run(
        [sys.executable, str(PIPELINE), "--input", str(a0), "--output", str(a1),
         "--dry-run", "--json"],
        cwd=REPO_ROOT, capture_output=True, text=True, check=False,
    )
    assert proc.returncode == 0, proc.stderr
    assert json.loads(proc.stdout)["dry_run"] is True


def test_business_value_in_experiment_manifest(tmp_path: Path) -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(BENCHMARK_ROOT / "pipelines" / "run_experiment.py"),
            "--output-dir",
            str(tmp_path),
            "--tasks",
            "hello_fn",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr
    manifest = json.loads((tmp_path / "run_manifest.json").read_text(encoding="utf-8"))
    assert "business_value" in manifest
    assert "hypothesis" in manifest["business_value"]
    task = manifest["tasks"][0]
    assert task["a0"]["economics"]["generation_rounds"] is None
    assert task["delta"]["economics"]["delta_cost_usd"] is None


def test_run_experiment_smoke(tmp_path: Path) -> None:
    proc = subprocess.run(
        [sys.executable, str(BENCHMARK_ROOT / "pipelines" / "run_experiment.py"),
         "--output-dir", str(tmp_path), "--tasks", "hello_fn", "--json"],
        cwd=REPO_ROOT, capture_output=True, text=True, check=False,
    )
    assert proc.returncode == 0, proc.stderr
    summary = json.loads(proc.stdout)
    assert summary["task_count"] == 1
    assert summary["tasks"][0]["a1_has_contract_rules"] is True
    assert summary.get("primary_comparison") == "A0 (ad-hoc prompt) vs A1 (PDD formalized prompt)"
    assert summary.get("a0_vs_a1_summary", {}).get("tasks_compared") == 1
    task_result = json.loads((tmp_path / "hello_fn" / "result.json").read_text(encoding="utf-8"))
    a0_vs_a1 = task_result.get("a0_vs_a1") or {}
    assert a0_vs_a1.get("deterministic") is True
    assert a0_vs_a1.get("a1_improves_readiness") is True
    assert (
        a0_vs_a1.get("a1", {}).get("implementation_readiness_score", 0)
        > a0_vs_a1.get("a0", {}).get("implementation_readiness_score", 0)
    )
    manifest = json.loads((tmp_path / "run_manifest.json").read_text(encoding="utf-8"))
    assert manifest["story_template_issue"] == 820
    assert "seeded_from_a0" in manifest["tasks"][0]["story_template"]


def test_story_metrics_oracle_blocks() -> None:
    import story_metrics  # noqa: E402

    story = (
        BENCHMARK_ROOT
        / "corpus"
        / "tasks"
        / "email_validator"
        / "stories"
        / "story__email_validation.md"
    )
    stats = story_metrics.collect_story_file_stats(story)
    assert stats["has_oracle"] is True
    assert stats["has_non_oracle"] is True
    assert stats["oracle_bullets"] >= 1
    assert stats["non_oracle_bullets"] >= 1


def test_story_seed_from_prompt(tmp_path: Path) -> None:
    import story_metrics  # noqa: E402

    prompt = BENCHMARK_ROOT / "corpus" / "tasks" / "email_validator" / "A0.prompt"
    seeded = story_metrics.seed_story_from_prompt(
        prompt_path=prompt,
        output_dir=tmp_path / "stories",
        slug="email_validator",
    )
    assert seeded["success"] is True
    assert seeded["template_stats"]["has_oracle"] is True
    assert seeded["template_stats"]["has_non_oracle"] is True


def test_corpus_manifest_has_five_tasks() -> None:
    import yaml  # pylint: disable=import-outside-toplevel

    manifest = BENCHMARK_ROOT / "corpus" / "manifest.yaml"
    tasks = yaml.safe_load(manifest.read_text(encoding="utf-8"))["tasks"]
    assert len(tasks) == 5
    for task in tasks:
        assert (BENCHMARK_ROOT / "corpus" / task["a0"]).is_file()


def test_m2_harness_only_smoke(tmp_path: Path) -> None:
    m1 = tmp_path / "m1"
    a0 = BENCHMARK_ROOT / "corpus" / "tasks" / "email_validator" / "A0.prompt"
    (m1 / "email_validator").mkdir(parents=True)
    (m1 / "email_validator" / "A1.prompt").write_text(
        a0.read_text(encoding="utf-8"), encoding="utf-8"
    )
    proc = subprocess.run(
        [
            sys.executable,
            str(BENCHMARK_ROOT / "pipelines" / "run_generation_benchmark.py"),
            "--harness-only",
            "--skip-formalize",
            "--m1-dir",
            str(m1),
            "--output-dir",
            str(tmp_path / "m2"),
            "--tasks",
            "email_validator",
            "--json",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr
    manifest = json.loads(proc.stdout)
    task = manifest["tasks"][0]
    assert task["arms"]["A1"]["economics"]["oracle_test_pass_rate"] == 1.0
    eval_modes = task["arms"]["A1"]["evaluation_modes"]
    assert eval_modes["oracle"]["pass_rate"] == 1.0
    assert eval_modes["oracle"]["source"] == "tier_gold"
    assert eval_modes["non_oracle"]["source"] == "pdd_test_generated"
    assert "evaluation_summary" in task


def test_m2_replay_fixtures_smoke(tmp_path: Path) -> None:
    m1 = tmp_path / "m1"
    a0 = BENCHMARK_ROOT / "corpus" / "tasks" / "email_validator" / "A0.prompt"
    (m1 / "email_validator").mkdir(parents=True)
    (m1 / "email_validator" / "A1.prompt").write_text(
        a0.read_text(encoding="utf-8"), encoding="utf-8"
    )
    proc = subprocess.run(
        [
            sys.executable,
            str(BENCHMARK_ROOT / "pipelines" / "run_generation_benchmark.py"),
            "--replay-fixtures",
            "--skip-formalize",
            "--m1-dir",
            str(m1),
            "--output-dir",
            str(tmp_path / "m2"),
            "--tasks",
            "email_validator",
            "--json",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr
    manifest = json.loads(proc.stdout)
    assert manifest["replay_fixtures"] is True
    a0_econ = manifest["tasks"][0]["arms"]["A0"]["economics"]
    a1_econ = manifest["tasks"][0]["arms"]["A1"]["economics"]
    assert a0_econ.get("test_source") == "pdd_fixtures"
    assert a0_econ.get("code_source") == "pdd_fixtures"
    assert a1_econ.get("test_source") == "pdd_fixtures"
    notes = manifest["tasks"][0]["arms"]["A0"]["notes"]
    assert any("pdd_generated fixtures" in n for n in notes)


def test_m3_pipeline_replay_smoke(tmp_path: Path) -> None:
    m1 = tmp_path / "m1"
    a0 = BENCHMARK_ROOT / "corpus" / "tasks" / "email_validator" / "A0.prompt"
    (m1 / "email_validator").mkdir(parents=True)
    (m1 / "email_validator" / "A1.prompt").write_text(
        a0.read_text(encoding="utf-8"), encoding="utf-8"
    )
    proc = subprocess.run(
        [
            sys.executable,
            str(BENCHMARK_ROOT / "pipelines" / "run_m3_pipeline.py"),
            "--replay-fixtures",
            "--m1-dir",
            str(m1),
            "--m2-dir",
            str(tmp_path / "m2"),
            "--m3-dir",
            str(tmp_path / "m3"),
            "--tasks",
            "email_validator",
            "--json",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout
    payload = json.loads(proc.stdout)
    assert payload["live_m2"] is False
    assert payload["m3_dry_run"] is True
    assert (tmp_path / "m3" / "PIPELINE_RESULT.md").is_file()
    assert (tmp_path / "m3" / "summary.json").is_file()


def test_m3_dry_run_smoke(tmp_path: Path) -> None:
    m1 = tmp_path / "m1"
    m2 = tmp_path / "m2"
    a0 = BENCHMARK_ROOT / "corpus" / "tasks" / "email_validator" / "A0.prompt"
    (m1 / "email_validator").mkdir(parents=True)
    (m1 / "email_validator" / "A1.prompt").write_text(
        a0.read_text(encoding="utf-8"), encoding="utf-8"
    )
    subprocess.run(
        [
            sys.executable,
            str(BENCHMARK_ROOT / "pipelines" / "run_generation_benchmark.py"),
            "--harness-only",
            "--skip-formalize",
            "--m1-dir",
            str(m1),
            "--output-dir",
            str(m2),
            "--tasks",
            "email_validator",
        ],
        cwd=REPO_ROOT,
        check=True,
    )
    proc = subprocess.run(
        [
            sys.executable,
            str(BENCHMARK_ROOT / "pipelines" / "run_drift_benchmark.py"),
            "--dry-run",
            "--m2-dir",
            str(m2),
            "--m1-dir",
            str(m1),
            "--output-dir",
            str(tmp_path / "m3"),
            "--tasks",
            "email_validator",
            "--runs",
            "1",
            "--json",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout
    manifest = json.loads(proc.stdout)
    arm = manifest["tasks"][0]["arms"]["A1"]
    assert arm["drift"]["status"] == "stable"


def test_oracle_tests_pass_with_baseline() -> None:
    sys.path.insert(0, str(BENCHMARK_ROOT / "pipelines"))
    from pytest_metrics import run_pytest  # noqa: E402

    base = BENCHMARK_ROOT / "corpus" / "tier_gold" / "email_validator"
    metrics = run_pytest(
        list((base / "oracle_tests").glob("test_*.py")),
        pythonpath=[base / "baseline_src"],
        cwd=REPO_ROOT,
    )
    assert metrics["test_pass_rate"] == 1.0


def test_formalize_a1_deterministic_writeback(tmp_path: Path) -> None:
    a0 = tmp_path / "A0.prompt"
    a0.write_text(
        "<requirements>\nWhen email is valid, return True.\n"
        "When email is invalid, return False.\n</requirements>\n",
        encoding="utf-8",
    )
    a1 = tmp_path / "A1.prompt"
    proc = subprocess.run(
        [sys.executable, str(PIPELINE), "--input", str(a0), "--output", str(a1), "--json"],
        cwd=REPO_ROOT, capture_output=True, text=True, check=False,
    )
    assert proc.returncode == 0, proc.stderr
    manifest = json.loads(proc.stdout)
    assert manifest["summary"]["has_vocabulary"] is True
    assert manifest["summary"]["has_contract_rules"] is True
