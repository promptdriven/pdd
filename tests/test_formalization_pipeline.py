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


def test_corpus_manifest_has_five_tasks() -> None:
    import yaml  # pylint: disable=import-outside-toplevel

    manifest = BENCHMARK_ROOT / "corpus" / "manifest.yaml"
    tasks = yaml.safe_load(manifest.read_text(encoding="utf-8"))["tasks"]
    assert len(tasks) == 5
    for task in tasks:
        assert (BENCHMARK_ROOT / "corpus" / task["a0"]).is_file()


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
