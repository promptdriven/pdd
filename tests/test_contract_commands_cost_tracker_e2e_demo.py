"""CI tests for contract-commands E2E demo (cost_tracker prompt)."""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
DEMO = REPO_ROOT / "examples" / "contract_commands_cost_tracker_e2e_demo"
RUN_E2E = DEMO / "lib" / "run_e2e.py"

BASELINE_PROMPT = DEMO / "prompts" / "cost_tracker_utility_Python.prompt"
CONTRACTS_PROMPT = DEMO / "prompts" / "cost_tracker_with_contracts_python.prompt"
TEMPLATE_PROMPT = (
    REPO_ROOT
    / "examples"
    / "template_example"
    / "prompts"
    / "cost_tracker_utility_Python.prompt"
)
STORY = DEMO / "user_stories" / "story__cost_tracker.md"
REPORTS = DEMO / "reports"

RUN_REAL_LLM = (
    os.getenv("PDD_RUN_REAL_LLM_TESTS") == "1"
    or os.getenv("PDD_RUN_ALL_TESTS") == "1"
)


@pytest.fixture(autouse=True)
def _pdd_env(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("PDD_PATH", str(REPO_ROOT / "pdd"))
    monkeypatch.setenv("PDD_SKIP_UPDATE_CHECK", "1")


def _run_demo(*extra: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(RUN_E2E), *extra],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        check=False,
        env={**os.environ, "PYTHONPATH": str(REPO_ROOT)},
    )


def test_baseline_prompt_matches_template_example() -> None:
    """Committed prompt is a verbatim copy of template_example."""
    assert BASELINE_PROMPT.read_text(encoding="utf-8") == TEMPLATE_PROMPT.read_text(
        encoding="utf-8"
    )


def test_contracts_prompt_has_rules_and_vocabulary() -> None:
    text = CONTRACTS_PROMPT.read_text(encoding="utf-8")
    assert "<contract_rules>" in text
    assert "<vocabulary>" in text
    assert "R1:" in text and "R3:" in text


def test_story_covers_contract_rules() -> None:
    text = STORY.read_text(encoding="utf-8")
    assert "## Oracle" in text
    assert "## Negative Cases" in text
    for rid in ("R1", "R2", "R3"):
        assert f"cost_tracker_with_contracts_python.prompt#{rid}" in text


def test_deterministic_demo_runs_new_commands() -> None:
    """Gate, evidence, drift, and deterministic author all succeed."""
    proc = _run_demo()
    assert proc.returncode == 0, proc.stdout + proc.stderr

    comparison = json.loads((REPORTS / "comparison.json").read_text(encoding="utf-8"))
    assert comparison["mode"] == "deterministic"
    assert comparison["evidence_baseline_schema"] == "pdd.evidence.manifest.v1"
    assert comparison["validate_baseline"]["valid"] is True
    assert comparison["drift_baseline_vs_contracts"]["has_drift"] is True
    assert comparison["author_deterministic"]["work_exists"] is True

    step_names = [s["name"] for s in comparison["author_deterministic"]["steps"]]
    assert "contracts_check" in step_names
    assert "contracts_compile" in step_names
    assert "coverage_contracts" in step_names
    assert "evidence_emit" in step_names

    for name in (
        "gate_baseline.json",
        "gate_contracts.json",
        "evidence_baseline.json",
        "evidence_contracts.json",
        "evidence_work.json",
        "drift.json",
    ):
        assert (REPORTS / name).is_file(), f"missing reports/{name}"

    drift = json.loads((REPORTS / "drift.json").read_text(encoding="utf-8"))
    assert drift["has_drift"] is True
    assert len(drift["findings"]) >= 1

    gate = json.loads((REPORTS / "gate_contracts.json").read_text(encoding="utf-8"))
    stage_names = [s["name"] for s in gate["stages"]]
    assert stage_names == [
        "prompt_lint",
        "contracts_check",
        "contracts_compile",
        "coverage_contracts",
    ]


def test_demo_cleanup_removes_work_copy() -> None:
    work = DEMO / "prompts" / "cost_tracker_work_python.prompt"
    work.write_text("% stale\n", encoding="utf-8")
    proc = _run_demo("--cleanup")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert not work.exists()


@pytest.mark.real
def test_demo_live_contracts_author() -> None:
    if not RUN_REAL_LLM:
        pytest.skip("Set PDD_RUN_REAL_LLM_TESTS=1 for live author.")
    proc = _run_demo("--live", "--keep-artifacts")
    try:
        if proc.returncode == 77:
            pytest.skip("LLM unavailable.\n" + (proc.stdout + proc.stderr)[-2000:])
        assert proc.returncode in (0, 1), proc.stdout + proc.stderr
        live = json.loads((REPORTS / "live.json").read_text(encoding="utf-8"))
        assert live["mode"] == "live"
        assert (DEMO / "prompts" / "cost_tracker_work_python.prompt").is_file()
        assert (REPORTS / "evidence_live.json").is_file()
    finally:
        _run_demo("--cleanup")
