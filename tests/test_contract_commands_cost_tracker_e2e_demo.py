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


# ---------------------------------------------------------------------------
# Static fixture assertions (no demo run needed)
# ---------------------------------------------------------------------------

def test_baseline_prompt_matches_template_example() -> None:
    """Committed baseline prompt is a verbatim copy of template_example."""
    assert BASELINE_PROMPT.read_text(encoding="utf-8") == TEMPLATE_PROMPT.read_text(
        encoding="utf-8"
    )


def test_contracts_prompt_has_rules_and_vocabulary() -> None:
    text = CONTRACTS_PROMPT.read_text(encoding="utf-8")
    assert "<contract_rules>" in text
    assert "<vocabulary>" in text
    for rid in ("R1", "R2", "R3"):
        assert rid in text


def test_story_covers_contract_rules() -> None:
    text = STORY.read_text(encoding="utf-8")
    assert "## Covers" in text
    for rid in ("R1", "R2", "R3"):
        assert f"cost_tracker_with_contracts_python.prompt#{rid}" in text


# ---------------------------------------------------------------------------
# Deterministic demo run
# ---------------------------------------------------------------------------

def test_deterministic_demo_runs_contract_pipeline() -> None:
    """Deterministic pipeline (lint, check, compile, coverage) runs on both prompts."""
    proc = _run_demo()
    assert proc.returncode == 0, proc.stdout + proc.stderr

    comparison = json.loads((REPORTS / "comparison.json").read_text(encoding="utf-8"))
    assert comparison["mode"] == "deterministic"
    assert not comparison["validation_failures"], comparison["validation_failures"]

    rows = {row["label"]: row for row in comparison["rows"]}
    baseline = rows["baseline"]
    contracts = rows["contracts"]

    # Baseline has no contract rules (legacy-safe)
    assert not baseline["has_contract_rules"]
    assert baseline["compile_rules"] == 0

    # Contracts prompt has rules and compiles them (may have minor errors for imperfect rules)
    assert contracts["has_contract_rules"]
    assert contracts["compile_rules"] >= 3
    s = contracts["coverage_summary"]
    assert s.get("checked", 0) + s.get("story_only", 0) >= 1

    # Report files are written
    for name in ("baseline.json", "contracts.json", "comparison.json"):
        assert (REPORTS / name).is_file(), f"missing reports/{name}"


def test_deterministic_demo_baseline_has_no_contract_check_issues() -> None:
    """Baseline prompt exits 0 from contracts check (legacy-safe)."""
    proc = _run_demo()
    assert proc.returncode == 0, proc.stdout + proc.stderr
    baseline = json.loads((REPORTS / "baseline.json").read_text(encoding="utf-8"))
    # Legacy prompt: no contract rules → contracts check has nothing to flag
    assert baseline["check_issues"] == 0


def test_demo_cleanup_removes_reports() -> None:
    (REPORTS / "comparison.json").parent.mkdir(parents=True, exist_ok=True)
    (REPORTS / "comparison.json").write_text("{}", encoding="utf-8")
    proc = _run_demo("--cleanup")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert not (REPORTS / "comparison.json").exists()
