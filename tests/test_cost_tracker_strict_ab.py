"""CI tests for cost_tracker strict A/B pipeline."""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
STRICT_AB = REPO_ROOT / "examples" / "cost_tracker_strict_ab"
PARENT = REPO_ROOT / "examples" / "contract_commands_cost_tracker_e2e_demo"
RUN_A = STRICT_AB / "scripts" / "run_experiment_a.py"

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
        [sys.executable, str(RUN_A), *extra],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        check=False,
        env={**os.environ, "PYTHONPATH": str(REPO_ROOT)},
    )


def test_experiment_a_runs_deterministic() -> None:
    proc = _run_demo()
    assert proc.returncode == 0, proc.stdout + proc.stderr

    report = json.loads(
        (STRICT_AB / "reports" / "experiment_a.json").read_text(encoding="utf-8")
    )
    assert report["experiment"] == "cost_tracker_spec_instrumentation"
    assert report["A1_contracts"]["rule_count"] >= 3
    assert report["A0_baseline"]["rule_count"] == 0
    assert report["drift"]["has_drift"] is True
    assert report["verdict"]["spec_instrumentation_improved"] is True

    for name in ("evidence_A0.json", "evidence_A1.json", "experiment_a_drift.json"):
        assert (STRICT_AB / "reports" / name).is_file(), f"missing reports/{name}"


def test_parent_prompts_exist() -> None:
    assert (PARENT / "prompts" / "cost_tracker_utility_Python.prompt").is_file()
    assert (PARENT / "prompts" / "cost_tracker_with_contracts_python.prompt").is_file()


def test_run_golden_pytest_stages_package_and_runs() -> None:
    """Golden harness must create edit_file_tool/ before copy2."""
    import importlib.util

    mod_path = STRICT_AB / "scripts" / "run_golden_pytest.py"
    spec = importlib.util.spec_from_file_location("run_golden_pytest", mod_path)
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    golden = PARENT / "tests" / "test_cost_tracker_reference.py"
    candidates = [
        STRICT_AB / "src" / "edit_file_tool" / "cost_tracker_utility_after.py",
        STRICT_AB / "src" / "edit_file_tool" / "cost_tracker_utility.py",
        PARENT / "src" / "edit_file_tool" / "cost_tracker_utility_after.py",
    ]
    src = next((p for p in candidates if p.is_file()), None)
    if src is None:
        pytest.skip("no src snapshot available for golden harness test")

    result = mod.run_golden(src.resolve(), golden.resolve(), python=sys.executable)
    assert result.get("error") is None
    assert result["exit_ok"] is True
    assert result["passed"] >= 3
    assert result["failed"] == 0


@pytest.mark.real
def test_experiment_b_live_ab_pipeline() -> None:
    if not RUN_REAL_LLM:
        pytest.skip("Set PDD_RUN_REAL_LLM_TESTS=1 for live A/B.")
    proc = subprocess.run(
        ["bash", str(STRICT_AB / "demo.sh"), "--live-ab", "--keep-artifacts"],
        cwd=str(STRICT_AB),
        capture_output=True,
        text=True,
        check=False,
        env={**os.environ, "PYTHONPATH": str(REPO_ROOT), "PDD_SKIP_UPDATE_CHECK": "1"},
    )
    try:
        if proc.returncode == 77:
            pytest.skip((proc.stdout + proc.stderr)[-2000:])
        assert proc.returncode == 0, proc.stdout + proc.stderr

        ab = json.loads((STRICT_AB / "reports" / "ab_live.json").read_text(encoding="utf-8"))
        assert ab["schema"] == "pdd.ab_report.v1"
        assert ab["experiment"] == "cost_tracker_clarify_sandwich"
        assert ab["clarify"]["ambiguity_count"] >= 1
        assert ab["lint"]["warn_after"] <= ab["lint"]["warn_before"]
        assert ab["before"]["generate_bytes"] > 0
        assert ab["after"]["generate_bytes"] > 0
        assert "spec_instrumented" in ab["verdict"]
        assert "golden_pytest" in ab["before"]
        assert ab["verdict"]["behavioral_claim_strength"] == "single_live_run"

        artifacts = STRICT_AB / "reports" / "artifacts"
        diffs = STRICT_AB / "reports" / "diffs"
        for rel in (
            "prompt_pre_clarify.prompt",
            "prompt_post_clarify.prompt",
            "src/cost_tracker_utility_before.py",
            "src/cost_tracker_utility_after.py",
            "tests/test_cost_tracker_work_before.py",
            "tests/test_cost_tracker_work_after.py",
        ):
            assert (artifacts / rel).is_file(), rel
        for rel in (
            "prompt_pre_vs_post.diff",
            "src_before_vs_after.diff",
            "tests_before_vs_after.diff",
        ):
            assert (diffs / rel).is_file(), rel
            assert (diffs / rel).read_text(encoding="utf-8").startswith("---")
    finally:
        subprocess.run(
            ["bash", str(STRICT_AB / "demo.sh"), "--cleanup"],
            cwd=str(STRICT_AB),
            check=False,
        )
