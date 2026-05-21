"""CI tests for the verifier-template prompt-lint E2E demo.

The demo invokes only real ``pdd`` CLI commands. The only hand-authored prompt
is ``examples/prompt_lint_e2e_demo/prompts/find_verification_errors_LLM.prompt``
(plus the fixtures under ``fixtures/`` that serve as inputs to the verifier
when running ``--live``).
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
DEMO = REPO_ROOT / "examples" / "prompt_lint_e2e_demo"
RUN_E2E = DEMO / "lib" / "run_e2e.py"
INPUT_PROMPT = DEMO / "prompts" / "find_verification_errors_LLM.prompt"
WORK_PROMPT = DEMO / "prompts" / "find_verification_errors_work_LLM.prompt"
REPORTS = DEMO / "reports"
FIXTURES = DEMO / "fixtures"

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


def test_only_handwritten_files_are_input_prompt_and_fixtures() -> None:
    """The demo prompts dir holds exactly the input verifier template."""
    prompts = sorted(p.name for p in (DEMO / "prompts").iterdir() if p.is_file())
    assert prompts == ["find_verification_errors_LLM.prompt"], prompts
    for name in (
        "sample_program.py",
        "sample_code.py",
        "sample_output.txt",
        "subject_refund_python.prompt",
    ):
        assert (FIXTURES / name).is_file(), name


def test_demo_runs_only_real_pdd_cli_commands() -> None:
    """Deterministic E2E: every reports/*.json comes from a real CLI invocation."""
    proc = _run_demo()
    assert proc.returncode == 0, proc.stdout + proc.stderr

    lint = json.loads((REPORTS / "lint.json").read_text(encoding="utf-8"))
    lint_tmpl = json.loads((REPORTS / "lint_llm_template.json").read_text(encoding="utf-8"))
    contracts = json.loads((REPORTS / "contracts_check.json").read_text(encoding="utf-8"))
    compiled = json.loads((REPORTS / "contracts_compile.json").read_text(encoding="utf-8"))
    formalization = json.loads((REPORTS / "formalization.json").read_text(encoding="utf-8"))
    manifest = json.loads((REPORTS / "manifest.json").read_text(encoding="utf-8"))

    assert lint["warn_count"] > 0
    assert lint_tmpl["warn_count"] >= lint["warn_count"]
    assert contracts["issue_count"] > 0
    assert contracts["target_count"] >= 1
    assert compiled["error_count"] > 0
    assert formalization["file_count"] >= 1
    assert manifest["mode"] == "deterministic"
    assert "pdd prompt lint" in manifest["commands"]
    assert "pdd contracts check --json" in manifest["commands"]
    assert "pdd contracts compile --json" in manifest["commands"]


def test_demo_cleanup_removes_generated_work_copy() -> None:
    WORK_PROMPT.parent.mkdir(parents=True, exist_ok=True)
    WORK_PROMPT.write_text("% stale\n", encoding="utf-8")
    proc = _run_demo("--cleanup")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert not WORK_PROMPT.exists()
    assert not re.search(
        r"<vocabulary>", INPUT_PROMPT.read_text(encoding="utf-8"), re.I
    )


def test_input_prompt_is_lintable_input() -> None:
    """Sanity: the only handwritten prompt triggers deterministic lint."""
    from pdd.prompt_lint import scan_prompt

    result = scan_prompt(INPUT_PROMPT)
    assert result.warn_count > 0


@pytest.mark.real
def test_demo_live_runs_full_pdd_pipeline() -> None:
    """End-to-end with real LLM: clarify + real verifier smoke run."""
    if not RUN_REAL_LLM:
        pytest.skip(
            "Real LLM tests require API access; "
            "set PDD_RUN_REAL_LLM_TESTS=1 or PDD_RUN_ALL_TESTS=1."
        )
    proc = _run_demo("--live", "--keep-artifacts")
    try:
        if proc.returncode == 77:
            pytest.skip(
                "LLM unavailable (preflight or every provider failed); "
                "check Gemini quota and PDD_MODEL_DEFAULT.\n"
                + (proc.stdout + proc.stderr)[-2000:]
            )
        assert proc.returncode == 0, proc.stdout + proc.stderr

        live = json.loads((REPORTS / "live.json").read_text(encoding="utf-8"))
        assert live["mode"] == "live"
        assert live["clarify"]["ambiguity_count"] >= 1
        assert live["has_vocabulary_after"] is True
        assert live["after_lint"]["warn_count"] <= live["before_lint"]["warn_count"]
        assert live["before_smoke"]["issues_count"] >= 0
        assert live["after_smoke"]["issues_count"] >= 0

        assert WORK_PROMPT.is_file()
        work_text = WORK_PROMPT.read_text(encoding="utf-8")
        assert re.search(r"<vocabulary>", work_text, re.I)
    finally:
        _run_demo("--cleanup")
