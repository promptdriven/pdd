"""CI tests for the prompt-lint + contracts E2E demo.

The demo is a paired vague + formalized fixture in the same domain:

  * ``prompts/foo_vague_python.prompt``      — intentionally vague
  * ``prompts/foo_formalized_python.prompt`` — source-of-truth grade

Plus two companion stories under ``user_stories/``. Every other artifact in
``reports/``, ``src/``, ``tests/`` is produced by real ``pdd`` CLI commands
driven from ``lib/run_e2e.py``.
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
DEMO = REPO_ROOT / "examples" / "prompt_lint_contract_e2e_demo"
RUN_E2E = DEMO / "lib" / "run_e2e.py"

VAGUE_PROMPT = DEMO / "prompts" / "foo_vague_python.prompt"
FORMALIZED_PROMPT = DEMO / "prompts" / "foo_formalized_python.prompt"
VAGUE_STORY = DEMO / "user_stories" / "story__foo_vague.md"
FORMALIZED_STORY = DEMO / "user_stories" / "story__foo_formalized.md"

WORK_PROMPT = DEMO / "prompts" / "foo_work_python.prompt"
SRC_FILE = DEMO / "src" / "foo_work.py"
TEST_FILE = DEMO / "tests" / "test_foo_work.py"
REPORTS = DEMO / "reports"

HAND_AUTHORED_PROMPTS = sorted([VAGUE_PROMPT.name, FORMALIZED_PROMPT.name])
HAND_AUTHORED_STORIES = sorted([VAGUE_STORY.name, FORMALIZED_STORY.name])

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


def _is_real_file(p: Path) -> bool:
    return p.is_file() and "__pycache__" not in p.parts


# ---------------------------------------------------------------------------
# Hand-authored fixture inventory
# ---------------------------------------------------------------------------


def test_paired_fixtures_are_the_only_handwritten_inputs() -> None:
    """Exactly two prompts + two stories are committed; nothing under src/ or tests/."""
    prompts = sorted(p.name for p in (DEMO / "prompts").iterdir() if p.is_file())
    assert prompts == HAND_AUTHORED_PROMPTS, prompts

    stories = sorted(p.name for p in (DEMO / "user_stories").iterdir() if p.is_file())
    assert stories == HAND_AUTHORED_STORIES, stories

    for sub in ("src", "tests"):
        d = DEMO / sub
        if d.exists():
            files = [p for p in d.rglob("*") if _is_real_file(p)]
            assert not files, f"unexpected committed files in {sub}/: {files}"


def test_formalized_prompt_declares_vocabulary_and_formalization() -> None:
    """The positive fixture must contain <vocabulary> and <formalization>."""
    text = FORMALIZED_PROMPT.read_text(encoding="utf-8")
    assert re.search(r"<vocabulary>", text)
    assert re.search(r"<formalization>", text)
    assert "target: smt" in text


def test_formalized_story_has_glossary_and_covers_all_rules() -> None:
    """The positive story must declare a ## Glossary and cover R1..R4."""
    text = FORMALIZED_STORY.read_text(encoding="utf-8")
    assert "## Glossary" in text
    for rid in ("R1", "R2", "R3", "R4"):
        assert f"foo_formalized_python.prompt#{rid}" in text


# ---------------------------------------------------------------------------
# Deterministic E2E — the heart of the demo
# ---------------------------------------------------------------------------


def test_deterministic_demo_compares_vague_vs_formalized() -> None:
    """Run the deterministic demo and assert the side-by-side comparison."""
    proc = _run_demo()
    assert proc.returncode == 0, proc.stdout + proc.stderr

    comparison = json.loads((REPORTS / "comparison.json").read_text(encoding="utf-8"))
    assert comparison["mode"] == "deterministic"
    rows = {row["label"]: row for row in comparison["rows"]}
    vague = rows["vague"]
    formalized = rows["formalized"]

    # Vague fixture must trip the linter loudly.
    assert vague["lint_warn_count"] >= 10
    assert vague["lint_by_code"].get("VAGUE_TERM_UNDEFINED", 0) >= 5
    assert vague["lint_by_code"].get("VAGUE_NO_OBSERVABLE_OUTCOME", 0) >= 1
    assert vague["compile_errors"] >= 1
    assert vague["compile_obligations"] <= 2
    assert vague["coverage_summary"]["unchecked"] >= 1

    # Formalized fixture must clear the structural checks.
    assert formalized["compile_errors"] == 0
    assert formalized["compile_rules"] >= 4
    assert formalized["compile_obligations"] >= 6
    assert formalized["coverage_summary"]["unchecked"] == 0
    assert formalized["coverage_summary"]["story_only"] + \
        formalized["coverage_summary"]["checked"] >= 4
    assert "VAGUE_TERM_UNDEFINED" not in formalized["lint_by_code"]
    assert "VAGUE_NO_OBSERVABLE_OUTCOME" not in formalized["lint_by_code"]
    assert formalized["lint_warn_count"] <= 5

    # The contrast itself.
    assert formalized["lint_warn_count"] < vague["lint_warn_count"]
    assert formalized["compile_errors"] < vague["compile_errors"]
    assert formalized["compile_obligations"] > vague["compile_obligations"]


def test_deterministic_demo_writes_per_fixture_reports() -> None:
    proc = _run_demo()
    assert proc.returncode == 0, proc.stdout + proc.stderr
    for name in ("vague.json", "formalized.json", "comparison.json"):
        assert (REPORTS / name).is_file(), f"missing reports/{name}"

    vague = json.loads((REPORTS / "vague.json").read_text(encoding="utf-8"))
    formalized = json.loads((REPORTS / "formalized.json").read_text(encoding="utf-8"))
    assert vague["prompt"].endswith("foo_vague_python.prompt")
    assert formalized["prompt"].endswith("foo_formalized_python.prompt")


def test_deterministic_demo_persists_before_after_artifacts_and_diff() -> None:
    """The demo always keeps stable copies of the before/after pair + their diff."""
    proc = _run_demo()
    assert proc.returncode == 0, proc.stdout + proc.stderr

    before = REPORTS / "artifacts" / "prompt_before.prompt"
    after = REPORTS / "artifacts" / "prompt_after.prompt"
    diff = REPORTS / "diffs" / "prompt_before_vs_after.diff"

    assert before.is_file(), "missing reports/artifacts/prompt_before.prompt"
    assert after.is_file(), "missing reports/artifacts/prompt_after.prompt"
    assert diff.is_file(), "missing reports/diffs/prompt_before_vs_after.diff"

    # The persisted copies must exactly match the hand-authored inputs.
    assert before.read_text(encoding="utf-8") == VAGUE_PROMPT.read_text(encoding="utf-8")
    assert after.read_text(encoding="utf-8") == FORMALIZED_PROMPT.read_text(encoding="utf-8")

    diff_text = diff.read_text(encoding="utf-8")
    assert diff_text.startswith("---"), "unified diff should start with a --- header"
    assert "+++ prompts/foo_formalized_python.prompt" in diff_text
    assert re.search(r"^@@ ", diff_text, re.MULTILINE), "diff must contain at least one hunk"
    # The migration must add a <vocabulary> block and remove no observable verbs.
    assert any(
        line.startswith("+") and "<vocabulary>" in line
        for line in diff_text.splitlines()
    ), "diff should show <vocabulary> being added"
    assert any(
        line.startswith("+") and "<formalization>" in line
        for line in diff_text.splitlines()
    ), "diff should show <formalization> being added"


def test_vague_and_formalized_are_lintable_inputs() -> None:
    """Sanity: vague trips warnings; formalized stays under the warning floor."""
    from pdd.prompt_lint import scan_prompt

    vague = scan_prompt(VAGUE_PROMPT)
    formalized = scan_prompt(FORMALIZED_PROMPT)
    assert vague.warn_count >= 10
    assert formalized.warn_count <= 5


# ---------------------------------------------------------------------------
# Cleanup
# ---------------------------------------------------------------------------


def test_demo_cleanup_removes_generated_artifacts() -> None:
    WORK_PROMPT.parent.mkdir(parents=True, exist_ok=True)
    WORK_PROMPT.write_text("% stale\n", encoding="utf-8")
    SRC_FILE.parent.mkdir(parents=True, exist_ok=True)
    SRC_FILE.write_text("# stale\n", encoding="utf-8")
    TEST_FILE.parent.mkdir(parents=True, exist_ok=True)
    TEST_FILE.write_text("# stale\n", encoding="utf-8")

    proc = _run_demo("--cleanup")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert not WORK_PROMPT.exists()
    assert not SRC_FILE.exists()
    assert not TEST_FILE.exists()


# ---------------------------------------------------------------------------
# Live (real LLM) — clarifies the vague fixture toward the formalized shape
# ---------------------------------------------------------------------------


@pytest.mark.real
def test_demo_live_runs_full_pdd_pipeline() -> None:
    """End-to-end with real LLM: clarify (vague) → generate → test → pytest."""
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
        assert live["after_lint"]["warn_count"] <= live["before_lint"]["warn_count"]
        assert live["contracts_compile"]["error_count"] <= 6
        assert live["generate"]["byte_size"] > 0
        assert live["test"]["byte_size"] > 0
        assert live["pytest"]["passed"] is True

        assert SRC_FILE.is_file()
        assert TEST_FILE.is_file()
        assert len(SRC_FILE.read_text(encoding="utf-8")) > 100
        assert re.search(r"def\s+test_", TEST_FILE.read_text(encoding="utf-8"))

        # Live mode must persist the clarified prompt + generated code/test
        # alongside the deterministic before/after pair, plus three diffs.
        artifacts = REPORTS / "artifacts"
        diffs = REPORTS / "diffs"
        for rel in (
            "prompt_before.prompt",
            "prompt_after.prompt",
            "prompt_clarified.prompt",
            "src/foo_work.py",
            "tests/test_foo_work.py",
        ):
            assert (artifacts / rel).is_file(), f"missing reports/artifacts/{rel}"
        for rel in (
            "prompt_before_vs_after.diff",
            "prompt_before_vs_clarified.diff",
            "prompt_clarified_vs_after.diff",
        ):
            assert (diffs / rel).is_file(), f"missing reports/diffs/{rel}"
        assert live["diffs"]["before_vs_clarified"]["hunk_count"] >= 1
        assert live["diffs"]["clarified_vs_after"]["hunk_count"] >= 1
    finally:
        _run_demo("--cleanup")
