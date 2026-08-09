# End-to-end test for the PR #1501 change-story workflow (issue #1454).
#
# Exercises the whole chain against a REAL LLM, nothing stubbed:
#   1. generate_user_story  -> human story + machine-checkable contract
#   2. _compose_story_oracle -> story + contract combined oracle
#   3. run_user_story_tests  -> validate the linked story/prompt subset
#   4. run_user_story_fix    -> contract-aware detect/repair path
#   5. _generate_user_story_artifacts_for_change -> off|warn|strict policy gate,
#      including live reuse of the story created in step 1.
#
# Real API calls cost money, so this is marked `e2e` and skipped unless a usable
# provider key is present. `PDD_FORCE_LOCAL=1` keeps llm_invoke off the cloud
# auth path (which otherwise blocks on interactive GitHub device-flow login).
#
# Run with:  pytest -m e2e tests/test_e2e_story_workflow_1501.py -v
# Skip with: pytest -m "not e2e" ...

import csv
import os
from pathlib import Path
from types import SimpleNamespace

import pytest

import pdd

from pdd.user_story_tests import (
    generate_user_story,
    run_user_story_tests,
    run_user_story_fix,
    _compose_story_oracle,
    _contract_path_for_story,
)
from pdd.agentic_change_orchestrator import _generate_user_story_artifacts_for_change

pytestmark = [pytest.mark.e2e, pytest.mark.timeout(900)]

# Strength tier: low strength can route to the cloud/interactive model tier first
# in some environments; 0.5 selects a keyed local chat model directly.
_STRENGTH = float(os.environ.get("PDD_DEMO_STRENGTH", "0.5"))

_ISSUE = """# Issue: Upload a CSV and view a summary report

## Summary
Users upload a CSV file and the tool returns a summary report of the contents.

## Acceptance Criteria
- Given a valid CSV, when uploaded, then a summary report (row count + columns) is shown.
- Given a malformed CSV, when uploaded, then a clear validation error is returned.
"""

_PROMPT = """% Module: upload
Implement upload(csv_path: str) -> dict that reads a CSV file and returns a
summary report with the row count and column names. Raise ValueError on a
malformed CSV.
"""

_CODE = '''"""Upload a CSV and return a summary report."""
import csv


def upload(csv_path: str) -> dict:
    with open(csv_path, newline="") as fh:
        rows = list(csv.reader(fh))
    if not rows:
        raise ValueError("malformed CSV: empty file")
    header, *body = rows
    return {"row_count": len(body), "columns": header}
'''


def _pick_keyed_model() -> str | None:
    """Return a cheap, non-interactive model whose required key(s) are all set.

    Pinning ``PDD_MODEL_DEFAULT`` to this avoids llm_invoke's automatic cascade,
    which under pytest stdin-capture would otherwise try to *prompt* for every
    missing provider key and fail. Provider-agnostic: it reads the packaged
    ``llm_model.csv`` and matches the ``api_key`` env vars actually present, so
    the test runs against whatever credentials CI/the developer has (Gemini,
    OpenAI, Anthropic, Vertex, ...).
    """
    csv_path = Path(pdd.__file__).resolve().parent / "data" / "llm_model.csv"
    if not csv_path.exists():
        return None
    prefer = ("flash", "mini", "haiku", "lite", "small", "2.5")
    fallback = None
    with open(csv_path, newline="", encoding="utf-8") as fh:
        for row in csv.DictReader(fh):
            if str(row.get("interactive_only", "")).strip().lower() == "true":
                continue
            envs = [e.strip() for e in (row.get("api_key") or "").split("|") if e.strip()]
            if not envs or not all(os.environ.get(e) for e in envs):
                continue
            model = (row.get("model") or "").strip()
            if not model:
                continue
            if any(p in model.lower() for p in prefer):
                return model
            fallback = fallback or model
    return fallback


_KEYED_MODEL = _pick_keyed_model()

# conftest's autouse `_isolate_provider_env` clears provider keys before every
# test so unit tests can't make accidental real calls. Snapshot them at import
# (before any fixture runs) and re-inject in the test body — the documented
# opt-back-in path for credential-dependent tests.
_PROVIDER_ENV_SNAPSHOT = {
    k: v
    for k, v in os.environ.items()
    if k.endswith("_API_KEY")
    or k in ("VERTEXAI_PROJECT", "VERTEXAI_LOCATION", "GOOGLE_APPLICATION_CREDENTIALS")
}


def _build_workspace(tmp_path: Path) -> dict:
    prompts = tmp_path / "prompts"; prompts.mkdir()
    src = tmp_path / "src"; src.mkdir()
    stories = tmp_path / "user_stories"; stories.mkdir()
    prompt_file = prompts / "upload_python.prompt"
    prompt_file.write_text(_PROMPT, encoding="utf-8")
    (src / "upload.py").write_text(_CODE, encoding="utf-8")
    issue_file = tmp_path / "issue_1454.md"
    issue_file.write_text(_ISSUE, encoding="utf-8")
    return {
        "prompts": prompts, "src": src, "stories": stories,
        "prompt_file": prompt_file, "issue_file": issue_file,
    }


@pytest.mark.skipif(_KEYED_MODEL is None, reason="no keyed LLM model available - skipping e2e")
def test_e2e_change_story_workflow_end_to_end(tmp_path, monkeypatch):
    # Keep llm_invoke on the local (keyed) path; the cloud path blocks on
    # interactive GitHub device-flow auth in headless runs. Pin a model we hold a
    # key for so selection never cascades into stdin key prompts.
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", _KEYED_MODEL)
    monkeypatch.delenv("PDD_ALLOW_INTERACTIVE", raising=False)
    # Re-inject the provider keys the autouse isolation fixture cleared.
    for key, value in _PROVIDER_ENV_SNAPSHOT.items():
        monkeypatch.setenv(key, value)

    ws = _build_workspace(tmp_path)
    prompts, stories = ws["prompts"], ws["stories"]
    prompt_file, issue_file = ws["prompt_file"], ws["issue_file"]

    # --- 1) Author the human story + machine-checkable contract (real LLM) ----
    ok, msg, cost, model, story_path, linked = generate_user_story(
        prompt_files=[str(prompt_file)],
        issue=str(issue_file),
        stories_dir=str(stories),
        prompts_dir=str(prompts),
        strength=_STRENGTH,
    )
    assert ok, f"story generation failed: {msg}"
    assert cost > 0 and model, "expected a real (billed) LLM call"
    story_path = Path(story_path)
    assert story_path.exists()
    assert "upload_python.prompt" in [Path(p).name for p in linked]
    contract_path = _contract_path_for_story(story_path)
    assert contract_path.exists(), "two-file model must write a sibling contract"

    # --- 2) The combined oracle carries BOTH the story and the contract -------
    oracle = _compose_story_oracle(story_path, story_path.read_text(encoding="utf-8"))
    assert "## Story" in oracle  # human story prose
    assert "## Acceptance Criteria" in oracle  # contract-only section
    assert oracle != story_path.read_text(encoding="utf-8")  # contract was appended

    # --- 3) Validate ONLY the linked story/prompt subset (real detect oracle) --
    passed, results, vcost, vmodel = run_user_story_tests(
        prompts_dir=str(prompts),
        story_files=[story_path],
        prompt_files=[prompt_file],
        strength=_STRENGTH,
        quiet=True,
    )
    assert isinstance(passed, bool)
    assert vcost > 0
    assert len(results) == 1
    assert Path(str(results[0]["story"])).name == story_path.name

    # --- 4) Contract-aware repair path runs end to end (real LLM) -------------
    ctx = SimpleNamespace(obj={})
    fok, fmsg, fcost, fmodel, changed = run_user_story_fix(
        ctx=ctx, story_file=str(story_path), prompts_dir=str(prompts),
        strength=_STRENGTH, quiet=True,
    )
    assert isinstance(fok, bool)
    assert fcost > 0, "fix must run detect_change against the combined oracle"
    # The fix path must restore the caller's skip flag regardless of outcome.
    assert ctx.obj.get("skip_user_stories") is None

    # --- 5) Orchestrator policy gate: off | warn | strict (real generate/validate)
    # off: no creation, no checking.
    monkeypatch.setenv("PDD_STORY_POLICY", "off")
    files, summary, c, m, block = _generate_user_story_artifacts_for_change(
        issue_url=str(issue_file), changed_files=["prompts/upload_python.prompt"],
        worktree_path=tmp_path, strength=_STRENGTH, temperature=0.0,
        time_budget=0.3, verbose=False, quiet=True,
    )
    assert files == [] and block is None and "off" in summary

    # warn: reuses the story authored in step 1, validates, reports, never blocks.
    monkeypatch.setenv("PDD_STORY_POLICY", "warn")
    files, summary, c, m, block = _generate_user_story_artifacts_for_change(
        issue_url=str(issue_file), changed_files=["prompts/upload_python.prompt"],
        worktree_path=tmp_path, strength=_STRENGTH, temperature=0.0,
        time_budget=0.3, verbose=False, quiet=True,
    )
    assert block is None, "warn must never block"
    assert "Policy: `warn`" in summary
    assert "reused existing linked story" in summary  # live reuse, not regenerated
    assert "Validation:" in summary

    # strict: same reuse + validation; blocks iff a linked story fails.
    monkeypatch.setenv("PDD_STORY_POLICY", "strict")
    files, summary, c, m, block = _generate_user_story_artifacts_for_change(
        issue_url=str(issue_file), changed_files=["prompts/upload_python.prompt"],
        worktree_path=tmp_path, strength=_STRENGTH, temperature=0.0,
        time_budget=0.3, verbose=False, quiet=True,
    )
    assert "Policy: `strict`" in summary
    assert "reused existing linked story" in summary
    # Block decision must be consistent with the reported validation result.
    failed = "❌" in summary
    if failed:
        assert block is not None and "Blocking (strict policy)" in summary
    else:
        assert block is None
