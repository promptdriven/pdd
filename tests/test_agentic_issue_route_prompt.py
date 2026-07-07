import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
PROMPT_PATH = REPO_ROOT / "pdd" / "prompts" / "agentic_issue_route_LLM.prompt"
ARCHITECTURE_PATH = REPO_ROOT / "architecture.json"


def _prompt_text() -> str:
    assert PROMPT_PATH.exists(), f"Prompt file not found: {PROMPT_PATH}"
    return PROMPT_PATH.read_text(encoding="utf-8")


def test_issue_route_prompt_defines_machine_readable_routes() -> None:
    prompt = _prompt_text()

    assert "ROUTE: bug_fix" in prompt
    assert "ROUTE: change_sync" in prompt
    assert "ROUTE: clarify" in prompt
    assert "ROUTE_RATIONALE:" in prompt
    assert "Use only these route values: `bug_fix`, `change_sync`, `clarify`" in prompt


def test_issue_route_prompt_runtime_signals_override_prompt_phrasing() -> None:
    prompt = _prompt_text()
    lowered = prompt.lower()

    assert "structural > behavioral > phrasing" in lowered
    assert "higher-priority runtime evidence overrides" in lowered
    assert "the prompt should be updated because the generated cli crashes" in lowered
    assert "because the crash is a behavioral runtime symptom" in lowered
    assert "route to `bug -> fix`" in lowered


def test_issue_route_prompt_runtime_evidence_examples_route_to_bug_fix() -> None:
    prompt = _prompt_text().lower()

    for signal in ("stack traces", "exception names", "failing tests", "wrong output", "regression"):
        assert signal in prompt

    assert "traceback, failing test, wrong runtime output, or regression" in prompt
    assert "route: bug_fix" in prompt


def test_issue_route_prompt_genuine_source_truth_change_routes_to_change_sync() -> None:
    prompt = _prompt_text().lower()

    assert "add a new requirement to the prompt/spec so future generated code supports x" in prompt
    assert "with no current failing behavior -> `route: change_sync`" in prompt
    assert "no current runtime failure to reproduce" in prompt
    assert "route to `change -> sync` only" in prompt


def test_issue_route_prompt_ambiguous_cases_ask_for_clarification() -> None:
    prompt = _prompt_text().lower()

    assert "ambiguous issues route to clarification" in prompt
    assert "the prompt should handle edge cases better" in prompt
    assert "route: clarify" in prompt
    assert "route_question:" in prompt
    assert "ask for the missing information instead of silently choosing" in prompt


def test_issue_route_prompt_preserves_later_bug_prompt_classification() -> None:
    prompt = _prompt_text()

    assert "BEFORE the later `pdd bug` Step 7" in prompt
    assert "Do not duplicate that later classification" in prompt
    assert "`pdd bug` can still fix the prompt source" in prompt


def test_architecture_tracks_issue_route_prompt_as_runtime_template() -> None:
    architecture = json.loads(ARCHITECTURE_PATH.read_text(encoding="utf-8"))
    matches = [
        entry
        for entry in architecture
        if entry.get("filename") == "agentic_issue_route_LLM.prompt"
    ]

    assert len(matches) == 1
    entry = matches[0]
    assert entry["filepath"] == "prompts/agentic_issue_route_LLM.prompt"
    assert entry["interface"]["type"] == "config"
    assert {"agentic", "config", "llm", "template"}.issubset(set(entry["tags"]))
