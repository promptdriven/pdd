"""Regression tests for #1434 interactive session backend spike evidence.

These tests pin the Block 0 contract: Hybrid decision, Python-owned menus/
apply gating, and spike-only scope (no production session module in #1434).
They would fail on the pre-review branch that mixed pi_first artifacts with
Python-owned ownership tables and shipped pdd/checkup_interactive_session.py.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
SPIKE_DOC = REPO_ROOT / "docs" / "checkup_interactive_session_spike.md"
SAMPLE_JSON = REPO_ROOT / "docs" / "checkup_interactive_session_tty_sample.json"
PI_SAMPLE_JSONL = REPO_ROOT / "docs" / "checkup_interactive_session_pi_sample.jsonl"

PI_ALLOWED_TOOLS = frozenset({"read", "grep", "propose_repair_options"})
PI_DISABLED_DEFAULTS = frozenset({"write", "edit", "bash"})
PI_MIN_NODE = (22, 19, 0)

PYTHON_OWNED_CAPABILITIES = frozenset(
    {
        "numbered_menus",
        "choice_validation",
        "apply_gating",
        "session_persistence",
        "file_mutation",
    }
)


@pytest.fixture
def spike_doc_text() -> str:
    assert SPIKE_DOC.is_file(), f"Missing spike doc: {SPIKE_DOC}"
    return SPIKE_DOC.read_text(encoding="utf-8")


@pytest.fixture
def sample_artifact() -> dict:
    assert SAMPLE_JSON.is_file(), f"Missing sample artifact: {SAMPLE_JSON}"
    return json.loads(SAMPLE_JSON.read_text(encoding="utf-8"))


@pytest.fixture
def pi_sample_events() -> list[dict]:
    assert PI_SAMPLE_JSONL.is_file(), f"Missing Pi sample artifact: {PI_SAMPLE_JSONL}"
    events: list[dict] = []
    for line in PI_SAMPLE_JSONL.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line:
            events.append(json.loads(line))
    return events


def _parse_node_version(raw: str) -> tuple[int, int, int] | None:
    """Mirror spike-doc guard pseudocode for boundary regression tests."""
    raw = raw.strip().lstrip("v")
    parts = raw.split(".")
    if len(parts) < 3:
        return None
    try:
        return int(parts[0]), int(parts[1]), int(parts[2])
    except ValueError:
        return None


def _node_meets_pi_requirement(version: str) -> bool:
    parsed = _parse_node_version(version)
    return parsed is not None and parsed >= PI_MIN_NODE


def test_spike_doc_records_hybrid_decision(spike_doc_text: str) -> None:
    """#1434 must record Hybrid, not Pi-first, as the chosen backend."""
    decision_section = spike_doc_text.split("## Decision", 1)[1].split("##", 1)[0]
    assert re.search(r"\*\*Hybrid\*\*", decision_section), (
        "Spike doc Decision section must select Hybrid backend"
    )
    assert "Pi-first" not in decision_section.replace("Rejected: Pi-first", ""), (
        "Spike doc must not adopt Pi-first as the decision"
    )


def test_spike_doc_python_owns_menus_and_apply(spike_doc_text: str) -> None:
    """#1423 requires Python-owned numbered menus and --apply gating."""
    assert "Python owns deterministic menus" in spike_doc_text
    assert "`--apply` gating" in spike_doc_text
    assert "| Render numbered `[1]...[4]` repair menus | Python |" in spike_doc_text
    assert "| Enforce `--apply` before mutations | Python |" in spike_doc_text


def test_sample_artifact_decision_matches_hybrid(sample_artifact: dict) -> None:
    """Sample JSON must not declare pi_first while using python_tty backend."""
    assert sample_artifact["decision"] == "hybrid"
    assert sample_artifact["backend"] == "python_tty"
    assert sample_artifact["decision"] != "pi_first"


def test_sample_artifact_ownership_assigns_menus_to_python(sample_artifact: dict) -> None:
    """Ownership table must keep menus, validation, and apply in Python."""
    python_caps = set(sample_artifact["ownership"]["python"])
    assert PYTHON_OWNED_CAPABILITIES <= python_caps
    pi_caps = set(sample_artifact["ownership"]["pi"])
    assert "numbered_menus" not in pi_caps
    assert "apply_gating" not in pi_caps


def test_sample_artifact_recommends_hybrid_with_apply_gated(sample_artifact: dict) -> None:
    """Recommended proposal and menu selection must align with Hybrid + no apply."""
    recommended = [
        p for p in sample_artifact["proposals"] if p.get("recommended") is True
    ]
    assert len(recommended) == 1
    assert recommended[0]["proposal_id"] == "P-003"
    assert recommended[0]["label"] == "Hybrid"

    menu = sample_artifact["rendered_menu"]
    assert menu["selected_proposal_id"] == "P-003"
    assert menu["apply"] is False
    assert menu["apply_owner"] == "python"


def test_spike_scope_excludes_production_session_module() -> None:
    """#1434 is evidence-only; production session code belongs in #1435."""
    module_path = REPO_ROOT / "pdd" / "checkup_interactive_session.py"
    bridge_path = REPO_ROOT / "pdd" / "scripts" / "_pi_repair_bridge.mjs"
    # Guard both the canonical prompt source tree (`prompts/`, per .pddrc's
    # prompts_dir) and the package-copy path (`pdd/prompts/`) so a production
    # prompt added at either location trips this scope check.
    prompt_paths = [
        REPO_ROOT / "prompts" / "checkup_interactive_session_python.prompt",
        REPO_ROOT / "pdd" / "prompts" / "checkup_interactive_session_python.prompt",
    ]

    assert not module_path.is_file(), (
        f"{module_path} is implementation surface; defer to #1435"
    )
    assert not bridge_path.is_file(), (
        f"{bridge_path} is implementation surface; defer to #1435"
    )
    for prompt_path in prompt_paths:
        assert not prompt_path.is_file(), (
            f"{prompt_path} is implementation surface; defer to #1435"
        )


def test_spike_doc_and_sample_artifact_cross_reference(
    spike_doc_text: str, sample_artifact: dict
) -> None:
    """Spike doc must describe the checked-in artifact fields consistently."""
    assert "decision: \"hybrid\"" in spike_doc_text or "`decision: \"hybrid\"`" in spike_doc_text
    assert 'backend: "python_tty"' in spike_doc_text or '`backend: "python_tty"`' in spike_doc_text
    assert sample_artifact["schema"] == "pdd.checkup_interactive_session_sample.v1"
    assert len(sample_artifact["turns"]) == 3


def test_pi_sample_documents_restricted_tool_allowlist(pi_sample_events: list[dict]) -> None:
    """Pi spike task 1: createAgentSession ran with explicit allowlist, no write/edit/bash."""
    header = pi_sample_events[0]
    assert header["schema"] == "pdd.checkup_interactive_session_pi_sample.v1"
    assert header["decision"] == "hybrid"
    assert header["backend"] == "pi_agent_session"

    session_created = next(
        event for event in pi_sample_events if event.get("event") == "session_created"
    )
    assert frozenset(session_created["tools"]) == PI_ALLOWED_TOOLS
    assert frozenset(session_created["disabled_defaults"]) == PI_DISABLED_DEFAULTS
    assert session_created["write_edit_bash_enabled"] is False


def test_pi_sample_retains_context_and_defers_menus_to_python(
    pi_sample_events: list[dict],
) -> None:
    """Pi path retains QA context; menus and apply gating stay Python-owned."""
    user_turns = [
        event["content"]
        for event in pi_sample_events
        if event.get("event") == "turn" and event.get("role") == "user"
    ]
    assert user_turns == ["why?", "what check failed?", "tradeoff?"]

    retained = next(
        event for event in pi_sample_events if event.get("event") == "session_state_retained"
    )
    assert retained["finding_ids"] == ["F-001"]
    assert retained["turn_count"] == 3
    assert retained["menus_rendered_by"] == "python"
    assert retained["apply_gating_owner"] == "python"

    tool_call = next(
        event for event in pi_sample_events if event.get("event") == "tool_call"
    )
    assert tool_call["name"] == "propose_repair_options"
    assert tool_call["recommended_proposal_id"] == "P-003"


def test_spike_doc_references_pi_sample_artifact(spike_doc_text: str) -> None:
    """Pass-criteria tool control must cite checked-in Pi evidence."""
    assert "checkup_interactive_session_pi_sample.jsonl" in spike_doc_text
    assert "session_created" in spike_doc_text


@pytest.mark.parametrize(
    ("version", "expected"),
    [
        ("v22.18.0", False),
        ("v22.19.0", True),
        ("v23.0.0", True),
        ("v21.99.99", False),
    ],
)
def test_node_guard_uses_full_semver_not_major_only(version: str, expected: bool) -> None:
    """Packaging guard must reject Node <22.19.0 (spike doc boundary cases)."""
    assert _node_meets_pi_requirement(version) is expected


def test_spike_doc_node_guard_uses_full_semver(spike_doc_text: str) -> None:
    """Spike doc guard pseudocode must compare full semver, not major-only."""
    guard_section = spike_doc_text.split("Guard pattern", 1)[1].split("##", 1)[0]
    assert "PI_MIN_NODE = (22, 19, 0)" in guard_section
    assert "version >= PI_MIN_NODE" in guard_section
    assert "v22.18.0" in guard_section
    assert "v22.19.0" in guard_section
