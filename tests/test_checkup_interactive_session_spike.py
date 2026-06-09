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
    prompt_path = REPO_ROOT / "pdd" / "prompts" / "checkup_interactive_session_python.prompt"

    assert not module_path.is_file(), (
        f"{module_path} is implementation surface; defer to #1435"
    )
    assert not bridge_path.is_file(), (
        f"{bridge_path} is implementation surface; defer to #1435"
    )
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
