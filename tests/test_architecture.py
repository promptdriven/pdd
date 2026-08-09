"""Structural invariants for the repository architecture manifest.

These tests guard against duplicate/conflicting node definitions in
``architecture.json``. Two independent sub-PRs (#1699 and #1769) each appended
an entry for ``user_story_tests_python.prompt`` and
``coverage_contracts_python.prompt`` with contradictory ``dependencies`` and
``priority`` values. ``pdd checkup --validate-arch-includes`` aggregates
duplicate entries and is blind to the conflict, but dependency ordering becomes
consumer-dependent when the same filename maps to two different dependency sets.
Each dev-unit filename MUST appear exactly once as a top-level node.
"""
from __future__ import annotations

import collections
import json
from pathlib import Path

ARCHITECTURE_JSON = Path(__file__).parents[1] / "architecture.json"


def _load_nodes() -> list[dict]:
    return json.loads(ARCHITECTURE_JSON.read_text(encoding="utf-8"))


def test_architecture_json_has_no_duplicate_filenames():
    """Every node's ``filename`` is a unique top-level key."""
    nodes = _load_nodes()
    counts = collections.Counter(node.get("filename") for node in nodes)
    duplicates = {name: n for name, n in counts.items() if name and n > 1}
    assert not duplicates, f"duplicate architecture nodes: {duplicates}"


def test_story_prompt_filenames_appear_exactly_once():
    """The two prompts merged for pdd#1889 D-F1 each appear once."""
    nodes = _load_nodes()
    counts = collections.Counter(node.get("filename") for node in nodes)
    assert counts["user_story_tests_python.prompt"] == 1
    assert counts["coverage_contracts_python.prompt"] == 1


def test_merged_nodes_dependencies_match_prompt_declarations():
    """Merged nodes carry the union of dependencies declared by the prompt.

    ``coverage_contracts_python.prompt`` declares three ``<pdd-dependency>``
    tags (contract_ir, user_story_tests, story_regression); the pre-merge
    duplicates each listed only a partial set. ``user_story_tests_python.prompt``
    declares four (contract_ir, detect_change, change_main, llm_invoke).
    """
    nodes = {node.get("filename"): node for node in _load_nodes()}

    coverage_deps = set(nodes["coverage_contracts_python.prompt"]["dependencies"])
    assert coverage_deps == {
        "contract_ir_python.prompt",
        "user_story_tests_python.prompt",
        "story_regression_python.prompt",
    }

    story_deps = set(nodes["user_story_tests_python.prompt"]["dependencies"])
    assert story_deps == {
        "contract_ir_python.prompt",
        "detect_change_python.prompt",
        "change_main_python.prompt",
        "llm_invoke_python.prompt",
    }
