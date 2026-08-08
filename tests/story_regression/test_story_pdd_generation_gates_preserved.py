"""Generated story-backed regression tests.

This file is deterministic and safe to run without LLM/cloud credentials.
"""
from pathlib import Path

import pytest

PDD_STORY_ID = "pdd_generation_gates_preserved"
PDD_STORY_HASH = "168ff71807ad212f"
STORY_PATH = Path(__file__).resolve().parent / "../../user_stories/story__pdd_generation_gates_preserved.md"
CONTRACT_PATH = Path(__file__).resolve().parent / "../../user_stories/contracts/pdd_generation_gates_preserved.contract.md"


def _story_bundle() -> str:
    story = STORY_PATH.read_text(encoding="utf-8")
    if CONTRACT_PATH is not None and CONTRACT_PATH.exists():
        return story + "\n\n" + CONTRACT_PATH.read_text(encoding="utf-8")
    return story


def _bundle_hash() -> str:
    # Reuse the canonical primitive so the recorded PDD_STORY_HASH and
    # the gate's freshness check can never drift (pdd#1889). A
    # metadata-only prompt relink does not change this value.
    from pdd.story_test_generation import story_bundle_hash

    return story_bundle_hash(STORY_PATH)


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_generation_gates_preserved_oracle_contract():
    assert _bundle_hash() == PDD_STORY_HASH
    expected = [
    'These details matter for pass/fail:',
    'The distinction between "output is not code" and "code is missing a symbol" in error reporting.',
    'The presence of the specific symbol name and its expected signature in the regression error message.',
    'The failure to write to disk (file hash remains constant) upon any gate violation.',
    'The requirement for an explicit directive to bypass churn or interface gates.',
    'Specific typed exceptions (as defined in `gate_errors_python.prompt`) being raised for different failure modes.'
]
    bundle = _story_bundle()
    assert expected, "story has no Oracle or Acceptance Criteria clauses"
    for clause in expected:
        assert clause in bundle


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_generation_gates_preserved_negative_cases():
    assert _bundle_hash() == PDD_STORY_HASH
    expected = [
    'A safety check silently passes (no-op) when it should have blocked a change.',
    'A failing check results in a truncated or partially overwritten file.',
    'An override directive for one check (e.g., churn) accidentally suppresses a different check (e.g., interface shape).',
    'Multiple distinct failure types are collapsed into a single generic "Generation failed" error.'
]
    bundle = _story_bundle()
    for clause in expected:
        assert clause in bundle

