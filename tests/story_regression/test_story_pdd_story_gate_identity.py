"""Generated story regression tests. Do not hand-edit."""
from __future__ import annotations

import importlib
import pytest

STORY_ID = 'pdd_story_gate_identity'
STORY_HASH = 'f77dcbd4dfce4f4d'
ENTRY_MODULE = 'pdd.story_regression_gate'
ENTRY_CALLABLE = 'story_id_from_path'
ENTRY_ARGS = ["user_stories/story__pdd_generate.md"]
ENTRY_KWARGS = {}
SEAMS = []


@pytest.fixture()
def story_result(monkeypatch):
    for target, value in SEAMS:
        monkeypatch.setattr(target, value)
    module = importlib.import_module(ENTRY_MODULE)
    entry = getattr(module, ENTRY_CALLABLE)
    return entry(*ENTRY_ARGS, **ENTRY_KWARGS)

@pytest.mark.story(story_id=STORY_ID, story_hash=STORY_HASH)
def test_story_pdd_story_gate_identity_R1_oracle_1(story_result):
    result = story_result
    assert result == "pdd_generate"
