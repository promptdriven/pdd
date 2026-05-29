"""Regression: generate_test_LLM must expand context/test.prompt for contract rules."""
from __future__ import annotations

import os
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]


@pytest.fixture(autouse=True)
def _pin_pdd_path(monkeypatch: pytest.MonkeyPatch) -> None:
    """Match production layout: packaged prompts live under the repo's pdd/ tree."""
    monkeypatch.setenv("PDD_PATH", str(REPO_ROOT / "pdd"))
    monkeypatch.setenv("PDD_QUIET", "1")


def test_generate_test_llm_preprocess_expands_contract_rule_test_context() -> None:
    """
    The legacy pdd test LLM template must inline context/test.prompt so contract
    rule IDs reach the model. Literal ``<include>s module`` prose previously
    paired with the real closing tag and blocked expansion.
    """
    from pdd.load_prompt_template import load_prompt_template
    from pdd.preprocess import preprocess

    preprocessed = preprocess(
        load_prompt_template("generate_test_LLM"),
        recursive=False,
        double_curly_brackets=False,
    )

    assert "CONTRACT RULE TEST PLANNING" in preprocessed
    assert "negative test for each MUST NOT rule" in preprocessed
    assert "Preserve existing accumulated tests" in preprocessed
    assert "<include optional>context/test.prompt</include>" not in preprocessed
    assert "<include>s module" not in preprocessed
