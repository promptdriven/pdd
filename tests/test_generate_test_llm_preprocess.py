"""Regression: test LLM templates must expand context/test.prompt for contract rules."""
from __future__ import annotations

from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]

_TEMPLATE_NAMES = ("generate_test_LLM", "generate_test_from_example_LLM")

# Unexpanded include tags that must not survive preprocess for each template.
_FORBIDDEN_UNEXPANDED_INCLUDES: dict[str, tuple[str, ...]] = {
    "generate_test_LLM": (
        "<include optional>context/test.prompt</include>",
        "<include>s module",
    ),
    "generate_test_from_example_LLM": (
        "<include optional>./context/test.prompt</include>",
        "<include optional>context/test.prompt</include>",
    ),
}


@pytest.fixture(autouse=True)
def _pin_pdd_path(monkeypatch: pytest.MonkeyPatch) -> None:
    """Match production layout: packaged prompts live under the repo's pdd/ tree."""
    monkeypatch.setenv("PDD_PATH", str(REPO_ROOT / "pdd"))
    monkeypatch.setenv("PDD_QUIET", "1")


@pytest.mark.parametrize("template_name", _TEMPLATE_NAMES)
def test_generate_test_templates_preprocess_contract_rule_context(
    template_name: str,
) -> None:
    """
    Legacy pdd test LLM templates must inline context/test.prompt so contract
    rule IDs reach the model.

    generate_test_LLM previously had ``<include>s module`` prose that falsely
    paired with the real closing tag and blocked expansion.
    """
    from pdd.load_prompt_template import load_prompt_template
    from pdd.preprocess import preprocess

    preprocessed = preprocess(
        load_prompt_template(template_name),
        recursive=False,
        double_curly_brackets=False,
    )

    assert "CONTRACT RULE TEST PLANNING" in preprocessed
    assert "negative test for each MUST NOT rule" in preprocessed
    assert "Preserve existing accumulated tests" in preprocessed

    for forbidden in _FORBIDDEN_UNEXPANDED_INCLUDES[template_name]:
        assert forbidden not in preprocessed, (
            f"{template_name} left unexpanded include artifact: {forbidden!r}"
        )
