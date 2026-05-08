"""Prompt contract tests for issue-level complexity splitting."""
from __future__ import annotations

from pathlib import Path


def test_complexity_prompt_requires_independently_shippable_splits() -> None:
    prompt = Path("pdd/prompts/agentic_arch_step1b_complexity_LLM.prompt").read_text(
        encoding="utf-8"
    )

    required_phrases = [
        "independently implementable and independently verifiable",
        "Do NOT create prompt-only, architecture-only, test-only, or review-only sub-issues",
        "Create 2 sub-issues by default; create 3 only when",
        "Preserve one parent-level acceptance test",
    ]

    missing = [phrase for phrase in required_phrases if phrase not in prompt]
    assert missing == []


def test_step9_prompt_requires_existing_module_contract_context() -> None:
    prompt = Path("pdd/prompts/agentic_arch_step9_prompts_LLM.prompt").read_text(
        encoding="utf-8"
    )

    required_phrases = [
        "For existing modules, the declared interface and LLM context must stay aligned.",
        "full `<include>` of that source file",
        "targeted `<include select=\"...\">` that covers every existing public symbol",
        "`<pdd-dependency>` is architecture metadata, not LLM context",
    ]

    missing = [phrase for phrase in required_phrases if phrase not in prompt]
    assert missing == []
