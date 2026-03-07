"""
Tests for cross-step consistency validation in bug workflow prompts.

Issue #577: PDD bot generates fixes that pass mocked tests but don't solve the
real bug because test mocks encode assumptions that contradict the bot's own
investigation findings from earlier steps.

These tests verify that Steps 8 (test plan), 9 (generate test), and 10 (verify)
prompts instruct the LLM to cross-validate test assumptions against investigation
findings from Steps 4-6.
"""
from pathlib import Path
import pytest

PROMPTS_DIR = Path(__file__).parent.parent / "pdd" / "prompts"

@pytest.fixture
def step8_content() -> str:
    path = PROMPTS_DIR / "agentic_bug_step8_test_plan_LLM.prompt"
    assert path.exists()
    return path.read_text()

@pytest.fixture
def step9_content() -> str:
    path = PROMPTS_DIR / "agentic_bug_step9_generate_LLM.prompt"
    assert path.exists()
    return path.read_text()

@pytest.fixture
def step10_content() -> str:
    path = PROMPTS_DIR / "agentic_bug_step10_verify_LLM.prompt"
    assert path.exists()
    return path.read_text()


class TestStep8CrossStepConsistency:
    """Step 8 (test plan) must instruct cross-referencing mocks against Steps 4-6."""

    def test_prompt_requires_mock_validation_against_prior_steps(self, step8_content: str) -> None:
        content_lower = step8_content.lower()
        has_instruction = any([
            "cross-reference" in content_lower and "steps 4" in content_lower,
            "cross-validate" in content_lower and "investigation" in content_lower,
            "consistent with" in content_lower and ("step 4" in content_lower or "step 5" in content_lower or "step 6" in content_lower),
        ])
        assert has_instruction, (
            "Step 8 prompt must instruct cross-referencing planned mocks/assumptions "
            "against investigation findings from Steps 4-6."
        )

    def test_prompt_requires_contradiction_resolution(self, step8_content: str) -> None:
        content_lower = step8_content.lower()
        has_instruction = "contradict" in content_lower and ("redesign" in content_lower or "document" in content_lower or "resolution" in content_lower)
        assert has_instruction, (
            "Step 8 prompt must instruct resolving contradictions between test "
            "assumptions and investigation findings, not silently proceeding."
        )


class TestStep9MockAccuracyValidation:
    """Step 9 (generate test) must instruct validating mocks against investigation."""

    def test_prompt_requires_mock_consistency_with_investigation(self, step9_content: str) -> None:
        content_lower = step9_content.lower()
        has_instruction = any([
            "re-read steps 4" in content_lower,
            "verify" in content_lower and "mock" in content_lower and ("step 4" in content_lower or "step 5" in content_lower or "step 6" in content_lower),
            "mock" in content_lower and "investigation findings" in content_lower,
        ])
        assert has_instruction, (
            "Step 9 prompt must instruct verifying mock responses against "
            "investigation findings from Steps 4-6."
        )

    def test_prompt_flags_impossible_mocks(self, step9_content: str) -> None:
        content_lower = step9_content.lower()
        has_instruction = any([
            "flag" in content_lower and "impossible" in content_lower,
            "signal" in content_lower and "fix direction" in content_lower,
            "better to flag" in content_lower,
        ])
        assert has_instruction, (
            "Step 9 prompt must instruct flagging when no mock can be both "
            "consistent with investigation AND demonstrate the fix working."
        )


class TestStep10CrossValidation:
    """Step 10 (verify) must cross-validate test mocks against investigation."""

    def test_prompt_requires_mock_vs_investigation_check(self, step10_content: str) -> None:
        content_lower = step10_content.lower()
        has_instruction = any([
            "cross-validate" in content_lower and ("step 4" in content_lower or "step 5" in content_lower or "step 6" in content_lower),
            "mock" in content_lower and "contradict" in content_lower and "investigation" in content_lower,
            "verify" in content_lower and "mock" in content_lower and "real" in content_lower and "behavior" in content_lower,
        ])
        assert has_instruction, (
            "Step 10 prompt must instruct cross-validating test mocks against "
            "investigation findings from Steps 4-6."
        )

    def test_prompt_can_fail_for_assumption_mismatch(self, step10_content: str) -> None:
        has_fail_signal = "mock assumptions contradict investigation" in step10_content.lower()
        assert has_fail_signal, (
            "Step 10 prompt must define a FAIL condition for when mock assumptions "
            "contradict investigation findings (enables orchestrator hard stop)."
        )
