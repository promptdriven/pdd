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


class TestStep8BlocksStructuralTests:
    """Step 8 (test plan) must block structural/shape anti-patterns (issue #838)."""

    def test_prompt_blocks_structural_anti_patterns(self, step8_content: str) -> None:
        """Verify Step 8 blocks structural anti-patterns (language-agnostic)."""
        content_lower = step8_content.lower()
        has_block = (
            ("reflection" in content_lower or "introspection" in content_lower)
            and ("existence checks" in content_lower or "attribute/method existence" in content_lower)
            and ("signature inspection" in content_lower or "signature" in content_lower)
        )
        assert has_block, (
            "Step 8 prompt must block reflection, introspection, existence checks, "
            "and signature inspection patterns."
        )

    def test_prompt_provides_bad_good_examples(self, step8_content: str) -> None:
        """Verify Step 8 provides BAD and GOOD test plan examples."""
        content_lower = step8_content.lower()
        has_bad_example = "bad test plan" in content_lower or ("bad" in content_lower and "structural" in content_lower)
        has_good_example = "good test plan" in content_lower or ("good" in content_lower and "behavioral" in content_lower)
        assert has_bad_example and has_good_example, (
            "Step 8 prompt must provide both BAD (structural) and GOOD (behavioral) "
            "test plan examples to guide the LLM away from shape-testing."
        )

    def test_prompt_includes_self_check_heuristic(self, step8_content: str) -> None:
        """Verify Step 8 includes a self-check question to catch structural tests."""
        content_lower = step8_content.lower()
        # The self-check asks: could this test pass if someone just added a parameter?
        has_self_check = (
            "self-check" in content_lower
            and ("could this test pass" in content_lower or "just added" in content_lower)
        )
        assert has_self_check, (
            "Step 8 prompt must include a self-check heuristic asking whether "
            "a test could pass by merely adding a parameter to the signature."
        )


class TestStep9BlocksStructuralTests:
    """Step 9 (test generation) must block structural/shape test code (issue #838)."""

    def test_prompt_blocks_structural_test_code(self, step9_content: str) -> None:
        """Verify Step 9 blocks structural code patterns (language-agnostic)."""
        content_lower = step9_content.lower()
        has_block = (
            ("reflection" in content_lower or "introspection" in content_lower)
            and ("existence checks" in content_lower or "attribute/method existence" in content_lower)
            and ("signature inspection" in content_lower or "signature" in content_lower)
        )
        assert has_block, (
            "Step 9 prompt must block reflection, introspection, existence checks, "
            "and signature inspection patterns."
        )

    def test_prompt_provides_bad_good_code_examples(self, step9_content: str) -> None:
        """Verify Step 9 provides BAD and GOOD examples."""
        content_lower = step9_content.lower()
        has_bad = "bad" in content_lower and "structural" in content_lower
        has_good = "good" in content_lower and "behavioral" in content_lower
        assert has_bad, (
            "Step 9 prompt must provide a BAD structural example."
        )
        assert has_good, (
            "Step 9 prompt must provide a GOOD behavioral example."
        )

    def test_prompt_includes_self_check(self, step9_content: str) -> None:
        """Verify Step 9 includes a self-check before writing each test."""
        content_lower = step9_content.lower()
        has_self_check = (
            "self-check" in content_lower
            and ("could this test pass" in content_lower or "just added" in content_lower)
        )
        assert has_self_check, (
            "Step 9 prompt must include a self-check asking whether a test could "
            "pass by merely adding a parameter default without implementing logic."
        )

    def test_important_section_forbids_introspection(self, step9_content: str) -> None:
        """Verify the Important section explicitly forbids introspection-based tests."""
        content_lower = step9_content.lower()
        # The Important section must explicitly mention inspect.signature and hasattr
        important_idx = content_lower.rfind("% important")
        assert important_idx != -1, "Step 9 prompt must have an Important section."
        important_section = content_lower[important_idx:]
        has_introspection_ban = (
            "inspect.signature()" in important_section
            or "hasattr()" in important_section
            or "introspection" in important_section
        )
        assert has_introspection_ban, (
            "Step 9 Important section must explicitly forbid inspect.signature(), "
            "hasattr(), or similar introspection — the weak one-liner 'Focus on "
            "testing behavior' was insufficient to prevent issue #838."
        )


class TestCrossPromptStructuralTestConsistency:
    """Both Step 8 and Step 9 must block the same core anti-patterns (issue #838)."""

    def test_both_prompts_block_same_concepts(self, step8_content: str, step9_content: str) -> None:
        """Verify both prompts block the same structural testing concepts."""
        concepts = ["reflection", "introspection", "existence checks", "signature inspection"]
        for concept in concepts:
            in_step8 = concept in step8_content.lower()
            in_step9 = concept in step9_content.lower()
            assert in_step8 or in_step9, (
                f"Concept '{concept}' should be present in at least one of "
                f"Step 8 or Step 9 prompts. Found in step8={in_step8}, step9={in_step9}."
            )
