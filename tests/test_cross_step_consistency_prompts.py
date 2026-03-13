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
        """Verify Step 8 explicitly lists BLOCKED structural anti-patterns."""
        content_lower = step8_content.lower()
        # Must mention the key structural anti-patterns that led to issue #838
        has_inspect_block = "inspect.signature()" in content_lower or "inspect.getfullargspec()" in content_lower
        has_hasattr_block = "hasattr()" in content_lower or "getattr()" in content_lower
        has_param_check_block = "sig.parameters" in content_lower
        assert has_inspect_block, (
            "Step 8 prompt must explicitly block inspect.signature() as a structural "
            "anti-pattern — this was the exact pattern that caused issue #838."
        )
        assert has_hasattr_block, (
            "Step 8 prompt must explicitly block hasattr()/getattr() attribute checks."
        )
        assert has_param_check_block, (
            "Step 8 prompt must explicitly block 'sig.parameters' pattern checks."
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
        """Verify Step 9 explicitly lists BLOCKED structural code patterns."""
        content_lower = step9_content.lower()
        has_inspect_block = "inspect.signature()" in content_lower or "inspect.getfullargspec()" in content_lower
        has_hasattr_block = "hasattr()" in content_lower or "getattr()" in content_lower
        has_param_check_block = "sig.parameters" in content_lower
        assert has_inspect_block, (
            "Step 9 prompt must explicitly block inspect.signature() in generated test code."
        )
        assert has_hasattr_block, (
            "Step 9 prompt must explicitly block hasattr()/getattr() in generated test code."
        )
        assert has_param_check_block, (
            "Step 9 prompt must explicitly block 'sig.parameters' pattern in generated test code."
        )

    def test_prompt_provides_bad_good_code_examples(self, step9_content: str) -> None:
        """Verify Step 9 provides BAD and GOOD Python code examples."""
        content_lower = step9_content.lower()
        # Must have concrete Python code showing the bad and good patterns
        has_bad_code = (
            "bad" in content_lower
            and "inspect.signature" in content_lower
            and 'assert "quiet" in sig.parameters' in content_lower.replace("'", '"')
        )
        has_good_code = (
            "good" in content_lower
            and "patch" in content_lower
            and "mock" in content_lower
        )
        assert has_bad_code, (
            "Step 9 prompt must provide a BAD code example showing the exact "
            "inspect.signature anti-pattern from issue #838."
        )
        assert has_good_code, (
            "Step 9 prompt must provide a GOOD code example using mocks/patches "
            "to verify observable behavior."
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

    def test_both_prompts_block_same_anti_patterns(self, step8_content: str, step9_content: str) -> None:
        """Verify both prompts block inspect.signature, hasattr, and sig.parameters."""
        anti_patterns = ["inspect.signature()", "hasattr()", "sig.parameters"]
        for pattern in anti_patterns:
            in_step8 = pattern in step8_content.lower()
            in_step9 = pattern in step9_content.lower()
            assert in_step8 and in_step9, (
                f"Anti-pattern '{pattern}' must be blocked in BOTH Step 8 and Step 9 "
                f"prompts. Found in step8={in_step8}, step9={in_step9}. "
                f"A gap in either prompt allows structural tests to slip through."
            )
