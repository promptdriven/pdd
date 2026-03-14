"""
Unit tests for agentic_bug_step9_generate_LLM.prompt

Issue #838: pdd bug generates structural tests (param existence checks)
instead of behavioral tests.

The Step 9 prompt instructs the LLM to generate actual test code. Without
explicit anti-pattern guidance against inspect.signature(), hasattr(), and
sig.parameters, the LLM generates structural tests that pass by merely
adding parameters to function signatures without implementing behavior.

The existing caller-vs-callee anti-pattern (lines 51-74, from PR #249) only
covers one narrow case. The broader class of shape-testing anti-patterns
(inspect.signature, hasattr, isinstance on functions) is completely missing.

These tests FAIL on the current buggy prompt and PASS once the fix is applied.
"""

from pathlib import Path

import pytest

PROMPT_PATH = Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_bug_step9_generate_LLM.prompt"


@pytest.fixture
def prompt_content() -> str:
    """Load the Step 9 test generation prompt content."""
    assert PROMPT_PATH.exists(), f"Prompt file not found: {PROMPT_PATH}"
    return PROMPT_PATH.read_text()


class TestStep9BlocksStructuralPatterns:
    """Step 9 must explicitly block structural/shape test code patterns."""

    def test_prompt_blocks_reflection_introspection(self, prompt_content: str) -> None:
        """Verify prompt blocks reflection/introspection patterns.

        The prompt must block structural anti-patterns like inspect.signature(),
        hasattr(), sig.parameters — either by naming them explicitly or via a
        language-agnostic rule covering all reflection/introspection.
        """
        content_lower = prompt_content.lower()
        has_block = (
            "reflection" in content_lower
            or "introspection" in content_lower
            or "inspect.signature()" in content_lower
        )
        assert has_block, (
            "Step 9 prompt must block reflection/introspection patterns."
        )

    def test_prompt_blocks_existence_checks(self, prompt_content: str) -> None:
        """Verify prompt blocks existence/shape checks in test code.

        The prompt must block patterns that verify something *exists* rather
        than testing what *happens* when it's used.
        """
        content_lower = prompt_content.lower()
        has_block = (
            "existence checks" in content_lower
            or "hasattr()" in content_lower
            or "attribute/method existence" in content_lower
        )
        assert has_block, (
            "Step 9 prompt must block existence checks (hasattr, getattr, etc.)."
        )

    def test_prompt_blocks_signature_inspection(self, prompt_content: str) -> None:
        """Verify prompt blocks signature inspection patterns.

        The issue #838 anti-pattern was inspect.signature() + sig.parameters.
        The prompt must block this either explicitly or via general rule.
        """
        content_lower = prompt_content.lower()
        has_block = (
            "signature inspection" in content_lower
            or "sig.parameters" in content_lower
            or "inspect.signature()" in content_lower
        )
        assert has_block, (
            "Step 9 prompt must block signature inspection patterns."
        )


class TestStep9BadGoodCodeExamples:
    """Step 9 must provide BAD and GOOD Python code examples."""

    def test_prompt_has_bad_structural_example(self, prompt_content: str) -> None:
        """Verify prompt shows a BAD example of structural testing.

        The LLM needs a concrete negative example showing what NOT to generate.
        This can be a specific code snippet or a descriptive example.
        """
        content_lower = prompt_content.lower()
        has_bad = (
            ("bad" in content_lower and "structural" in content_lower)
            or "bad test" in content_lower
            or ("never generate" in content_lower and "structural" in content_lower)
        )
        assert has_bad, (
            "Step 9 prompt must show a BAD example of structural testing "
            "to teach the LLM what NOT to generate."
        )

    def test_prompt_has_good_code_with_mock_patch(self, prompt_content: str) -> None:
        """Verify prompt shows a GOOD code example using mock/patch.

        The positive example must demonstrate behavioral testing with
        mocks/patches to verify observable output/behavior.
        """
        content_lower = prompt_content.lower()
        has_good_code = (
            "good" in content_lower
            and ("patch" in content_lower or "mock" in content_lower)
        )
        assert has_good_code, (
            "Step 9 prompt must show a GOOD code example using mocks/patches "
            "for behavioral assertions."
        )


class TestStep9SelfCheck:
    """Step 9 must include a self-check before writing each test."""

    def test_prompt_includes_self_check(self, prompt_content: str) -> None:
        """Verify prompt asks: could this test pass by just adding a parameter?

        The self-check catches structural tests at code generation time.
        This is the last line of defense before Step 10's TDD validation,
        which cannot distinguish structural from behavioral tests.
        """
        content_lower = prompt_content.lower()
        has_self_check = (
            "self-check" in content_lower
            and ("could this test pass" in content_lower or "just added" in content_lower)
        )
        assert has_self_check, (
            "Step 9 prompt must include a self-check: 'Could this test pass "
            "if someone just added quiet=False without implementing logic?'"
        )


class TestStep9ImportantSectionForbidsIntrospection:
    """The Important section must explicitly forbid introspection-based tests."""

    def test_important_section_bans_introspection(self, prompt_content: str) -> None:
        """Verify the Important section names introspection as forbidden.

        The original prompt had only: 'Focus on testing behavior, not
        implementation details' — a vague one-liner insufficient to prevent
        the LLM from generating inspect.signature() checks. The Important
        section must explicitly name the forbidden patterns.
        """
        content_lower = prompt_content.lower()
        important_idx = content_lower.rfind("% important")
        assert important_idx != -1, "Step 9 prompt must have an Important section."
        important_section = content_lower[important_idx:]
        has_ban = (
            "inspect.signature()" in important_section
            or "hasattr()" in important_section
            or "introspection" in important_section
        )
        assert has_ban, (
            "Step 9 Important section must explicitly forbid introspection-based "
            "tests (inspect.signature, hasattr). The weak one-liner 'Focus on "
            "testing behavior' was insufficient to prevent issue #838."
        )
