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

    def test_prompt_blocks_inspect_signature(self, prompt_content: str) -> None:
        """Verify prompt explicitly names inspect.signature() as blocked.

        The issue #838 root cause: the LLM generated
        `sig = inspect.signature(fn); assert 'quiet' in sig.parameters`
        because the prompt had no mention of this anti-pattern.
        """
        content_lower = prompt_content.lower()
        assert "inspect.signature()" in content_lower or "inspect.getfullargspec()" in content_lower, (
            "Step 9 prompt must explicitly block inspect.signature() in generated "
            "test code — the exact pattern from issue #838."
        )

    def test_prompt_blocks_hasattr_getattr(self, prompt_content: str) -> None:
        """Verify prompt explicitly blocks hasattr()/getattr() in test code.

        These are shape-testing patterns that verify code structure rather than
        observable behavior.
        """
        content_lower = prompt_content.lower()
        assert "hasattr()" in content_lower or "getattr()" in content_lower, (
            "Step 9 prompt must explicitly block hasattr()/getattr() in test code."
        )

    def test_prompt_blocks_sig_parameters(self, prompt_content: str) -> None:
        """Verify prompt explicitly blocks sig.parameters pattern.

        `assert 'quiet' in sig.parameters` was the exact assertion from #838
        that allowed a fix to pass by merely adding quiet=False to signatures.
        """
        assert "sig.parameters" in prompt_content.lower(), (
            "Step 9 prompt must block 'sig.parameters' — the pattern from #838."
        )


class TestStep9BadGoodCodeExamples:
    """Step 9 must provide BAD and GOOD Python code examples."""

    def test_prompt_has_bad_code_with_inspect_signature(self, prompt_content: str) -> None:
        """Verify prompt shows a BAD code example using inspect.signature().

        The LLM needs a concrete code snippet showing the anti-pattern to avoid.
        Without it, the LLM defaults to easier structural assertions.
        """
        content_lower = prompt_content.lower()
        has_bad_code = (
            "bad" in content_lower
            and "inspect.signature" in content_lower
            and "sig.parameters" in content_lower.replace("'", '"')
        )
        assert has_bad_code, (
            "Step 9 prompt must show a BAD code example with inspect.signature() "
            "and sig.parameters — the exact anti-pattern from issue #838."
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
