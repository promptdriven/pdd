"""
Test Plan for agentic_bug_step9_generate_LLM.prompt

This test file verifies that the Step 9 prompt blocks structural/shape test
code generation and requires behavioral assertions only.

Issue #838: pdd bug generates structural tests instead of behavioral tests

The bug: Step 9 generated test code using inspect.signature(), hasattr(), and
similar introspection patterns. The weak one-liner 'Focus on testing behavior'
was insufficient to prevent this.

These tests verify the prompt contains explicit blocking guidance.

Test Categories:
1. Unit tests: Verify prompt blocks structural test code patterns
2. Unit tests: Verify prompt requires behavioral assertions
3. Unit tests: Verify prompt includes self-check before each test
4. Unit tests: Verify the Important section forbids introspection
"""

from pathlib import Path

import pytest


# --- Constants ---

PROMPT_PATH = Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_bug_step9_generate_LLM.prompt"


# --- Fixtures ---


@pytest.fixture
def prompt_content() -> str:
    """Load the Step 9 prompt content."""
    assert PROMPT_PATH.exists(), f"Prompt file not found: {PROMPT_PATH}"
    return PROMPT_PATH.read_text()


# --- Tests ---


class TestStep9BlocksStructuralCode:
    """Step 9 must explicitly block structural/shape test code generation."""

    def test_prompt_blocks_reflection_introspection(self, prompt_content: str) -> None:
        """Verify prompt blocks reflection/introspection in generated code."""
        content_lower = prompt_content.lower()
        has_block = (
            "reflection" in content_lower
            or "introspection" in content_lower
            or "inspect.signature()" in content_lower
        )
        assert has_block, (
            "Step 9 prompt must block reflection/introspection patterns in "
            "generated test code."
        )

    def test_prompt_blocks_existence_checks(self, prompt_content: str) -> None:
        """Verify prompt blocks existence/shape checks in generated code."""
        content_lower = prompt_content.lower()
        has_block = (
            "existence checks" in content_lower
            or "hasattr()" in content_lower
            or "attribute/method existence" in content_lower
        )
        assert has_block, (
            "Step 9 prompt must block existence checks in generated test code."
        )

    def test_prompt_blocks_source_scanning(self, prompt_content: str) -> None:
        """Verify prompt blocks source code scanning in generated tests.

        Some LLMs generate tests that read the source file and check for
        keywords — this is another form of structural testing.
        """
        content_lower = prompt_content.lower()
        has_block = "source code scanning" in content_lower or "source scanning" in content_lower
        assert has_block, (
            "Step 9 prompt must block source code scanning patterns."
        )

    def test_prompt_is_language_agnostic(self, prompt_content: str) -> None:
        """Verify the blocking rule applies to all languages."""
        content_lower = prompt_content.lower()
        has_language_agnostic = (
            "every language" in content_lower
            or "all languages" in content_lower
            or "any language" in content_lower
        )
        assert has_language_agnostic, (
            "Step 9 structural test blocking must be language-agnostic."
        )


class TestStep9RequiresBehavioralAssertions:
    """Step 9 must require behavioral assertions that test observable outcomes."""

    def test_prompt_provides_bad_code_example(self, prompt_content: str) -> None:
        """Verify prompt provides a BAD (structural) test code example."""
        content_lower = prompt_content.lower()
        has_bad = "bad test" in content_lower and "structural" in content_lower
        assert has_bad, (
            "Step 9 prompt must provide a BAD (structural) test code example."
        )

    def test_prompt_provides_good_code_example(self, prompt_content: str) -> None:
        """Verify prompt provides a GOOD (behavioral) test code example."""
        content_lower = prompt_content.lower()
        has_good = "good test" in content_lower and "behavioral" in content_lower
        assert has_good, (
            "Step 9 prompt must provide a GOOD (behavioral) test code example."
        )

    def test_bad_example_shows_the_anti_pattern(self, prompt_content: str) -> None:
        """Verify the BAD example shows the actual anti-pattern from issue #838.

        The example should show a test that checks whether a function accepts
        a parameter without ever calling it.
        """
        content_lower = prompt_content.lower()
        has_anti_pattern = (
            ("accepts" in content_lower or "exists" in content_lower)
            and "without" in content_lower
            and ("calling" in content_lower or "invoking" in content_lower or "ever calling" in content_lower)
        )
        assert has_anti_pattern, (
            "Step 9 BAD example must show the anti-pattern: checking parameter "
            "existence without calling the function."
        )

    def test_good_example_shows_calling_and_asserting(self, prompt_content: str) -> None:
        """Verify the GOOD example shows calling the function and asserting on output."""
        content_lower = prompt_content.lower()
        has_behavioral = (
            ("calls" in content_lower or "calling" in content_lower)
            and ("assert" in content_lower or "output" in content_lower or "side effect" in content_lower)
        )
        assert has_behavioral, (
            "Step 9 GOOD example must show calling the function and asserting "
            "on observable output or side effects."
        )


class TestStep9SelfCheck:
    """Step 9 must include a self-check before writing each test."""

    def test_prompt_includes_self_check(self, prompt_content: str) -> None:
        """Verify the prompt includes a self-check question."""
        content_lower = prompt_content.lower()
        assert "self-check" in content_lower, (
            "Step 9 prompt must include a self-check asking whether a test could "
            "pass by merely adding a parameter default without implementing logic."
        )

    def test_self_check_mentions_stub_or_signature(self, prompt_content: str) -> None:
        """Verify the self-check references the key failure mode."""
        content_lower = prompt_content.lower()
        has_failure_mode = (
            "empty stub" in content_lower
            or "function signature" in content_lower
            or "just added" in content_lower
            or "just changed" in content_lower
        )
        assert has_failure_mode, (
            "Step 9 self-check must reference the failure mode: passing by "
            "adding a stub or changing a signature."
        )


class TestStep9ImportantSectionForbidsIntrospection:
    """The Important section must explicitly forbid introspection-based tests."""

    def test_important_section_exists(self, prompt_content: str) -> None:
        """Verify the prompt has an Important section."""
        assert "% important" in prompt_content.lower() or "% Important" in prompt_content, (
            "Step 9 prompt must have an Important section."
        )

    def test_important_section_forbids_introspection(self, prompt_content: str) -> None:
        """Verify the Important section explicitly forbids introspection.

        The weak one-liner 'Focus on testing behavior' in the old Important
        section was insufficient to prevent issue #838. The section must
        explicitly name the forbidden patterns.
        """
        content_lower = prompt_content.lower()
        important_idx = content_lower.rfind("% important")
        if important_idx == -1:
            pytest.fail("Step 9 prompt must have an Important section.")
        important_section = content_lower[important_idx:]
        has_introspection_ban = (
            "reflection" in important_section
            or "introspection" in important_section
            or "inspect.signature()" in important_section
        )
        assert has_introspection_ban, (
            "Step 9 Important section must explicitly forbid reflection, "
            "introspection, or similar patterns — the weak one-liner "
            "'Focus on testing behavior' was insufficient to prevent issue #838."
        )
