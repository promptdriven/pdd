"""
Test Plan for agentic_bug_step8_test_plan_LLM.prompt

This test file verifies that the Step 8 prompt blocks structural/shape test
anti-patterns and requires behavioral tests only.

Issue #838: pdd bug generates structural tests instead of behavioral tests

The bug: The LLM generated tests using inspect.signature(), hasattr(), and
similar introspection patterns that pass by merely adding a parameter to a
function signature without implementing any actual logic.

These tests verify the prompt contains sufficient guidance to prevent this.

Test Categories:
1. Unit tests: Verify prompt blocks structural anti-patterns
2. Unit tests: Verify prompt requires behavioral testing
3. Unit tests: Verify prompt includes self-check heuristic
"""

from pathlib import Path

import pytest


# --- Constants ---

PROMPT_PATH = Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_bug_step8_test_plan_LLM.prompt"


# --- Fixtures ---


@pytest.fixture
def prompt_content() -> str:
    """Load the Step 8 prompt content."""
    assert PROMPT_PATH.exists(), f"Prompt file not found: {PROMPT_PATH}"
    return PROMPT_PATH.read_text()


# --- Tests ---


class TestStep8BlocksStructuralPatterns:
    """Step 8 must explicitly block structural/shape testing anti-patterns."""

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
            "Step 8 prompt must block reflection/introspection patterns — "
            "either explicitly or via a language-agnostic rule."
        )

    def test_prompt_blocks_existence_checks(self, prompt_content: str) -> None:
        """Verify prompt blocks existence/shape checks.

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
            "Step 8 prompt must block existence checks (hasattr, getattr, etc.)."
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
            "Step 8 prompt must block signature inspection patterns."
        )

    def test_prompt_is_language_agnostic(self, prompt_content: str) -> None:
        """Verify the blocking rule applies to all languages, not just Python.

        The prompt should say 'every language' or 'all languages' to prevent
        the LLM from thinking the rule only applies to Python.
        """
        content_lower = prompt_content.lower()
        has_language_agnostic = (
            "every language" in content_lower
            or "all languages" in content_lower
            or "any language" in content_lower
        )
        assert has_language_agnostic, (
            "Step 8 structural test blocking must be language-agnostic — "
            "the prompt should state the rule applies to every language."
        )


class TestStep8RequiresBehavioralTesting:
    """Step 8 must require behavioral tests that verify observable outcomes."""

    def test_prompt_provides_bad_example(self, prompt_content: str) -> None:
        """Verify prompt provides a BAD (structural) test plan example."""
        content_lower = prompt_content.lower()
        has_bad = "bad test plan" in content_lower or (
            "bad" in content_lower and "structural" in content_lower
        )
        assert has_bad, (
            "Step 8 prompt must provide a BAD (structural) test plan example "
            "to show the LLM what NOT to do."
        )

    def test_prompt_provides_good_example(self, prompt_content: str) -> None:
        """Verify prompt provides a GOOD (behavioral) test plan example."""
        content_lower = prompt_content.lower()
        has_good = "good test plan" in content_lower or (
            "good" in content_lower and "behavioral" in content_lower
        )
        assert has_good, (
            "Step 8 prompt must provide a GOOD (behavioral) test plan example "
            "to show the LLM what TO do."
        )

    def test_good_example_involves_calling_function(self, prompt_content: str) -> None:
        """Verify the GOOD example demonstrates calling the function under test.

        A behavioral test must invoke the function and assert on its output.
        The example should show this pattern.
        """
        content_lower = prompt_content.lower()
        # The good example should mention calling/invoking and asserting on output
        has_call_pattern = (
            ("call" in content_lower or "calling" in content_lower)
            and ("assert" in content_lower or "verify" in content_lower)
        )
        assert has_call_pattern, (
            "Step 8 GOOD example must demonstrate calling the function and "
            "asserting on observable output."
        )


class TestStep8SelfCheckHeuristic:
    """Step 8 must include a self-check heuristic to catch structural tests."""

    def test_prompt_includes_self_check(self, prompt_content: str) -> None:
        """Verify the prompt includes a self-check question.

        The self-check asks: 'Could this test pass if someone just changed the
        function signature or added an empty stub without implementing any
        actual logic?'
        """
        content_lower = prompt_content.lower()
        has_self_check = "self-check" in content_lower
        assert has_self_check, (
            "Step 8 prompt must include a self-check heuristic asking whether "
            "a test could pass by merely adding a parameter or empty stub."
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
            "Step 8 self-check must mention the failure mode: a test that passes "
            "by merely changing the signature or adding an empty stub."
        )
