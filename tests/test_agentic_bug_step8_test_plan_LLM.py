"""
Unit tests for agentic_bug_step8_test_plan_LLM.prompt

Issue #838: pdd bug generates structural tests (param existence checks)
instead of behavioral tests.

The Step 8 prompt designs the test plan that Step 9 implements. Without
explicit anti-shape-testing constraints, the LLM designs test plans using
inspect.signature() / hasattr() / sig.parameters checks that pass by
merely adding parameters to function signatures without implementing logic.

These tests FAIL on the current buggy prompt and PASS once the fix is applied.
"""

from pathlib import Path

import pytest

PROMPT_PATH = Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_bug_step8_test_plan_LLM.prompt"


@pytest.fixture
def prompt_content() -> str:
    """Load the Step 8 test plan prompt content."""
    assert PROMPT_PATH.exists(), f"Prompt file not found: {PROMPT_PATH}"
    return PROMPT_PATH.read_text()


class TestStep8BlocksInspectSignature:
    """Step 8 must explicitly block inspect.signature() anti-pattern."""

    def test_prompt_mentions_inspect_signature_as_blocked(self, prompt_content: str) -> None:
        """Verify prompt explicitly names inspect.signature() as a blocked pattern.

        This is the exact anti-pattern from issue #838: the LLM generated
        `sig = inspect.signature(fn); assert 'quiet' in sig.parameters`
        instead of behavioral tests verifying output suppression.
        """
        content_lower = prompt_content.lower()
        assert "inspect.signature()" in content_lower or "inspect.getfullargspec()" in content_lower, (
            "Step 8 prompt must explicitly block inspect.signature() — "
            "this was the exact anti-pattern that caused issue #838."
        )

    def test_prompt_mentions_sig_parameters_as_blocked(self, prompt_content: str) -> None:
        """Verify prompt explicitly blocks sig.parameters pattern.

        The issue #838 tests used `assert 'quiet' in sig.parameters` which
        passes by merely adding quiet=False to a function signature.
        """
        assert "sig.parameters" in prompt_content.lower(), (
            "Step 8 prompt must block 'sig.parameters' — the pattern used in "
            "issue #838 structural tests."
        )

    def test_prompt_mentions_hasattr_as_blocked(self, prompt_content: str) -> None:
        """Verify prompt explicitly blocks hasattr()/getattr() checks.

        hasattr() checks are another form of structural testing that verifies
        code shape rather than behavior.
        """
        content_lower = prompt_content.lower()
        assert "hasattr()" in content_lower or "getattr()" in content_lower, (
            "Step 8 prompt must block hasattr()/getattr() attribute checks."
        )


class TestStep8ProvidesExamples:
    """Step 8 must show BAD (structural) vs GOOD (behavioral) test plan examples."""

    def test_prompt_has_bad_structural_example(self, prompt_content: str) -> None:
        """Verify prompt provides a BAD example showing the structural anti-pattern.

        Without a concrete negative example, the LLM defaults to the easier
        structural approach when designing test plans.
        """
        content_lower = prompt_content.lower()
        has_bad = (
            ("bad" in content_lower and "structural" in content_lower)
            or "bad test plan" in content_lower
        )
        assert has_bad, (
            "Step 8 prompt must provide a BAD example showing structural test plans "
            "to teach the LLM what NOT to design."
        )

    def test_prompt_has_good_behavioral_example(self, prompt_content: str) -> None:
        """Verify prompt provides a GOOD example showing behavioral testing.

        The LLM needs a concrete positive example demonstrating mock-based
        behavioral assertions to follow.
        """
        content_lower = prompt_content.lower()
        has_good = (
            ("good" in content_lower and "behavioral" in content_lower)
            or "good test plan" in content_lower
        )
        assert has_good, (
            "Step 8 prompt must provide a GOOD example showing behavioral test plans."
        )


class TestStep8SelfCheck:
    """Step 8 must include a self-check heuristic to catch structural test plans."""

    def test_prompt_includes_self_check_heuristic(self, prompt_content: str) -> None:
        """Verify prompt asks: could this test pass by just adding a parameter?

        The self-check heuristic catches structural tests at the planning stage
        before Step 9 generates code. Without it, the LLM plans structural tests
        that Step 9 faithfully implements.
        """
        content_lower = prompt_content.lower()
        has_self_check = (
            "self-check" in content_lower
            and ("could this test pass" in content_lower or "just added" in content_lower)
        )
        assert has_self_check, (
            "Step 8 prompt must include a self-check heuristic: 'Could this test "
            "pass if someone just added quiet=False to the signature?'"
        )
