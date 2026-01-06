"""
Test Plan for agentic_bug_step7_generate_LLM.prompt

This test file verifies that the Step 7 prompt provides sufficient guidance for
generating tests that detect caller behavior bugs (e.g., using wrong parameter names).

Issue #247: pdd bug generates tests that verify function signature instead of caller behavior

The bug: When a bug involves incorrect function call arguments (e.g., `limit=` vs `k=`),
the current prompt allows the LLM to generate tests that verify the callee rejects wrong
parameters (always passes) rather than tests that verify the caller uses correct parameters
(would actually fail).

These tests FAIL on the current buggy prompt and PASS once the fix is applied.
"""

from pathlib import Path

import pytest


# --- Constants ---

PROMPT_PATH = Path(__file__).parent.parent / "prompts" / "agentic_bug_step7_generate_LLM.prompt"


# --- Fixtures ---


@pytest.fixture
def step7_prompt_content() -> str:
    """Load the Step 7 prompt content."""
    assert PROMPT_PATH.exists(), f"Prompt file not found: {PROMPT_PATH}"
    return PROMPT_PATH.read_text()


# --- Tests ---


class TestStep7PromptCallerMockingGuidance:
    """
    Test that the Step 7 prompt contains guidance for mocking caller behavior.

    When a bug involves incorrect function call arguments, the test should:
    1. Mock the called function
    2. Invoke the caller code path
    3. Assert the caller passed correct parameter names via mock.call_args

    Without this guidance, the LLM takes the easier path of testing that the
    callee rejects wrong parameters (which always passes since the function
    signature was never broken).
    """

    def test_prompt_mentions_mocking_called_function(self, step7_prompt_content: str) -> None:
        """
        Verify the prompt instructs LLMs to mock the called function when testing caller behavior.

        The prompt should mention using mock/patch to wrap the called function so we can
        inspect what arguments the caller passed.
        """
        content_lower = step7_prompt_content.lower()

        # The prompt should mention mocking for caller behavior testing
        has_mock_guidance = any([
            "mock the called function" in content_lower,
            "mock the callee" in content_lower,
            "patch the function being called" in content_lower,
            "@patch" in step7_prompt_content and "caller" in content_lower,
        ])

        assert has_mock_guidance, (
            "Step 7 prompt lacks guidance on mocking called functions for caller behavior tests. "
            "When a bug involves incorrect function call arguments, tests should mock the callee "
            "and verify the caller passes correct parameters."
        )

    def test_prompt_mentions_call_args_inspection(self, step7_prompt_content: str) -> None:
        """
        Verify the prompt instructs LLMs to use call_args to verify parameter names.

        For bugs where the caller uses wrong parameter names (e.g., limit= vs k=),
        the test must inspect mock.call_args.kwargs to verify correctness.
        """
        content_lower = step7_prompt_content.lower()

        # The prompt should mention call_args for inspecting what was passed
        has_call_args_guidance = any([
            "call_args" in content_lower,
            "call_args.kwargs" in content_lower,
            "assert_called_with" in content_lower and "parameter" in content_lower,
        ])

        assert has_call_args_guidance, (
            "Step 7 prompt lacks guidance on using call_args to verify caller behavior. "
            "For parameter mismatch bugs, tests should use mock.call_args.kwargs to verify "
            "the caller passes the correct parameter names."
        )


class TestStep7PromptAntiPatternWarning:
    """
    Test that the Step 7 prompt warns against testing callee signature for caller bugs.

    The anti-pattern: When the bug is "caller uses limit= but callee expects k=",
    generating a test like `search_similar_examples(limit=5)` raises TypeError is WRONG.
    This test always passes because the function signature was never broken.

    The prompt should explicitly warn against this anti-pattern.
    """

    def test_prompt_warns_against_testing_callee_for_caller_bugs(
        self, step7_prompt_content: str
    ) -> None:
        """
        Verify the prompt explicitly warns against the wrong testing approach.

        The prompt should warn: "Do NOT just test that the function rejects wrong parameters"
        or similar guidance to prevent the LLM from taking the easy path.
        """
        content_lower = step7_prompt_content.lower()

        has_anti_pattern_warning = any([
            "do not" in content_lower and "function rejects" in content_lower,
            "don't" in content_lower and "function rejects" in content_lower,
            "do not test that the callee" in content_lower,
            "don't test that the callee" in content_lower,
            "do not just test" in content_lower and "signature" in content_lower,
            "not the callee" in content_lower,
            "caller behavior" in content_lower and "not" in content_lower and "callee" in content_lower,
        ])

        assert has_anti_pattern_warning, (
            "Step 7 prompt lacks warning against testing callee signature for caller bugs. "
            "The prompt should explicitly state: Do NOT just test that the function rejects "
            "wrong parameters when the bug is in the caller's usage."
        )


class TestStep7PromptEnforcesStep6Strategy:
    """
    Test that the Step 7 prompt enforces implementing Step 6's test strategy.

    Step 6 often correctly identifies the test approach (mock, call_args, etc.),
    but Step 7 may ignore this and generate easier tests. The prompt should
    explicitly require implementing what Step 6 planned.
    """

    def test_prompt_requires_implementing_step6_test_strategy(
        self, step7_prompt_content: str
    ) -> None:
        """
        Verify the prompt instructs implementing Step 6's test STRATEGY, not just file path.

        The current prompt only extracts:
        - "Extract the test file path from Step 6"
        - "If Step 6 said (append)/(new)"

        But it should ALSO require:
        - "Implement EXACTLY what Step 6's test plan described"
        - "If Step 6 provided example test code, use that as the template"
        - "Follow Step 6's testing approach (mocking, assertions, etc.)"

        Without this, LLMs ignore Step 6's test strategy and generate easier tests.
        """
        content_lower = step7_prompt_content.lower()

        # The prompt mentions Step 6 for file path extraction, but does it enforce
        # implementing the actual test STRATEGY from Step 6?
        #
        # We need to check for EXPLICIT phrases that indicate strategy enforcement.
        # The current prompt only says "Extract the test file path from Step 6"
        # It does NOT say "Implement Step 6's test strategy" or similar.
        #
        # Key check: The phrases must be EXPLICIT instructions, not just word presence.
        # The current prompt says "planned the test strategy" (descriptive) but does NOT
        # say "implement the strategy" (imperative).
        has_strategy_enforcement = any([
            # Explicit enforcement phrases - these must be exact substrings
            "implement step 6" in content_lower,
            "implement the strategy" in content_lower and "step 6" in content_lower,
            "implement the test strategy" in content_lower,
            "implement exactly what step 6" in content_lower,
            "follow step 6's strategy" in content_lower,
            "follow step 6's test plan" in content_lower,
            "follow the test strategy" in content_lower and "step 6" in content_lower,
            # Template usage - step 6 example as template
            "step 6" in content_lower and "use as template" in content_lower,
            "step 6" in content_lower and "example code" in content_lower and "template" in content_lower,
            # Enforcement keywords in context of Step 6
            "step 6's approach" in content_lower,
            "step 6's test approach" in content_lower,
        ])

        assert has_strategy_enforcement, (
            "Step 7 prompt only extracts file path from Step 6, not the test STRATEGY. "
            "The prompt should require: 'Implement EXACTLY what Step 6's test plan described' "
            "and 'If Step 6 provided example test code, use that as the template'. "
            "Currently it only says 'Extract the test file path from Step 6'."
        )
