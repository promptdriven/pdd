"""
Tests for Issue #902 prompt sync and source-of-truth fix.

Two problems:
1. The agentic_common prompt is missing features that exist in the code
   (detect_control_token, classify_step_output, progress tracking, etc.)
2. The Step 3 root cause prompt doesn't consult the .prompt file as source
   of truth, so pdd-fix can't tell if code or tests are wrong — leading it
   to weaken tests instead of fixing code.
"""

from pathlib import Path

import pytest


PROMPTS_DIR = Path(__file__).parent.parent / "pdd" / "prompts"


# ---------------------------------------------------------------------------
# Part 1: agentic_common prompt must specify features that exist in the code
# ---------------------------------------------------------------------------


class TestAgenticCommonPromptSync:
    """The agentic_common prompt must specify key features from the code."""

    @pytest.fixture
    def prompt_content(self) -> str:
        path = PROMPTS_DIR / "agentic_common_python.prompt"
        assert path.exists(), f"Prompt not found: {path}"
        return path.read_text()

    def test_prompt_specifies_detect_control_token(self, prompt_content: str) -> None:
        """detect_control_token is the 4-tier token detection system added in #863."""
        assert "detect_control_token" in prompt_content, (
            "Prompt must specify detect_control_token — the 4-tier control token "
            "detection system (exact → case-insensitive → semantic regex → LLM)"
        )

    def test_prompt_specifies_classify_step_output(self, prompt_content: str) -> None:
        """classify_step_output is the tier-4 LLM classification fallback."""
        assert "classify_step_output" in prompt_content, (
            "Prompt must specify classify_step_output — the tier-4 LLM "
            "classification fallback for control tokens"
        )

    def test_prompt_specifies_semantic_patterns(self, prompt_content: str) -> None:
        """SEMANTIC_PATTERNS drives tier-3 regex matching."""
        assert "SEMANTIC_PATTERNS" in prompt_content, (
            "Prompt must specify SEMANTIC_PATTERNS — the regex patterns for "
            "tier-3 semantic control token detection"
        )

    def test_prompt_specifies_exponential_backoff_formula(self, prompt_content: str) -> None:
        """The prompt must specify the actual exponential formula, not just say 'exponential'."""
        assert "2 **" in prompt_content or "2^" in prompt_content, (
            "Prompt must specify the exponential backoff formula "
            "(e.g., retry_delay * 2^(attempt-1)), not just say 'exponential backoff'"
        )

    def test_prompt_specifies_jitter(self, prompt_content: str) -> None:
        """Backoff must include jitter to prevent thundering herd."""
        assert "jitter" in prompt_content.lower(), (
            "Prompt must specify jitter in the backoff formula "
            "to prevent thundering herd when concurrent jobs retry"
        )

    def test_prompt_specifies_error_classification(self, prompt_content: str) -> None:
        """Prompt must specify error classification for permanent vs transient errors."""
        has_error_class = (
            "permanent" in prompt_content.lower()
            or "transient" in prompt_content.lower()
            or "error classification" in prompt_content.lower()
        )
        assert has_error_class, (
            "Prompt must specify error classification — permanent errors "
            "(auth, invalid parameter) should fail fast, transient errors "
            "(rate limit, 5xx) should retry"
        )

    def test_prompt_specifies_aggregate_timeout(self, prompt_content: str) -> None:
        """Prompt must specify aggregate timeout across all providers."""
        has_aggregate = (
            "aggregate" in prompt_content.lower()
            or "total timeout" in prompt_content.lower()
            or "per-step timeout" in prompt_content.lower()
        )
        assert has_aggregate, (
            "Prompt must specify an aggregate timeout across all providers "
            "to prevent worst-case 9x timeout cascade"
        )

    def test_prompt_specifies_progress_tracking(self, prompt_content: str) -> None:
        """set_agentic_progress/clear_agentic_progress for Ctrl+C UX."""
        assert "set_agentic_progress" in prompt_content, (
            "Prompt must specify set_agentic_progress for Ctrl+C UX "
            "(added in commit 70a58d043)"
        )

    def test_prompt_specifies_post_final_comment(self, prompt_content: str) -> None:
        """post_final_comment for posting workflow summary."""
        assert "post_final_comment" in prompt_content, (
            "Prompt must specify post_final_comment for posting workflow "
            "summary comments to GitHub issues"
        )

    def test_prompt_specifies_substitute_template_variables(self, prompt_content: str) -> None:
        """substitute_template_variables for safe prompt formatting."""
        assert "substitute_template_variables" in prompt_content, (
            "Prompt must specify substitute_template_variables for safe "
            "template variable substitution"
        )


# ---------------------------------------------------------------------------
# Part 2: Step 3 must consult the .prompt file as source of truth
# ---------------------------------------------------------------------------


class TestStep3PromptSourceOfTruth:
    """Step 3 root cause prompt must use .prompt files as authoritative spec."""

    @pytest.fixture
    def step3_content(self) -> str:
        path = PROMPTS_DIR / "agentic_e2e_fix_step3_root_cause_LLM.prompt"
        assert path.exists(), f"Step 3 prompt not found: {path}"
        return path.read_text()

    def test_step3_references_prompt_as_source_of_truth(self, step3_content: str) -> None:
        """Step 3 must tell the LLM to read the .prompt file as authoritative spec."""
        has_prompt_ref = (
            "source of truth" in step3_content.lower()
            or "prompt file" in step3_content.lower()
            or ".prompt" in step3_content
            or "authoritative spec" in step3_content.lower()
        )
        assert has_prompt_ref, (
            "Step 3 prompt must reference the .prompt file as the authoritative "
            "specification. Without this, the LLM can't distinguish CODE_BUG "
            "(code disagrees with prompt) from TEST_BUG (test disagrees with prompt). "
            "This caused pdd-fix to weaken tests on #902 instead of fixing code."
        )

    def test_step3_prompt_trumps_code(self, step3_content: str) -> None:
        """Step 3 must explicitly state that prompt > code when they disagree."""
        content_lower = step3_content.lower()
        has_priority = (
            "code disagrees with the prompt" in content_lower
            or "prompt takes precedence" in content_lower
            or "code is a generated artifact" in content_lower
            or "prompt is the spec" in content_lower
            or "prompt overrides" in content_lower
        )
        assert has_priority, (
            "Step 3 must state that when code and prompt disagree, the prompt "
            "is authoritative and the code is wrong (CODE_BUG). On #902, the "
            "prompt said 'exponential backoff' but the code did linear — Step 3 "
            "should have classified this as CODE_BUG, not TEST_BUG."
        )
