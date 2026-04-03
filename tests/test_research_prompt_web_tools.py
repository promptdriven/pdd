"""
Test Plan for research step prompts (Step 3) across agentic workflows.

Issue: pdd-change (and pdd-arch) Step 3 prompts say "conduct web research" but
never mention the WebSearch or WebFetch tool names. The LLM has access to these
tools (via --dangerously-skip-permissions) but doesn't invoke them because the
prompt doesn't explicitly instruct it to. As a result, the agent hallucinates
answers from training data instead of looking up current information.

Fix: Explicitly instruct the agent to use WebSearch/WebFetch tools in research
step prompts so it actually queries live data (e.g., current model versions,
API docs, library versions) instead of guessing.

Test Categories:
1. TestChangeStep3WebTools: Verify change workflow research prompt references tools
2. TestArchStep3WebTools: Verify architecture workflow research prompt references tools
"""

from pathlib import Path

import pytest


# --- Constants ---

PROMPTS_DIR = Path(__file__).parent.parent / "pdd" / "prompts"

CHANGE_RESEARCH_PROMPT = PROMPTS_DIR / "agentic_change_step3_research_LLM.prompt"
ARCH_RESEARCH_PROMPT = PROMPTS_DIR / "agentic_arch_step3_research_LLM.prompt"
ARCH_DEPS_RESEARCH_PROMPT = PROMPTS_DIR / "agentic_arch_step6_research_deps_LLM.prompt"
BUG_API_RESEARCH_PROMPT = PROMPTS_DIR / "agentic_bug_step4_api_research_LLM.prompt"


# --- Fixtures ---


@pytest.fixture
def change_step3_prompt() -> str:
    """Load the change workflow Step 3 research prompt."""
    assert CHANGE_RESEARCH_PROMPT.exists(), f"Prompt not found: {CHANGE_RESEARCH_PROMPT}"
    return CHANGE_RESEARCH_PROMPT.read_text()


@pytest.fixture
def arch_step3_prompt() -> str:
    """Load the architecture workflow Step 3 research prompt."""
    assert ARCH_RESEARCH_PROMPT.exists(), f"Prompt not found: {ARCH_RESEARCH_PROMPT}"
    return ARCH_RESEARCH_PROMPT.read_text()


@pytest.fixture
def arch_step6_prompt() -> str:
    """Load the architecture workflow Step 6 deps research prompt."""
    assert ARCH_DEPS_RESEARCH_PROMPT.exists(), f"Prompt not found: {ARCH_DEPS_RESEARCH_PROMPT}"
    return ARCH_DEPS_RESEARCH_PROMPT.read_text()


@pytest.fixture
def bug_step4_prompt() -> str:
    """Load the bug workflow Step 4 API research prompt."""
    assert BUG_API_RESEARCH_PROMPT.exists(), f"Prompt not found: {BUG_API_RESEARCH_PROMPT}"
    return BUG_API_RESEARCH_PROMPT.read_text()


# --- Tests: Change Workflow Step 3 ---


class TestChangeStep3WebTools:
    """
    Verify the change workflow research prompt explicitly instructs the agent
    to use WebSearch and/or WebFetch tools for live information lookup.

    Without explicit tool names, the LLM interprets "conduct web research"
    loosely and answers from training data — producing stale or hallucinated
    version numbers, API signatures, and documentation references.
    """

    def test_prompt_mentions_websearch_tool(self, change_step3_prompt: str) -> None:
        """The prompt must reference the WebSearch tool by name."""
        assert "WebSearch" in change_step3_prompt, (
            "Change Step 3 prompt must explicitly mention 'WebSearch' tool "
            "so the agent knows to use it for live lookups"
        )

    def test_prompt_mentions_webfetch_tool(self, change_step3_prompt: str) -> None:
        """The prompt must reference the WebFetch tool for fetching specific URLs."""
        assert "WebFetch" in change_step3_prompt, (
            "Change Step 3 prompt must explicitly mention 'WebFetch' tool "
            "so the agent can fetch specific documentation URLs"
        )

    def test_prompt_instructs_verification_of_versions(self, change_step3_prompt: str) -> None:
        """The prompt must instruct the agent to verify version numbers via web lookup."""
        prompt_lower = change_step3_prompt.lower()
        has_version_check = (
            "verify" in prompt_lower and "version" in prompt_lower
        ) or (
            "look up" in prompt_lower and ("version" in prompt_lower or "latest" in prompt_lower)
        ) or (
            "current" in prompt_lower and "version" in prompt_lower and "websearch" in prompt_lower.replace(" ", "")
        )
        assert has_version_check, (
            "Change Step 3 prompt must instruct the agent to verify version "
            "numbers and model IDs via web search rather than relying on training data"
        )

    def test_prompt_warns_against_training_data(self, change_step3_prompt: str) -> None:
        """The prompt must warn the agent not to rely on training data for volatile info."""
        prompt_lower = change_step3_prompt.lower()
        has_warning = (
            "training data" in prompt_lower
            or "do not guess" in prompt_lower
            or "do not assume" in prompt_lower
            or "may be outdated" in prompt_lower
        )
        assert has_warning, (
            "Change Step 3 prompt must warn the agent that training data "
            "may be outdated for version numbers, model IDs, and API details"
        )


# --- Tests: Architecture Workflow Step 3 ---


class TestArchStep3WebTools:
    """
    Verify the architecture workflow research prompt explicitly instructs
    the agent to use WebSearch and/or WebFetch tools.
    """

    def test_prompt_mentions_websearch_tool(self, arch_step3_prompt: str) -> None:
        """The prompt must reference the WebSearch tool by name."""
        assert "WebSearch" in arch_step3_prompt, (
            "Arch Step 3 prompt must explicitly mention 'WebSearch' tool "
            "so the agent knows to use it for live lookups"
        )

    def test_prompt_mentions_webfetch_tool(self, arch_step3_prompt: str) -> None:
        """The prompt must reference the WebFetch tool for fetching specific URLs."""
        assert "WebFetch" in arch_step3_prompt, (
            "Arch Step 3 prompt must explicitly mention 'WebFetch' tool "
            "so the agent can fetch specific documentation URLs"
        )

    def test_prompt_instructs_verification_of_versions(self, arch_step3_prompt: str) -> None:
        """The prompt must instruct the agent to verify version numbers via web lookup."""
        prompt_lower = arch_step3_prompt.lower()
        has_version_check = (
            "verify" in prompt_lower and "version" in prompt_lower
        ) or (
            "look up" in prompt_lower and ("version" in prompt_lower or "latest" in prompt_lower)
        ) or (
            "current" in prompt_lower and "version" in prompt_lower and "websearch" in prompt_lower.replace(" ", "")
        )
        assert has_version_check, (
            "Arch Step 3 prompt must instruct the agent to verify version "
            "numbers via web search rather than relying on training data"
        )


# --- Tests: Architecture Workflow Step 6 (Deps Research) ---


class TestArchStep6WebTools:
    """Verify the arch Step 6 deps research prompt references WebSearch/WebFetch."""

    def test_prompt_mentions_websearch_tool(self, arch_step6_prompt: str) -> None:
        assert "WebSearch" in arch_step6_prompt

    def test_prompt_mentions_webfetch_tool(self, arch_step6_prompt: str) -> None:
        assert "WebFetch" in arch_step6_prompt


# --- Tests: Bug Workflow Step 4 (API Research) ---


class TestBugStep4WebTools:
    """Verify the bug Step 4 API research prompt references WebSearch/WebFetch."""

    def test_prompt_mentions_websearch_tool(self, bug_step4_prompt: str) -> None:
        assert "WebSearch" in bug_step4_prompt

    def test_prompt_mentions_webfetch_tool(self, bug_step4_prompt: str) -> None:
        assert "WebFetch" in bug_step4_prompt
