"""
Test that LLM prompts contain guidance for distinguishing mock configuration
errors from production code errors.

These are STATIC tests that check prompt file content, not LLM behavior.
The integration test validates actual LLM behavior.

TDD Workflow:
- These tests should FAIL before prompt updates (RED)
- These tests should PASS after prompt updates (GREEN)
"""

import pytest
import os

# Path relative to pdd root
PROMPTS_DIR = os.path.join(os.path.dirname(__file__), '..', 'prompts')


class TestFixVerificationErrorsPrompt:
    """Tests for fix_verification_errors_LLM.prompt content."""

    @pytest.fixture
    def prompt_content(self):
        prompt_path = os.path.join(PROMPTS_DIR, 'fix_verification_errors_LLM.prompt')
        with open(prompt_path, 'r') as f:
            return f.read()

    def test_contains_mock_guidance_section(self, prompt_content):
        """Prompt must have a dedicated mock vs production section."""
        assert 'MOCK VS PRODUCTION CODE GUIDANCE' in prompt_content, \
            "Missing 'MOCK VS PRODUCTION CODE GUIDANCE' section"

    def test_mentions_magicmock(self, prompt_content):
        """Prompt must mention MagicMock for mock identification."""
        assert 'MagicMock' in prompt_content or 'unittest.mock' in prompt_content, \
            "Prompt should mention MagicMock or unittest.mock"

    def test_mentions_getitem_pattern(self, prompt_content):
        """Prompt must mention __getitem__ mock pattern."""
        assert '__getitem__' in prompt_content, \
            "Prompt should mention __getitem__ mock pattern"

    def test_prioritizes_mock_fixes(self, prompt_content):
        """Prompt must instruct to check mocks BEFORE production code."""
        # Check that mock checking comes before production code changes
        assert 'FIRST check' in prompt_content or 'First:' in prompt_content, \
            "Prompt should instruct to check mocks FIRST"


class TestFindVerificationErrorsPrompt:
    """Tests for find_verification_errors_LLM.prompt content."""

    @pytest.fixture
    def prompt_content(self):
        prompt_path = os.path.join(PROMPTS_DIR, 'find_verification_errors_LLM.prompt')
        with open(prompt_path, 'r') as f:
            return f.read()

    def test_has_mock_identification_step(self, prompt_content):
        """Prompt must have step for identifying mock errors."""
        # Check for mock-related guidance
        has_mock_guidance = (
            'mock' in prompt_content.lower() and
            ('configuration' in prompt_content.lower() or 'setup' in prompt_content.lower())
        )
        assert has_mock_guidance, \
            "Prompt should have guidance for identifying mock configuration errors"
