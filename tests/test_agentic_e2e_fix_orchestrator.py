"""Tests for agentic_e2e_fix_orchestrator prompt formatting.

These tests verify that all e2e fix workflow prompts can be formatted
with the context variables provided by the orchestrator, without
raising KeyError on undefined placeholders.
"""
import pytest
from pdd.load_prompt_template import load_prompt_template


class TestPromptFormatting:
    """Test that all e2e fix prompts can be formatted with orchestrator context."""

    @pytest.fixture
    def base_context(self):
        """Minimal context provided by orchestrator for Step 1."""
        return {
            "issue_url": "https://github.com/test/repo/issues/1",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 1,
            "cycle_number": 1,
            "max_cycles": 5,
            "issue_content": "Test issue content",
        }

    def test_step1_prompt_formats_without_error(self, base_context):
        """Step 1 template should format successfully with orchestrator context.

        Reproduces bug: Template has {test_files}, {dev_unit}, {N}, etc.
        that are not provided in the orchestrator context.
        """
        template = load_prompt_template("agentic_e2e_fix_step1_unit_tests_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError
        formatted = template.format(**base_context)
        assert "pytest" in formatted
        assert "{issue_url}" not in formatted  # Should be substituted
        assert "{dev_unit}" in formatted  # Should remain as example literal

    def test_step2_prompt_formats_without_error(self, base_context):
        """Step 2 template should format successfully with orchestrator context.

        Reproduces bug: Template has {e2e_test_files}, {test_file}, {N}, etc.
        that are not provided in the orchestrator context.
        """
        base_context["step1_output"] = "Step 1 output"
        template = load_prompt_template("agentic_e2e_fix_step2_e2e_tests_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError
        formatted = template.format(**base_context)
        assert "pytest" in formatted
        assert "{test_file}" in formatted  # Should remain as example literal

    def test_step3_prompt_formats_without_error(self, base_context):
        """Step 3 template should format successfully with orchestrator context.

        Regression test for issue #338: Template had {test_name}, {description},
        {detailed_explanation} that were not escaped with double braces.
        """
        base_context["step1_output"] = "Step 1 output"
        base_context["step2_output"] = "Step 2 output"
        template = load_prompt_template("agentic_e2e_fix_step3_root_cause_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError (was the bug in issue #338)
        formatted = template.format(**base_context)
        assert "{test_name}" in formatted  # Should remain as example literal
        assert "{description}" in formatted  # Should remain as example literal
        assert "{detailed_explanation}" in formatted  # Should remain as example literal

    def test_step7_prompt_formats_without_error(self, base_context):
        """Step 7 template should format successfully with orchestrator context.

        Reproduces bug: Template has {test_files}, {name}, {N}, etc.
        that are not provided in the orchestrator context.
        """
        for i in range(1, 7):
            base_context[f"step{i}_output"] = f"Step {i} output"
        template = load_prompt_template("agentic_e2e_fix_step7_verify_tests_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError
        formatted = template.format(**base_context)
        assert "pytest" in formatted
        assert "{name}" in formatted  # Should remain as example literal
