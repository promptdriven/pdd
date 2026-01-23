"""
E2E Test for Issue #376: Template injection in step outputs causes KeyError

This E2E test verifies that the agentic change orchestrator can handle step outputs
containing JSON/dictionary content with braces without raising KeyError during
template formatting.

Root Cause Investigation:
After testing, Python's str.format() does NOT re-parse substituted values. The actual
bug pattern (if it exists) would be from literal unescaped braces IN THE TEMPLATE itself,
similar to issue #357.

However, this test still serves as a regression test to ensure step outputs with JSON
content are handled correctly throughout the workflow.
"""

import pytest
from pdd.load_prompt_template import load_prompt_template


class TestIssue376TemplateFormatting:
    """
    E2E tests for Issue #376: Verify orchestrator handles JSON in step outputs.
    """

    def test_step5_template_formats_with_json_in_previous_outputs(self):
        """
        E2E Test: Step 5 template should format successfully even when previous
        step outputs contain JSON with braces.

        This test verifies the behavior described in issue #376, where step outputs
        containing JSON were reported to cause KeyError during template formatting.

        Note: Python's str.format() does NOT re-parse substituted values, so JSON in
        step outputs should not cause issues UNLESS the template itself has literal
        unescaped braces.
        """
        # Context with step outputs containing JSON (as reported in issue #376)
        context = {
            "issue_url": "https://github.com/promptdriven/pdd/issues/376",
            "repo_owner": "promptdriven",
            "repo_name": "pdd",
            "issue_number": 376,
            "issue_content": "Test issue",
            "issue_author": "test",
            "issue_title": "Template injection test",
            "step1_output": "Step 1 complete",
            "step2_output": "Step 2 complete",
            "step3_output": '''Step 3 analysis:
{
  "step_outputs": {
    "1": "Step 1 complete",
    "2": "Step 2 complete"
  },
  "total_cost": 1.27,
  "model_used": "anthropic"
}
Analysis complete.''',
            "step4_output": "Step 4 complete"
        }

        # Load and format step 5 template
        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError
        try:
            formatted = template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"Template formatting failed with KeyError: '{e.args[0]}'\n\n"
                f"This indicates the template has literal unescaped braces that conflict "
                f"with the context keys. Check the template for JSON examples or other "
                f"literal braces that should be escaped as {{{{ }}}}."
            )

        # Verify the template was properly formatted
        assert "promptdriven/pdd" in formatted
        assert "376" in formatted
        # The JSON from step3_output should appear in the formatted output
        assert "Step 3 analysis" in formatted

    def test_all_change_steps_handle_json_outputs(self):
        """
        Regression test: All agentic change workflow steps should handle JSON
        in previous step outputs.
        """
        base_context = {
            "issue_url": "https://github.com/test/repo/issues/1",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 1,
            "issue_content": "Test",
            "issue_author": "test",
            "issue_title": "Test",
        }

        # Test steps 1-5 (testing early workflow steps)
        steps_to_test = [
            (1, "duplicate", []),
            (2, "docs", ["step1_output"]),
            (3, "research", ["step1_output", "step2_output"]),
            (4, "clarify", ["step1_output", "step2_output", "step3_output"]),
            (5, "docs_change", ["step1_output", "step2_output", "step3_output", "step4_output"]),
        ]

        json_output = '{"status": "complete", "data": {"count": 5}}'

        for step_num, step_name, required_outputs in steps_to_test:
            context = base_context.copy()
           
            # Add required previous outputs with JSON content
            for i, output_key in enumerate(required_outputs, 1):
                context[output_key] = f"Step {i}: {json_output}"

            template_name = f"agentic_change_step{step_num}_{step_name}_LLM"
            template = load_prompt_template(template_name)

            if template is None:
                continue  # Skip if template doesn't exist

            try:
                formatted = template.format(**context)
                assert len(formatted) > 0
            except KeyError as e:
                pytest.fail(
                    f"Step {step_num} ({step_name}) failed to format with JSON in outputs.\n"
                    f"KeyError: '{e.args[0]}'\n"
                    f"Template: {template_name}"
                )
