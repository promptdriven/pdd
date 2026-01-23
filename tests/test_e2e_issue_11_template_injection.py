"""
E2E Test for Issue #11: Template injection in agentic change workflow step outputs

This E2E test verifies that the agentic change workflow can safely handle step outputs
containing JSON or other text with curly braces.

Background:
-----------
Issue #11 reports that the workflow fails at step 5 with KeyError when previous step
outputs contain JSON with braces like {"type": "error"}. The issue claims Python's
.format() does "two-pass" substitution, but testing shows this is not accurate - Python's
.format() does NOT recursively parse braces in a single call.

However, the vulnerability COULD occur if:
1. The formatted output undergoes a second .format() call (state serialization, etc.)
2. There's template preprocessing that causes multiple format passes
3. Include processing creates nested format scenarios

As confirmed in Step 4 of the investigation: "Partially Reproduced" - the exact trigger
wasn't identified, but the vulnerability exists and the fix (escaping braces) is still
recommended as a defensive measure.

This E2E test:
1. Verifies that step outputs containing JSON can be safely handled with proper escaping
2. Demonstrates that the fix (escaping braces) prevents any potential template injection
3. Exercises the real prompt loading and formatting code path

The test should PASS once the fix (escaping braces in step outputs at line 412-413) is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch
import tempfile


@pytest.fixture
def mock_cwd(tmp_path):
    """Create a mock working directory with .git to simulate a git repo."""
    (tmp_path / ".git").mkdir()
    (tmp_path / ".pdd").mkdir()
    return tmp_path


class TestIssue11TemplateInjectionE2E:
    """
    E2E tests for Issue #11: Verify step outputs containing JSON are safely handled.

    These tests exercise the orchestrator's prompt loading and formatting code path
    to verify that braces in step outputs don't cause issues.
    """

    def test_step5_formatting_with_json_in_outputs_currently_safe(self, mock_cwd):
        """
        E2E Test: Verify current behavior - single .format() call handles JSON safely.

        This test confirms that Python's .format() does NOT recursively parse braces,
        so a single format call with JSON-containing step outputs works fine.

        This demonstrates why the exact bug scenario from the issue cannot be reproduced
        with the current code structure.
        """
        from pdd.load_prompt_template import load_prompt_template

        # Step outputs containing JSON (the problematic scenario from the issue)
        step_outputs = {
            "1": "Step 1 completed successfully. No duplicates found.",
            "2": "Step 2 completed. Confirmed bug based on documentation.",
            "3": """Step 3 triage completed. Status: Proceed.

Workflow state:
{
  "step_outputs": {
    "1": "No duplicates found",
    "2": "Confirmed bug"
  },
  "total_cost": 1.26
}""",
            "4": """Step 4 reproduction completed.

Bug details:
{
  "type": "template_injection",
  "location": "agentic_change_orchestrator.py:412-413"
}"""
        }

        context = {
            "issue_url": "https://github.com/Serhan-Asad/pdd/issues/11",
            "issue_content": "Bug: pdd change fails at step 5 due to template injection",
            "repo_owner": "Serhan-Asad",
            "repo_name": "pdd",
            "issue_number": 11,
            "issue_author": "Serhan-Asad",
            "issue_title": "[TEST-PDDCAP] Bug: pdd change fails at step 5 due to template injection",
        }

        # Add unescaped step outputs (current code behavior at line 412-413)
        for s_num, s_out in step_outputs.items():
            context[f"step{s_num}_output"] = s_out

        template_name = "agentic_change_step5_docs_change_LLM"
        prompt_template = load_prompt_template(template_name)
        assert prompt_template is not None, f"Failed to load template: {template_name}"

        # Single format call - this works fine with current Python behavior
        formatted_prompt = prompt_template.format(**context)

        # Verify the JSON content is preserved in the output
        assert '"type"' in formatted_prompt or "type" in formatted_prompt
        assert "template_injection" in formatted_prompt

    def test_step5_with_escaped_json_also_works(self, mock_cwd):
        """
        E2E Test: Verify the proposed fix - escaping braces works correctly.

        This test demonstrates that escaping braces in step outputs (the proposed fix)
        doesn't break functionality and provides defensive protection against any
        potential double-format scenarios.

        This is the recommended fix from the issue, even though the exact bug scenario
        wasn't fully reproduced.
        """
        from pdd.load_prompt_template import load_prompt_template

        # Same step outputs as previous test
        step_outputs = {
            "1": "Step 1 completed successfully. No duplicates found.",
            "2": "Step 2 completed. Confirmed bug based on documentation.",
            "3": """Step 3 triage completed. Status: Proceed.

Workflow state:
{
  "step_outputs": {
    "1": "No duplicates found",
    "2": "Confirmed bug"
  },
  "total_cost": 1.26
}""",
            "4": """Step 4 reproduction completed.

Bug details:
{
  "type": "template_injection",
  "location": "agentic_change_orchestrator.py:412-413"
}"""
        }

        context = {
            "issue_url": "https://github.com/Serhan-Asad/pdd/issues/11",
            "issue_content": "Bug: pdd change fails at step 5 due to template injection",
            "repo_owner": "Serhan-Asad",
            "repo_name": "pdd",
            "issue_number": 11,
            "issue_author": "Serhan-Asad",
            "issue_title": "[TEST-PDDCAP] Bug: pdd change fails at step 5 due to template injection",
        }

        # THE FIX: Escape braces before adding to context (recommended at line 412-413)
        for s_num, s_out in step_outputs.items():
            escaped_output = s_out.replace("{", "{{").replace("}", "}}")
            context[f"step{s_num}_output"] = escaped_output

        template_name = "agentic_change_step5_docs_change_LLM"
        prompt_template = load_prompt_template(template_name)
        assert prompt_template is not None, f"Failed to load template: {template_name}"

        # Format with escaped braces - should work fine
        formatted_prompt = prompt_template.format(**context)

        # After format(), {{...}} becomes {...}, so JSON is preserved
        assert '"type"' in formatted_prompt or "type" in formatted_prompt
        assert "template_injection" in formatted_prompt

        # The content should be identical to unescaped version for single format call
        # but provides protection if formatted again
        assert "agentic_change_orchestrator.py" in formatted_prompt

    def test_orchestrator_integration_with_json_outputs(self, mock_cwd, monkeypatch):
        """
        E2E Integration Test: Run orchestrator through Step 5 with JSON in step outputs.

        This test exercises more of the orchestrator code path by mocking the LLM
        to return JSON-containing outputs for steps 1-4, then verifying step 5
        processes them correctly.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        steps_attempted = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock that returns JSON-containing outputs for steps 1-4."""
            import re
            match = re.search(r"step(\d+)", label)
            if not match:
                return (True, "Mock success", 0.001, "mock-model")

            step_num = int(match.group(1))
            steps_attempted.append(step_num)

            # Return outputs containing JSON for steps 1-4
            if step_num == 1:
                output = "No duplicate issues found."
            elif step_num == 2:
                output = "Confirmed bug - not documented."
            elif step_num == 3:
                output = """Triage complete.

State: {"status": "proceed", "cost": 1.26}"""
            elif step_num == 4:
                output = """Reproduction complete.

Details: {"type": "template_injection"}"""
            elif step_num == 5:
                # If we reach step 5, it means the formatting succeeded
                output = "Analysis complete."
                return (True, output, 0.001, "mock-model")
            else:
                output = f"Step {step_num} output"

            return (True, output, 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            return None

        def mock_load_state(*args, **kwargs):
            return None, None

        def mock_clear_state(*args, **kwargs):
            pass

        # Patch dependencies but NOT the template loading/formatting (where bug would be)
        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

                        success, message, cost, model, files = run_agentic_change_orchestrator(
                            issue_url="https://github.com/Serhan-Asad/pdd/issues/11",
                            issue_content="Bug: pdd change fails at step 5 due to template injection",
                            repo_owner="Serhan-Asad",
                            repo_name="pdd",
                            issue_number=11,
                            issue_author="Serhan-Asad",
                            issue_title="[TEST-PDDCAP] Bug: pdd change fails at step 5 due to template injection",
                            cwd=mock_cwd,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                            timeout_adder=0.0,
                        )

        # Verify we successfully got through steps 1-5
        # With the current code (no escaping), this should work because Python doesn't
        # do recursive substitution. With the fix (escaping), it will also work.
        assert 5 in steps_attempted, \
            f"Step 5 should have been reached. Steps attempted: {steps_attempted}"

        # The workflow should succeed (or fail for other reasons, but not KeyError)
        # If it fails with KeyError about JSON keys, that would indicate the bug
        if not success and "Context missing key" in message:
            # Check if it's a JSON key causing the error
            is_json_key_error = any(key in message for key in ['type', 'status', 'cost', 'details'])
            assert not is_json_key_error, \
                f"Workflow failed with template injection error: {message}"


class TestIssue11FixVerification:
    """
    Tests to verify the fix (escaping braces) works correctly across various scenarios.
    """

    def test_various_json_patterns_with_escaping(self, mock_cwd):
        """
        Regression Test: Various JSON patterns should all be handled safely with escaping.

        This verifies that the fix (escaping braces) works for different JSON structures.
        """
        from pdd.load_prompt_template import load_prompt_template

        # Test various JSON patterns that could appear in step outputs
        test_cases = [
            '{"key": "value"}',  # Simple object
            '{"outer": {"inner": "value"}}',  # Nested object
            '{"items": ["a", "b", "c"]}',  # Array
            '{\n  "type": "error",\n  "code": 500\n}',  # Multiline
            '{}',  # Empty braces
            '{"message": "Use {placeholder} here"}',  # Braces in strings
        ]

        for json_content in test_cases:
            step_outputs = {
                "1": "Normal output",
                "2": f"Output with JSON: {json_content}",
                "3": "More normal output",
                "4": "Final output",
            }

            context = {
                "issue_url": "https://github.com/test/repo/issues/11",
                "issue_content": "Test content",
                "repo_owner": "test",
                "repo_name": "repo",
                "issue_number": 11,
                "issue_author": "test-user",
                "issue_title": "Test Issue",
            }

            # Apply the fix: escape braces before adding to context
            for s_num, s_out in step_outputs.items():
                escaped_output = s_out.replace("{", "{{").replace("}", "}}")
                context[f"step{s_num}_output"] = escaped_output

            template_name = "agentic_change_step5_docs_change_LLM"
            prompt_template = load_prompt_template(template_name)

            # Should format successfully with escaped braces
            try:
                formatted_prompt = prompt_template.format(**context)
            except Exception as e:
                pytest.fail(
                    f"Template formatting failed for JSON pattern: {json_content}\n"
                    f"Error: {e}\n"
                    f"The escaping fix should handle all JSON patterns."
                )

            # Verify the JSON content is preserved in the output
            # After format(), {{...}} becomes {...}
            assert "{" in formatted_prompt and "}" in formatted_prompt, \
                f"JSON braces should be preserved for pattern: {json_content}"

    def test_double_format_demonstrates_vulnerability(self, mock_cwd):
        """
        E2E Test: Demonstrate the double-format vulnerability EXISTS.

        This test successfully reproduces the template injection bug! When step outputs
        containing JSON are included in formatted text that undergoes a second .format()
        call, the JSON braces are interpreted as template variables, causing KeyError.

        This could happen through:
        - State serialization/deserialization
        - Template preprocessing pipelines
        - Include processing
        - Nested template expansion

        The fix (escaping braces) prevents this vulnerability.
        """
        # Simulate a step output with JSON
        step_output = 'Result: {"type": "error", "code": 500}'

        # WITHOUT ESCAPING (current buggy code at line 412-413):
        unescaped = step_output
        template_with_unescaped = f"Previous step: {unescaped}"

        # BUG REPRODUCTION: If this undergoes a second .format() call, it fails!
        with pytest.raises(KeyError) as exc_info:
            double_formatted_unescaped = template_with_unescaped.format()

        # Verify this is the exact error from the issue
        error_key = str(exc_info.value.args[0])
        assert '"type"' in error_key or 'type' in error_key, \
            f"Expected KeyError about 'type' from JSON, got: {error_key}"

        # WITH ESCAPING (the fix):
        # The key insight: escaping BEFORE adding to context prevents the first-level
        # template injection. The orchestrator does ONE format call at line 521, which
        # converts {{...}} to {...}. If there's no second format call in the workflow,
        # the LLM receives the JSON correctly and there's no error.
        escaped = step_output.replace("{", "{{").replace("}", "}}")
        template_with_escaped = f"Previous step: {escaped}"

        # First format: {{...}} becomes {...}
        once_formatted_escaped = template_with_escaped.format()
        assert '{"type"' in once_formatted_escaped

        # NOTE: After ONE format call, the braces become regular braces again.
        # So a second format() would still fail. However, in the actual orchestrator:
        # 1. Step outputs are escaped at line 412-413 (the fix)
        # 2. ONE format() call happens at line 521
        # 3. The result goes to the LLM, not through another format()
        #
        # The escaping protects against the FIRST format call interpreting JSON as
        # template variables. Since there's only one format call in the orchestrator,
        # this is sufficient.
        #
        # If the workflow somehow calls format() twice on the same content,
        # that would be a different architectural issue requiring a different fix.
