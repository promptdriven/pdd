"""
E2E Test for Issue #9: Template injection in agentic_change workflow

This E2E test verifies that the agentic_change orchestrator can handle step outputs
containing JSON/dictionary content with braces without raising KeyError during template
formatting.

Issue #9 claims that when step outputs contain JSON like {"type": "error"}, the
orchestrator's .format(**context) call at line 521 misinterprets these braces as
template variables, causing KeyError.

However, as discovered in Step 5 of the investigation, Python's .format() does NOT
do "two-pass substitution" - braces in substituted values are treated as literals.

This E2E test:
1. Exercises the full orchestrator code path from step 1 through step 5
2. Injects JSON-containing output in step 3 (simulating workflow state data)
3. Verifies that step 5's template formatting succeeds without KeyError
4. Confirms that the system correctly handles structured data in step outputs

The test should PASS on the current code, confirming the bug report is based on
a misunderstanding of Python's string formatting behavior.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
import json


@pytest.fixture
def mock_cwd(tmp_path):
    """Create a mock working directory with .git to simulate a git repo."""
    (tmp_path / ".git").mkdir()
    (tmp_path / ".pdd").mkdir()
    # Create a minimal .pddrc file
    (tmp_path / ".pddrc").write_text("# Test config")
    return tmp_path


class TestIssue9TemplateInjectionE2E:
    """
    E2E tests for Issue #9: Verify orchestrator handles JSON in step outputs.

    These tests exercise the orchestrator's full workflow with step outputs
    containing JSON/dictionary syntax with braces.
    """

    def test_step5_formats_prompt_with_json_in_step3_output(self, mock_cwd):
        """
        E2E Test: Step 5 should format prompt even when step 3 output contains JSON.

        This test reproduces the exact scenario described in issue #9:
        - Steps 1-4 complete successfully
        - Step 3 output contains JSON workflow state with braces
        - Step 5 attempts to format its template with {step3_output}

        Expected behavior:
        - Prompt formats successfully
        - JSON braces are treated as literal characters, not template variables
        - No KeyError is raised

        Bug behavior (as claimed in issue #9):
        - KeyError: '\n  "type"' when formatting step 5 template
        """
        from pdd.load_prompt_template import load_prompt_template

        # Simulate step outputs from previous steps
        # Step 3 output contains JSON with braces (the claimed bug trigger)
        step3_output_with_json = """
Issue #9 investigation findings:

Workflow state:
{
  "step_outputs": {
    "1": "Duplicate check complete",
    "2": "Documentation review complete",
    "3": "Research findings documented",
    "4": "Requirements clarified"
  },
  "total_cost": 1.2660064,
  "model_used": "anthropic",
  "last_completed_step": 4,
  "github_comment_id": 3786243914
}

The error manifests as: {"type": "KeyError", "message": "Context missing key"}
"""

        # Build context as the orchestrator would for Step 5
        # This mimics agentic_change_orchestrator.py lines 401-413
        context = {
            "issue_url": "https://github.com/Serhan-Asad/pdd/issues/9",
            "issue_content": "Template injection bug report",
            "repo_owner": "Serhan-Asad",
            "repo_name": "pdd",
            "issue_number": 9,
            "issue_author": "test-user",
            "issue_title": "Bug: pdd change fails at step 5 due to template injection",
            "step1_output": "No duplicates found",
            "step2_output": "Feature not yet implemented in docs",
            "step3_output": step3_output_with_json,  # Contains JSON with braces!
            "step4_output": "Requirements are clear, proceeding to implementation",
        }

        # Load the Step 5 template - this is the REAL template, not mocked
        step_num = 5
        template_name = "agentic_change_step5_docs_change_LLM"

        prompt_template = load_prompt_template(template_name)
        assert prompt_template is not None, f"Failed to load template: {template_name}"

        # THE BUG CHECK: This line should NOT raise KeyError: '\n  "type"'
        # Bug location: agentic_change_orchestrator.py:521
        # Bug claim: .format() interprets braces in step3_output as template vars
        try:
            formatted_prompt = prompt_template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"BUG DETECTED (Issue #9): KeyError '{e.args[0]}' raised when formatting "
                f"Step 5 prompt template.\n\n"
                f"This would confirm the bug claim that Python's .format() does two-pass "
                f"substitution. However, this should NOT happen based on Python semantics.\n\n"
                f"Step 3 output contained: {step3_output_with_json[:200]}..."
            )

        # Verify context variables were substituted
        assert "https://github.com/Serhan-Asad/pdd/issues/9" in formatted_prompt, \
            "issue_url should be substituted"
        assert "9" in formatted_prompt, \
            "issue_number should be substituted"

        # Verify step3_output (with its JSON) was inserted as literal text
        assert '"type"' in formatted_prompt or "step_outputs" in formatted_prompt, \
            "Step 3 output's JSON content should appear as literal text in formatted prompt"

    def test_orchestrator_step5_with_dict_syntax_in_step_outputs(self, mock_cwd):
        """
        E2E Test: Orchestrator should handle Python dict repr syntax in step outputs.

        Tests the scenario where step outputs contain dictionary representations
        with braces, simulating what might be captured from debug output or
        error messages.
        """
        from pdd.load_prompt_template import load_prompt_template

        step_outputs_with_dicts = {
            "step1_output": "Analysis complete: {'status': 'no_duplicates', 'count': 0}",
            "step2_output": "Review result: {'implemented': False, 'confidence': 0.95}",
            "step3_output": """
Research findings for Issue #9:

Error details: {"error_type": "KeyError", "key": "\\n  \\"type\\""}
Template vars: {"step1_output": "...", "step2_output": "..."}
Context: {"repo": "pdd", "issue": 9}
""",
            "step4_output": "Clarification: {'ready_to_implement': True, 'blockers': []}",
        }

        context = {
            "issue_url": "https://github.com/test/repo/issues/9",
            "issue_content": "Test issue",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 9,
            "issue_author": "test-author",
            "issue_title": "Test Issue",
            **step_outputs_with_dicts,
        }

        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None

        # This should NOT raise KeyError
        try:
            formatted = template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"BUG DETECTED (Issue #9): KeyError '{e.args[0]}' during formatting.\n"
                f"Step outputs contained dict syntax that was misinterpreted as template vars."
            )

        # Verify dict syntax remains in output
        assert "error_type" in formatted or "status" in formatted, \
            "Dictionary content from step outputs should be preserved"

    def test_orchestrator_step5_with_nested_json_structures(self, mock_cwd):
        """
        E2E Test: Deeply nested JSON in step outputs should not cause KeyError.

        Tests with complex, deeply nested JSON structures to ensure all
        brace levels are handled correctly.
        """
        from pdd.load_prompt_template import load_prompt_template

        nested_json_output = """
Complex workflow state:
{
  "workflow": {
    "steps": [
      {"id": 1, "status": "complete", "data": {"findings": ["a", "b"]}},
      {"id": 2, "status": "complete", "data": {"results": {"key": "value"}}},
      {"id": 3, "status": "complete", "data": {
        "nested": {
          "deeply": {
            "structure": {"type": "analysis", "details": ["x", "y", "z"]}
          }
        }
      }}
    ]
  },
  "metadata": {"timestamp": "2026-01-22", "cost": 1.5}
}
"""

        context = {
            "issue_url": "https://github.com/test/repo/issues/9",
            "issue_content": "Test",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 9,
            "issue_author": "test",
            "issue_title": "Test",
            "step1_output": "Step 1",
            "step2_output": "Step 2",
            "step3_output": nested_json_output,
            "step4_output": "Step 4",
        }

        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None

        try:
            formatted = template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"BUG DETECTED (Issue #9): KeyError '{e.args[0]}' with nested JSON.\n"
                f"Nested structures should be treated as literal text."
            )

        assert "workflow" in formatted or "metadata" in formatted, \
            "Nested JSON should be preserved in formatted output"

    def test_full_orchestrator_integration_with_json_outputs(self, mock_cwd, monkeypatch):
        """
        E2E Integration Test: Run orchestrator through Step 5 with JSON in outputs.

        This test exercises the actual orchestrator code path by:
        1. Calling run_agentic_change_orchestrator with mocked LLM
        2. Making step 3 return output with JSON content
        3. Verifying the orchestrator doesn't crash at Step 5 due to KeyError
        4. Confirming all steps complete successfully

        Note: We mock run_agentic_task to avoid actual LLM calls, but the prompt
        loading and formatting code (where the claimed bug is) is NOT mocked.
        """
        # Set up environment
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Track which steps were attempted
        steps_attempted = []
        step_prompts = {}

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """
            Mock LLM task runner that simulates step completions.

            IMPORTANT: This is called AFTER template formatting, so if there's
            a KeyError in formatting, this mock won't be reached.
            """
            # Extract step number from label
            import re
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_attempted.append(step_num)
                step_prompts[step_num] = instruction

            # Return step-specific outputs
            if "step1" in label:
                return (True, "No duplicate issues found", 0.001, "mock-model")
            elif "step2" in label:
                return (True, "Feature not documented yet", 0.001, "mock-model")
            elif "step3" in label:
                # Step 3 returns JSON-containing output (the bug trigger)
                output = """
Research complete for Issue #9.

Findings include workflow state data:
{
  "investigation": {
    "root_cause": "template_injection_claim",
    "evidence": {"issues": [6, 357], "exists": false},
    "conclusion": "Cannot reproduce"
  },
  "test_results": {"status": "pass", "count": 5}
}

Error patterns observed: {"type": "KeyError", "key": "\\n  \\"type\\""}
"""
                return (True, output, 0.001, "mock-model")
            elif "step4" in label:
                return (True, "Requirements clarified: {'ready': True}", 0.001, "mock-model")
            elif "step5" in label:
                # If we reach step 5, it means formatting succeeded!
                return (True, "Documentation changes identified", 0.001, "mock-model")
            else:
                return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            """Mock state persistence."""
            return None

        def mock_load_state(*args, **kwargs):
            """Mock state loading - return no previous state."""
            return None, None

        # Patch the LLM task runner and state management
        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator._setup_worktree') as mock_worktree:
                        # Mock worktree setup to avoid git operations
                        mock_worktree.return_value = (None, None)

                        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

                        try:
                            success, message, cost, model, files = run_agentic_change_orchestrator(
                                issue_url="https://github.com/Serhan-Asad/pdd/issues/9",
                                issue_content="Template injection bug test",
                                repo_owner="Serhan-Asad",
                                repo_name="pdd",
                                issue_number=9,
                                issue_author="test-user",
                                issue_title="Issue 9 Template Injection Test",
                                cwd=mock_cwd,
                                verbose=False,
                                quiet=True,
                                use_github_state=False,
                            )
                        except KeyError as e:
                            pytest.fail(
                                f"BUG DETECTED (Issue #9): Orchestrator raised KeyError '{e.args[0]}' "
                                f"during template formatting.\n\n"
                                f"Steps completed before crash: {steps_attempted}\n\n"
                                f"This would confirm that JSON in step outputs causes template injection.\n"
                                f"However, this should NOT happen based on Python's .format() behavior."
                            )

        # Verify all steps 1-5 were attempted
        assert 1 in steps_attempted, "Step 1 should be attempted"
        assert 2 in steps_attempted, "Step 2 should be attempted"
        assert 3 in steps_attempted, "Step 3 should be attempted"
        assert 4 in steps_attempted, "Step 4 should be attempted"
        assert 5 in steps_attempted, (
            f"Step 5 should be attempted. Steps attempted: {steps_attempted}\n"
            f"If Step 5 wasn't reached, template formatting may have failed."
        )

        # Verify step 3's JSON output was included in step 5's prompt
        if 5 in step_prompts:
            step5_prompt = step_prompts[5]
            assert "investigation" in step5_prompt or "test_results" in step5_prompt, \
                "Step 5 prompt should contain step 3's JSON output as literal text"


class TestIssue9RegressionPrevention:
    """
    Regression prevention tests for Issue #9.

    These tests verify that the system correctly handles braces in step outputs
    and prevent future regressions.
    """

    def test_context_building_preserves_braces_in_step_outputs(self):
        """
        Regression Test: Context building should preserve braces in step outputs.

        This test verifies that when step outputs are added to the context dict,
        their content (including braces) is preserved as-is and not pre-processed
        or escaped.
        """
        # Simulate the context building code from lines 412-413
        step_outputs = {
            "1": "Step 1: {'result': 'success'}",
            "2": "Step 2: {\"data\": [1, 2, 3]}",
            "3": """{"workflow": {"status": "ok"}}""",
        }

        context = {}
        for s_num, s_out in step_outputs.items():
            context[f"step{s_num}_output"] = s_out

        # Verify braces are preserved
        assert "{" in context["step1_output"]
        assert "}" in context["step2_output"]
        assert '"workflow"' in context["step3_output"]

        # Verify these can be used in string formatting without error
        test_template = "Previous steps: {step1_output}, {step2_output}, {step3_output}"

        try:
            formatted = test_template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"KeyError '{e.args[0]}' when formatting with step outputs containing braces.\n"
                f"This indicates Python is misinterpreting braces in substituted values."
            )

        # Verify all step outputs appear in formatted string
        assert "result" in formatted
        assert "data" in formatted
        assert "workflow" in formatted

    def test_format_does_not_do_two_pass_substitution(self):
        """
        Unit Test: Verify Python's .format() behavior with braces in values.

        This test documents Python's actual behavior: .format() does NOT
        interpret braces in substituted values as new template variables.

        This is the core misunderstanding in Issue #9's root cause analysis.
        """
        # Simulate exactly what the orchestrator does
        step3_output = '{"type": "error", "key": "\\n  \\"type\\""}'
        context = {"step3_output": step3_output}
        template = "Step 3 result: {step3_output}"

        # This should NOT raise KeyError
        formatted = template.format(**context)

        # Verify the JSON appears as literal text
        assert '{"type": "error"' in formatted
        assert step3_output in formatted

        # Verify Python did NOT try to interpret {"type": ...} as a template variable
        # If it did, we'd get KeyError: 'type'
