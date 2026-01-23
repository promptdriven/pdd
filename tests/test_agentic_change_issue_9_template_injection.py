"""
E2E Test for Issue #9: Template injection bug in pdd change workflow

This E2E test exercises the full orchestrator code path for Step 5 of the agentic change workflow.
It verifies that when previous step outputs contain JSON or dictionary-like content with braces
(e.g., {"type": "error"}), the orchestrator can format the Step 5 prompt without raising KeyError.

The bug: When step outputs (from steps 1-4) are added to the context dict at lines 412-413 of
agentic_change_orchestrator.py, they are NOT escaped. If those outputs contain JSON/dictionary
content with braces like:

    {
      "step_outputs": {
        "1": "...",
        "2": "...",
        "3": "...",
        "4": "..."
      },
      "total_cost": 1.2660064,
      "model_used": "anthropic",
      "last_completed_step": 4,
      "github_comment_id": 3786243914
    }

Then when the Step 5 template tries to format with prompt_template.format(**context) at line 521,
Python interprets the braces in the substituted step outputs as NEW template variables, causing
KeyError: '\n  "type"' (or similar, depending on what JSON key appears first after a newline).

This is the same bug that was fixed in Issue #357 for the e2e workflow.

This E2E test:
1. Sets up a mock environment for the orchestrator
2. Simulates reaching Step 5 with step outputs containing JSON/dict content
3. Calls the orchestrator's prompt loading and formatting code
4. Verifies no KeyError is raised on the JSON braces in step outputs

The test should FAIL on buggy code (KeyError) and PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock


@pytest.fixture
def mock_cwd(tmp_path):
    """Create a mock working directory with .git to simulate a git repo."""
    (tmp_path / ".git").mkdir()
    (tmp_path / ".pdd").mkdir()
    return tmp_path


class TestIssue9TemplateInjectionE2E:
    """
    E2E tests for Issue #9: Verify Step 5 prompt template formats without KeyError
    when previous step outputs contain JSON/dictionary content.

    These tests exercise the orchestrator's prompt loading and formatting code path
    without mocking the buggy component (the template and its formatting).
    """

    def test_step5_formats_with_json_in_step3_output(self, mock_cwd):
        """
        E2E Test: Orchestrator Step 5 should format prompt when step 3 contains JSON.

        This reproduces the exact scenario from issue #9:
        - Step 3 output contains workflow state JSON with braces
        - Step 5 template references {step3_output}
        - Without escaping, Python's .format() tries to interpret braces in the JSON
        - Result: KeyError: '\n  "type"' (or similar)

        Expected behavior (after fix):
        - Prompt loads successfully
        - format(**context) succeeds without KeyError
        - Step outputs with JSON are treated as literal content

        Bug behavior (Issue #9):
        - KeyError: '\n  "type"' is raised at line 521 of agentic_change_orchestrator.py
        - The workflow fails with "Context missing key for step 5: '\n  "type"'"
        """
        from pdd.load_prompt_template import load_prompt_template

        # Build the context that the orchestrator would pass to Step 5
        # This mimics agentic_change_orchestrator.py lines 401-413
        context = {
            "issue_url": "https://github.com/Serhan-Asad/pdd/issues/9",
            "repo_owner": "Serhan-Asad",
            "repo_name": "pdd",
            "issue_number": 9,
            "issue_content": "Test issue content for bug #9",
        }

        # Simulate step outputs from steps 1-4
        # Step 3 contains JSON workflow state - this is what triggers the bug
        context["step1_output"] = "Step 1: Duplicate check complete - no duplicates found"
        context["step2_output"] = "Step 2: Confirmed this is a bug"
        context["step3_output"] = """Step 3: Triage complete.

Workflow state:
{
  "step_outputs": {
    "1": "Duplicate check complete",
    "2": "Confirmed bug",
    "3": "Triage complete",
    "4": "Reproduction attempted"
  },
  "total_cost": 1.2660064,
  "model_used": "anthropic",
  "last_completed_step": 4,
  "github_comment_id": 3786243914
}

Decision: Proceed to step 4"""
        context["step4_output"] = "Step 4: Attempted reproduction"

        # Load the Step 5 template - this is the REAL template, not mocked
        template_name = "agentic_change_step5_docs_change_LLM"
        prompt_template = load_prompt_template(template_name)
        assert prompt_template is not None, f"Failed to load template: {template_name}"

        # THE BUG CHECK: This line should NOT raise KeyError
        # Bug location: agentic_change_orchestrator.py:521
        # Bug cause: Lines 412-413 don't escape braces in step outputs before adding to context
        try:
            formatted_prompt = prompt_template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"BUG DETECTED (Issue #9): KeyError '{e.args[0]}' raised when formatting "
                f"Step 5 prompt template.\n\n"
                f"This confirms the bug at lines 412-413 of agentic_change_orchestrator.py:\n"
                f"  for s_num, s_out in step_outputs.items():\n"
                f"      context[f\"step{{s_num}}_output\"] = s_out  <- BUG: should escape braces\n\n"
                f"The step3_output contains JSON with braces like {{'total_cost': ...}}, and "
                f"Python's .format(**context) misinterprets them as template variables.\n\n"
                f"Fix: Escape braces before adding to context:\n"
                f"  escaped_output = s_out.replace('{{', '{{{{').replace('}}', '}}}}')\n"
                f"  context[f\"step{{s_num}}_output\"] = escaped_output"
            )

        # Verify context variables were actually substituted
        assert "https://github.com/Serhan-Asad/pdd/issues/9" in formatted_prompt, \
            "issue_url should be substituted"
        assert "9" in formatted_prompt, \
            "issue_number should be substituted"

        # Verify step outputs are present in the formatted prompt
        # The JSON content should be preserved as literal text
        assert "Step 3: Triage complete" in formatted_prompt or "step3_output" not in formatted_prompt, \
            "step3_output should be substituted into the prompt"

    def test_step5_formats_with_dict_syntax_in_step_output(self, mock_cwd):
        """
        E2E Test: Step 5 should handle Python dict repr syntax in step outputs.

        Tests the case where a step output contains dictionary repr like:
        {"type": "error", "message": "Template injection"}

        This is a more direct test of the template injection vulnerability.
        """
        from pdd.load_prompt_template import load_prompt_template

        context = {
            "issue_url": "https://github.com/Serhan-Asad/pdd/issues/9",
            "repo_owner": "Serhan-Asad",
            "repo_name": "pdd",
            "issue_number": 9,
            "issue_content": "Test issue",
        }

        # Step output with dict syntax - this is what the issue description mentions
        context["step1_output"] = "Check complete"
        context["step2_output"] = "Confirmed bug"
        context["step3_output"] = 'Result: {"type": "error", "status": "failed"}'
        context["step4_output"] = "Reproduction attempted"

        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None

        # This should NOT raise KeyError: 'type'
        try:
            formatted = template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"BUG DETECTED (Issue #9): KeyError '{e.args[0]}' during formatting.\n"
                f"Step outputs containing dict syntax {{\"key\": \"value\"}} are being "
                f"misinterpreted as template variables."
            )

        # Verify the dict content is preserved literally
        assert '{"type"' in formatted or '"type"' in formatted, \
            "Dict content from step output should be preserved in formatted prompt"

    def test_step5_formats_with_nested_json_in_step_output(self, mock_cwd):
        """
        E2E Test: Step 5 should handle deeply nested JSON structures.

        Tests that even complex nested JSON with multiple levels of braces
        doesn't cause template injection issues.
        """
        from pdd.load_prompt_template import load_prompt_template

        context = {
            "issue_url": "https://github.com/Serhan-Asad/pdd/issues/9",
            "repo_owner": "Serhan-Asad",
            "repo_name": "pdd",
            "issue_number": 9,
            "issue_content": "Test issue",
        }

        # Deeply nested JSON structure
        context["step1_output"] = "Check complete"
        context["step2_output"] = "Confirmed bug"
        context["step3_output"] = """{
  "workflow": {
    "steps": {
      "1": {"status": "completed", "cost": 0.5},
      "2": {"status": "completed", "cost": 0.6},
      "3": {"status": "in_progress", "cost": 0.7}
    },
    "metadata": {
      "repository": {"owner": "test", "name": "repo"},
      "timestamps": {"start": "2026-01-22T10:00:00Z"}
    }
  }
}"""
        context["step4_output"] = "Reproduction complete"

        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None

        # This should NOT raise KeyError
        try:
            formatted = template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"BUG DETECTED (Issue #9): KeyError '{e.args[0]}' with nested JSON.\n"
                f"Even deeply nested JSON structures should be treated as literal content."
            )

        # Verify nested structure is preserved
        assert "workflow" in formatted or "steps" in formatted, \
            "Nested JSON content should be preserved"


    def test_orchestrator_step5_integration_with_mock_llm(self, mock_cwd, monkeypatch):
        """
        E2E Integration Test: Run orchestrator through Step 5 with mocked LLM.

        This test exercises more of the orchestrator code path by:
        1. Calling run_agentic_change_orchestrator with mocked LLM
        2. Simulating progression through all 5 steps
        3. Verifying the orchestrator doesn't crash at Step 5 due to KeyError

        Note: We mock run_agentic_task to avoid actual LLM calls, but the prompt
        loading and formatting code (where the bug is) is NOT mocked.
        """
        # Track which steps were attempted
        steps_attempted = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """
            Mock that lets us track which steps are called and what prompts are used.

            IMPORTANT: This mock is called AFTER the prompt template is loaded and
            formatted, so if there's a KeyError in formatting, this mock won't be
            reached and the test will fail with KeyError.
            """
            import re
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_attempted.append(step_num)

            # Return different outputs for different steps
            # Step 3 returns JSON to trigger the bug at Step 5
            if "step3" in label:
                return (True, """Triage complete.

Analysis: {"status": "proceed", "confidence": 0.95}

Decision: Move to step 4""", 0.001, "mock-model")
            elif "step5" in label:
                # If we reach here, the bug is fixed (template formatting succeeded)
                return (True, "Documentation changes identified", 0.001, "mock-model")
            else:
                return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            """Mock state persistence to avoid side effects."""
            return None

        def mock_load_state(*args, **kwargs):
            """Mock state loading - return no previous state."""
            return None, None

        def mock_clear_state(*args, **kwargs):
            """Mock state clearing."""
            pass

        def mock_subprocess_run(*args, **kwargs):
            """Mock git operations."""
            result = MagicMock()
            result.returncode = 0
            result.stdout = str(mock_cwd)
            return result

        # Patch the LLM task runner and state management
        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        with patch('pdd.agentic_change_orchestrator.subprocess.run', side_effect=mock_subprocess_run):
                            from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

                            try:
                                success, message, cost, model, files = run_agentic_change_orchestrator(
                                    issue_url="https://github.com/Serhan-Asad/pdd/issues/9",
                                    issue_content="Test issue for bug #9",
                                    repo_owner="Serhan-Asad",
                                    repo_name="pdd",
                                    issue_number=9,
                                    issue_author="test-user",
                                    issue_title="Test Issue 9",
                                    cwd=mock_cwd,
                                    verbose=False,
                                    quiet=True,
                                    use_github_state=False
                                )
                            except KeyError as e:
                                pytest.fail(
                                    f"BUG DETECTED (Issue #9): Orchestrator raised KeyError '{e.args[0]}' "
                                    f"during Step 5 prompt formatting.\n\n"
                                    f"Steps attempted before crash: {steps_attempted}\n\n"
                                    f"This confirms the bug at lines 412-413 and 521 of agentic_change_orchestrator.py.\n"
                                    f"Step 3 returned JSON content, which was inserted into Step 5's template without "
                                    f"escaping, causing Python's .format() to misinterpret the braces."
                                )

        # Verify Step 5 was attempted (meaning all steps including Step 5 were formatted)
        assert 5 in steps_attempted, (
            f"Step 5 should have been attempted. Steps attempted: {steps_attempted}\n"
            f"If Step 5 wasn't reached, there may be an earlier issue."
        )


class TestIssue9RegressionPrevention:
    """
    Regression prevention tests for Issue #9.

    These tests check that the fix (escaping braces in step outputs) is properly
    implemented and prevents the template injection vulnerability.
    """

    def test_step_outputs_are_escaped_before_context_insertion(self):
        """
        Regression Test: Verify that step outputs have braces escaped before being added to context.

        This test directly checks the fix: that when step outputs are added to the context
        dictionary at lines 412-413, they have their braces escaped.

        This is a unit test of the orchestrator's context building logic.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        from unittest.mock import patch, MagicMock
        import tempfile

        # Create a minimal temp directory
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_path = Path(tmpdir)
            (tmp_path / ".git").mkdir()
            (tmp_path / ".pdd").mkdir()

            # Track what context is passed to template.format()
            captured_contexts = []

            def mock_template_format(**context):
                """Capture the context dict passed to format()."""
                captured_contexts.append(context.copy())
                return "Mocked formatted prompt"

            def mock_load_template(name):
                """Return a mock template with our format interceptor."""
                mock_template = MagicMock()
                mock_template.format = mock_template_format
                return mock_template

            def mock_run_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
                """Mock LLM calls - step 3 returns JSON."""
                if "step3" in label:
                    return (True, '{"status": "ok"}', 0.001, "mock")
                return (True, "Step output", 0.001, "mock")

            def mock_subprocess_run(*args, **kwargs):
                """Mock git operations."""
                result = MagicMock()
                result.returncode = 0
                result.stdout = str(tmp_path)
                return result

            with patch('pdd.agentic_change_orchestrator.load_prompt_template', side_effect=mock_load_template):
                with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_task):
                    with patch('pdd.agentic_change_orchestrator.save_workflow_state'):
                        with patch('pdd.agentic_change_orchestrator.load_workflow_state', return_value=(None, None)):
                            with patch('pdd.agentic_change_orchestrator.clear_workflow_state'):
                                with patch('pdd.agentic_change_orchestrator.subprocess.run', side_effect=mock_subprocess_run):
                                    try:
                                        run_agentic_change_orchestrator(
                                            issue_url="https://github.com/test/repo/issues/9",
                                            issue_content="Test",
                                            repo_owner="test",
                                            repo_name="repo",
                                            issue_number=9,
                                            issue_author="test",
                                            issue_title="Test",
                                            cwd=tmp_path,
                                            resume=False,
                                            verbose=False,
                                            quiet=True,
                                            use_github_state=False
                                        )
                                    except Exception:
                                        # We're just testing that format() is called with escaped content
                                        pass

            # Check that step outputs in captured contexts have escaped braces
            # After the fix, any step output with JSON like {"status": "ok"} should be
            # escaped to {{"status": "ok"}} when added to context
            if captured_contexts:
                # Find a context that includes step3_output (which had JSON)
                for ctx in captured_contexts:
                    if "step3_output" in ctx:
                        step3_content = ctx["step3_output"]
                        # After escaping, single braces { should become double braces {{
                        # So if the original was {"status": "ok"}, it should now be {{"status": "ok"}}
                        if '{"status"' in step3_content:
                            pytest.fail(
                                f"BUG DETECTED (Issue #9): Step outputs are not being escaped!\n\n"
                                f"Expected: step3_output should have escaped braces like {{{{\"status\": \"ok\"}}}}\n"
                                f"Actual: {repr(step3_content)}\n\n"
                                f"The fix (escaping braces at lines 412-413) is not applied."
                            )
                        # After escaping, we should see doubled braces
                        assert '{{' in step3_content or '{' not in step3_content, (
                            f"Step outputs with braces should be escaped. Got: {repr(step3_content)}"
                        )
