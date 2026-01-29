"""
E2E Test for Issue #392: pdd change fails at Step 5 with 'Context missing key for step 5: url'

This E2E test exercises the full `pdd change` command to verify that step outputs containing JSON
with curly braces are properly escaped before being added to the context dictionary.

The bug: Lines 490 and 675 of agentic_change_orchestrator.py store step outputs WITHOUT escaping
curly braces:

    Line 490: context[f"step{s_num}_output"] = s_out  # BUG: Not escaped
    Line 675: context[f"step{step_num}_output"] = step_output  # BUG: Not escaped

When step outputs from steps 1-4 contain JSON like {"url": "https://..."}, the Step 5 template
formatting fails because Python's .format() interprets {"url" as a placeholder and tries to access
a key named "url" (with the quote character), causing KeyError: '"url"'.

The fix exists in the codebase (_escape_format_braces() at pdd/agentic_change.py:19-24) and is
correctly applied to issue_content, but NOT to step outputs.

This E2E test:
1. Mocks run_agentic_task to simulate LLM responses containing JSON
2. Exercises the real orchestrator code path through Step 5
3. Verifies no KeyError is raised when formatting the prompt

The test should FAIL on buggy code (KeyError: '"url"') and PASS once the fix is applied.
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


class TestIssue392ChangeOrchestratorE2E:
    """
    E2E tests for Issue #392: Verify the change orchestrator handles JSON in step outputs.

    These tests exercise the full orchestrator code path by mocking only the LLM calls,
    not the template loading or formatting logic where the bug exists.
    """

    def test_change_orchestrator_step5_with_json_outputs(self, mock_cwd, monkeypatch):
        """
        E2E Test: Change orchestrator should handle JSON in step outputs without KeyError.

        This test runs the actual run_agentic_change_orchestrator function with mocked LLM
        responses that contain JSON. The orchestrator should:
        1. Store step outputs from steps 1-4 (some containing JSON)
        2. Load and format the Step 5 template with those outputs in context
        3. NOT raise KeyError: '"url"' during formatting

        This exercises the real bug at lines 490 and 675 of agentic_change_orchestrator.py.
        """
        import sys
        from pathlib import Path

        # Set up environment
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.chdir(mock_cwd)

        # Track which steps were attempted and their prompts
        steps_called = []
        format_errors = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """
            Mock LLM calls with responses containing JSON.

            IMPORTANT: This is called AFTER prompt loading and formatting. If there's a
            KeyError during formatting, this mock won't be reached.
            """
            steps_called.append(label)

            # Return different outputs for each step - some contain JSON with curly braces
            if label == "step1":
                # Duplicate check with JSON status
                return (True, 'No duplicates found.\nStatus: {"unique": true, "count": 0}', 0.001, "mock-model")
            elif label == "step2":
                # Docs check with JSON metadata
                return (True, 'Not implemented.\nMetadata: {"type": "feature", "implemented": false}', 0.001, "mock-model")
            elif label == "step3":
                # Research with JSON containing "url" key - THIS TRIGGERS THE BUG
                return (True, 'Research complete.\nSpecs: {"url": "https://example.com/spec", "version": "1.0"}', 0.001, "mock-model")
            elif label == "step4":
                # Requirements with nested JSON containing "url" key
                return (True, 'Requirements clear.\nDetails: {"needed": false, "data": {"url": "https://docs.example.com"}}', 0.001, "mock-model")
            elif label == "step5":
                # If we get here, Step 5 formatting succeeded!
                return (True, "STOP: Documentation changes identified", 0.001, "mock-model")
            else:
                # Shouldn't get past step 5 in this test
                return (True, f"Step {label} complete", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            """Mock state persistence."""
            return None

        def mock_load_state(*args, **kwargs):
            """Mock state loading - no previous state."""
            return None, None

        def mock_clear_state(*args, **kwargs):
            """Mock state clearing."""
            pass

        # Patch the LLM runner and state management
        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

                        try:
                            success, message, cost, model, files = run_agentic_change_orchestrator(
                                issue_url="https://github.com/promptdriven/pdd/issues/392",
                                issue_content="Test issue for bug #392",
                                repo_owner="promptdriven",
                                repo_name="pdd",
                                issue_number=392,
                                issue_author="test-user",
                                issue_title="Test Issue 392",
                                cwd=mock_cwd,
                                verbose=False,
                                quiet=True,
                                use_github_state=False,
                                timeout_adder=0
                            )
                        except KeyError as e:
                            # THE BUG: This KeyError indicates the bug at lines 490/675
                            pytest.fail(
                                f"BUG DETECTED (Issue #392): Orchestrator raised KeyError '{e.args[0]}' "
                                f"when formatting Step 5 prompt template.\n\n"
                                f"Steps completed before crash: {steps_called}\n\n"
                                f"This confirms the bug at lines 490 and 675 of agentic_change_orchestrator.py:\n"
                                f"  Line 490: context[f'step{{s_num}}_output'] = s_out  # NOT escaped\n"
                                f"  Line 675: context[f'step{{step_num}}_output'] = step_output  # NOT escaped\n\n"
                                f"The step outputs from steps 1-4 contain JSON with curly braces like:\n"
                                f'  {{"url": "https://example.com/spec"}}\n'
                                f"When these are inserted into the Step 5 template via {{step3_output}},\n"
                                f"Python's .format() interprets the JSON braces as new placeholders,\n"
                                f'causing KeyError: \'{e.args[0]}\'\n\n'
                                f"Fix: Apply _escape_format_braces() before storing outputs in context."
                            )

        # Verify all steps through step 5 were attempted
        assert "step1" in steps_called, "Step 1 should have been called"
        assert "step2" in steps_called, "Step 2 should have been called"
        assert "step3" in steps_called, "Step 3 should have been called (contains JSON with 'url' key)"
        assert "step4" in steps_called, "Step 4 should have been called (contains nested JSON)"
        assert "step5" in steps_called, "Step 5 should have been called (proves formatting succeeded)"

    def test_orchestrator_with_complex_json_patterns(self, mock_cwd, monkeypatch):
        """
        E2E Test: Orchestrator should handle various JSON patterns in step outputs.

        This test covers edge cases:
        - Multiline JSON
        - Nested objects
        - Arrays
        - Multiple JSON objects in one output
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.chdir(mock_cwd)

        steps_called = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            steps_called.append(label)

            if label == "step1":
                # Multiline JSON
                return (True, '''Duplicate check complete.
Analysis: {
  "duplicates": [],
  "status": "unique",
  "confidence": 0.95
}''', 0.001, "mock-model")
            elif label == "step2":
                # JSON with arrays
                return (True, 'Docs check.\nData: {"types": ["feature", "enhancement"], "implemented": false}', 0.001, "mock-model")
            elif label == "step3":
                # Multiple JSON objects
                return (True, 'Research done.\nConfig: {"url": "https://a.com"}\nMetadata: {"type": "spec"}', 0.001, "mock-model")
            elif label == "step4":
                # Deeply nested JSON
                return (True, 'Requirements.\nNested: {"a": {"b": {"c": {"url": "https://deep.com"}}}}', 0.001, "mock-model")
            elif label == "step5":
                return (True, "STOP: Done", 0.001, "mock-model")
            else:
                return (True, f"Step {label}", 0.001, "mock-model")

        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', return_value=None):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', return_value=(None, None)):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state'):
                        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

                        try:
                            success, message, cost, model, files = run_agentic_change_orchestrator(
                                issue_url="https://github.com/promptdriven/pdd/issues/392",
                                issue_content="Complex JSON test",
                                repo_owner="promptdriven",
                                repo_name="pdd",
                                issue_number=392,
                                issue_author="test",
                                issue_title="Test",
                                cwd=mock_cwd,
                                verbose=False,
                                quiet=True,
                                use_github_state=False,
                                timeout_adder=0
                            )
                        except KeyError as e:
                            pytest.fail(
                                f"BUG DETECTED: Complex JSON patterns cause KeyError '{e.args[0]}'.\n"
                                f"Steps completed: {steps_called}\n"
                                f"The escaping mechanism should handle all JSON patterns."
                            )

        assert "step5" in steps_called, "Should reach Step 5 without KeyError"

    def test_cached_outputs_with_json(self, mock_cwd, monkeypatch):
        """
        E2E Test: Resuming with cached step outputs containing JSON should work.

        This specifically tests line 490 where cached outputs are loaded from state.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.chdir(mock_cwd)

        # Simulate cached state from steps 1-4
        cached_state = {
            "step_outputs": {
                "1": 'Duplicate check.\nResult: {"status": "unique"}',
                "2": 'Docs check.\nData: {"type": "feature"}',
                "3": 'Research.\nSpec: {"url": "https://example.com"}',
                "4": 'Requirements.\nInfo: {"url": "https://docs.com"}',
            },
            "last_completed_step": 4,
            "total_cost": 0.01,
            "model_used": "mock",
        }

        def mock_load_state(*args, **kwargs):
            """Return cached state to trigger line 490."""
            return cached_state, None

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            # Step 5 should be called with cached outputs in context
            if label == "step5":
                return (True, "STOP: Success with cached outputs", 0.001, "mock")
            return (True, f"Step {label}", 0.001, "mock")

        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', return_value=None):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state'):
                        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

                        try:
                            success, message, cost, model, files = run_agentic_change_orchestrator(
                                issue_url="https://github.com/promptdriven/pdd/issues/392",
                                issue_content="Cached outputs test",
                                repo_owner="promptdriven",
                                repo_name="pdd",
                                issue_number=392,
                                issue_author="test",
                                issue_title="Test",
                                cwd=mock_cwd,
                                verbose=False,
                                quiet=True,
                                use_github_state=False,
                                timeout_adder=0
                            )
                        except KeyError as e:
                            pytest.fail(
                                f"BUG DETECTED (Issue #392): Cached outputs at line 490 not escaped.\n"
                                f"KeyError '{e.args[0]}' when formatting with cached step outputs.\n\n"
                                f"Bug location: agentic_change_orchestrator.py:490\n"
                                f"  for s_num, s_out in step_outputs.items():\n"
                                f"      context[f'step{{s_num}}_output'] = s_out  # BUG: NOT escaped"
                            )


class TestIssue392RegressionPrevention:
    """
    Regression prevention tests for Issue #392.
    """

    def test_escape_format_braces_function_exists(self):
        """
        Verify the _escape_format_braces function exists and works correctly.
        """
        from pdd.agentic_change import _escape_format_braces

        # Test the existing escape function
        test_cases = [
            ('{"url": "https://example.com"}', '{{"url": "https://example.com"}}'),
            ('{"type": "feature"}', '{{"type": "feature"}}'),
            ('result = {key: value}', 'result = {{key: value}}'),
            ('f"{variable}"', 'f"{{variable}}"'),
            ('No braces here', 'No braces here'),
            # Nested JSON
            ('{"a": {"b": "c"}}', '{{"a": {{"b": "c"}}}}'),
            # Arrays
            ('{"items": [1, 2, 3]}', '{{"items": [1, 2, 3]}}'),
        ]

        for input_text, expected_output in test_cases:
            result = _escape_format_braces(input_text)
            assert result == expected_output, (
                f"_escape_format_braces failed for: {input_text}\n"
                f"Expected: {expected_output}\n"
                f"Got: {result}"
            )

    def test_normal_outputs_work_after_fix(self, mock_cwd, monkeypatch):
        """
        Regression Test: Normal step outputs without JSON should still work.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.chdir(mock_cwd)

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            # Simple outputs without special characters
            outputs = {
                "step1": "No duplicates found after searching 50 issues.",
                "step2": "Feature is not yet implemented in the codebase.",
                "step3": "Research indicates this requires API changes.",
                "step4": "Requirements are clear and complete.",
                "step5": "STOP: Documentation changes identified",
            }
            return (True, outputs.get(label, f"Step {label}"), 0.001, "mock")

        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', return_value=None):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', return_value=(None, None)):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state'):
                        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

                        success, message, cost, model, files = run_agentic_change_orchestrator(
                            issue_url="https://github.com/promptdriven/pdd/issues/392",
                            issue_content="Normal test",
                            repo_owner="promptdriven",
                            repo_name="pdd",
                            issue_number=392,
                            issue_author="test",
                            issue_title="Test",
                            cwd=mock_cwd,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                            timeout_adder=0
                        )

        # Should complete successfully
        assert success or "STOP" in message, "Normal outputs should work without errors"
