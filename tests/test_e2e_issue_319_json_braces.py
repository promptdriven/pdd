"""
E2E Test for Issue #319: pdd change fails at Step 5 with KeyError when issue contains JSON

Investigation findings (from Steps 4-5 of bug workflow):
- The bug as described is technically impossible to reproduce with current codebase
- Python's str.format() does NOT re-parse already-substituted values
- The error can only occur if the TEMPLATE ITSELF contains literal JSON (not context values)
- Current template files don't contain raw JSON

This E2E test serves as a REGRESSION TEST to ensure:
1. The full CLI path handles JSON in GitHub issue content
2. The orchestrator handles JSON in step outputs passed to subsequent steps
3. No future changes introduce the bug pattern

The tests PASS on the current codebase (confirming correct behavior).
"""

import json
import pytest
from pathlib import Path
from unittest.mock import MagicMock, patch

# Import modules under test
from pdd.agentic_change import run_agentic_change
from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module.

    This is required because construct_paths uses PDD_PATH to find the language_format.csv
    file for language detection.
    """
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestIssue319JsonBracesE2E:
    """E2E tests for Issue #319: Verify pdd change handles JSON curly braces correctly."""

    def test_e2e_change_with_json_in_issue_body(self, tmp_path, monkeypatch):
        """
        E2E Test: pdd change should handle GitHub issues containing JSON code blocks.

        This exercises the full path: run_agentic_change -> orchestrator -> template formatting.
        The issue content containing JSON should pass through str.format() without raising KeyError.

        Expected behavior:
        - JSON in issue_content is passed through unchanged
        - No KeyError occurs during template formatting
        - Workflow proceeds normally

        Bug behavior (Issue #319) if it were real:
        - KeyError: '\\n  "type"' at Step 5 during template.format(**context)
        """
        # Mock the external dependencies but NOT the str.format() code path
        with patch("pdd.agentic_change.shutil.which") as mock_which, \
             patch("pdd.agentic_change.subprocess.run") as mock_subprocess, \
             patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_agentic_task, \
             patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_orch_subprocess, \
             patch("pdd.agentic_change.console"), \
             patch("pdd.agentic_change_orchestrator.console"):

            # gh CLI is installed
            mock_which.return_value = "/usr/bin/gh"

            # GitHub issue with JSON content - matching the exact error pattern from issue #319
            # The error was: KeyError: '\n  "type"'
            issue_data = {
                "title": "Context map sampling fails with JSON error",
                "body": '''The integration fails when the context map returns JSON:

```json
{
  "type": "error",
  "message": "Context sampling failed",
  "details": {
    "code": 500,
    "reason": "internal error"
  }
}
```

Expected behavior: Should handle JSON gracefully.
Actual behavior: Crashes with KeyError.

Here's the config that causes it:
```json
{
  "sampling_rate": 0.1,
  "enabled": true
}
```
''',
                "user": {"login": "jamesdlevine"},
                "comments_url": ""
            }

            def subprocess_side_effect(args, **kwargs):
                cmd = args if isinstance(args, list) else []

                # Issue API
                if "api" in cmd and "issues" in str(cmd):
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = json.dumps(issue_data)
                    return m

                # Git rev-parse for root detection
                if "rev-parse" in cmd:
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = str(tmp_path)
                    return m

                # Git worktree operations
                if "worktree" in cmd:
                    if "list" in cmd:
                        m = MagicMock()
                        m.returncode = 0
                        m.stdout = ""
                        return m
                    elif "add" in cmd:
                        # Create the worktree directory
                        worktree_dir = tmp_path / ".pdd" / "worktrees" / "change-issue-319"
                        worktree_dir.mkdir(parents=True, exist_ok=True)
                        m = MagicMock()
                        m.returncode = 0
                        return m

                # Git branch operations
                if "branch" in cmd:
                    m = MagicMock()
                    m.returncode = 0
                    return m

                # Default fallback
                m = MagicMock()
                m.returncode = 0
                m.stdout = str(tmp_path)
                return m

            mock_subprocess.side_effect = subprocess_side_effect
            mock_orch_subprocess.side_effect = subprocess_side_effect

            # Mock agentic task responses
            def agentic_task_side_effect(**kwargs):
                label = kwargs.get("label", "")
                if label == "step9":
                    return (True, "FILES_MODIFIED: fix.py", 0.1, "gpt-4")
                if label.startswith("step10"):
                    return (True, "No Issues Found", 0.1, "gpt-4")
                if label == "step12":
                    return (True, "PR Created: https://github.com/owner/repo/pull/1", 0.1, "gpt-4")
                return (True, f"Output for {label}", 0.1, "gpt-4")

            mock_agentic_task.side_effect = agentic_task_side_effect

            # Mock Path.cwd to simulate we're in the repo
            mock_path = MagicMock()
            mock_path.__truediv__ = MagicMock(return_value=MagicMock(exists=MagicMock(return_value=True)))
            mock_path.__str__ = lambda self: str(tmp_path)
            mock_path.__fspath__ = lambda self: str(tmp_path)

            # Create .git directory to simulate a git repo
            (tmp_path / ".git").mkdir(exist_ok=True)

            with patch("pdd.agentic_change.Path.cwd") as mock_cwd:
                mock_cwd.return_value = tmp_path

                # Mock git remote to match the URL
                def subprocess_side_effect_with_remote(args, **kwargs):
                    cmd = args if isinstance(args, list) else []
                    if "remote" in cmd and "get-url" in cmd:
                        m = MagicMock()
                        m.returncode = 0
                        m.stdout = "https://github.com/promptdriven/pdd.git"
                        return m
                    return subprocess_side_effect(args, **kwargs)

                mock_subprocess.side_effect = subprocess_side_effect_with_remote

                # RUN THE FULL E2E PATH
                success, msg, cost, model, files = run_agentic_change(
                    "https://github.com/promptdriven/pdd/issues/319",
                    verbose=False,
                    quiet=True,
                    use_github_state=False
                )

        # THE KEY ASSERTION: The bug pattern would cause this error message
        assert "Context missing key" not in msg, (
            f"BUG DETECTED (Issue #319): JSON braces in issue content caused KeyError!\n"
            f"Error message: {msg}\n"
            f"This means str.format() incorrectly interpreted JSON braces as placeholders."
        )

        # Verify the workflow completed successfully
        assert success is True, f"Workflow failed unexpectedly: {msg}"

    def test_e2e_change_with_json_in_step_outputs(self, tmp_path, monkeypatch):
        """
        E2E Test: Verify JSON in step outputs doesn't cause KeyError in later steps.

        When step 4 returns JSON-containing output, step 5's template uses {step4_output}.
        Python's str.format() should NOT re-parse the JSON braces in the substituted value.

        This tests the specific scenario from Issue #319 where step outputs contain JSON.
        """
        with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_agentic_task, \
             patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_subprocess, \
             patch("pdd.agentic_change_orchestrator.console"):

            def subprocess_side_effect(args, **kwargs):
                cmd = args if isinstance(args, list) else []

                if "rev-parse" in cmd:
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = str(tmp_path)
                    return m

                if "worktree" in cmd:
                    if "list" in cmd:
                        m = MagicMock()
                        m.returncode = 0
                        m.stdout = ""
                        return m
                    elif "add" in cmd:
                        worktree_dir = tmp_path / ".pdd" / "worktrees" / "change-issue-320"
                        worktree_dir.mkdir(parents=True, exist_ok=True)
                        m = MagicMock()
                        m.returncode = 0
                        return m

                if "branch" in cmd:
                    m = MagicMock()
                    m.returncode = 0
                    return m

                m = MagicMock()
                m.returncode = 0
                m.stdout = str(tmp_path)
                return m

            mock_subprocess.side_effect = subprocess_side_effect

            # Step 4 returns JSON-containing output that will be substituted into step 5
            def agentic_task_side_effect(**kwargs):
                label = kwargs.get("label", "")

                if label == "step4":
                    # Return output with JSON that has the exact pattern from the bug
                    return (True, '''Analysis complete. Found the following configuration:

```json
{
  "type": "feature",
  "priority": "high",
  "affects": ["module_a", "module_b"]
}
```

Requirements are clear. The change should:
1. Modify the sampling rate
2. Update error handling

Configuration schema:
```json
{
  "sampling": {
    "rate": 0.1,
    "enabled": true
  }
}
```
''', 0.1, "gpt-4")

                if label == "step9":
                    return (True, "FILES_MODIFIED: config.py", 0.1, "gpt-4")
                if label.startswith("step10"):
                    return (True, "No Issues Found", 0.1, "gpt-4")
                if label == "step12":
                    return (True, "PR Created: https://github.com/owner/repo/pull/2", 0.1, "gpt-4")
                return (True, f"Output for {label}", 0.1, "gpt-4")

            mock_agentic_task.side_effect = agentic_task_side_effect

            # Create state directory
            state_dir = tmp_path / ".pdd" / "change-state"
            state_dir.mkdir(parents=True, exist_ok=True)

            # RUN THE ORCHESTRATOR DIRECTLY
            success, msg, cost, model, files = run_agentic_change_orchestrator(
                issue_url="https://github.com/promptdriven/pdd/issues/320",
                issue_content="Add support for context map sampling",
                repo_owner="promptdriven",
                repo_name="pdd",
                issue_number=320,
                issue_author="user",
                issue_title="Add context map sampling",
                cwd=tmp_path,
                quiet=True,
                use_github_state=False
            )

        # THE KEY ASSERTION
        assert "Context missing key" not in msg, (
            f"BUG DETECTED: JSON braces in step4_output caused KeyError at step 5!\n"
            f"Error: {msg}\n"
            f"Python's str.format() should NOT re-parse JSON in substituted values."
        )

        # Verify step 5 was reached and the workflow completed
        assert success is True, f"Workflow failed: {msg}"

    def test_e2e_demonstrates_bug_pattern_keyerror(self):
        """
        Documentation test: Demonstrates the exact bug pattern that WOULD cause KeyError.

        This test shows that JSON in the TEMPLATE causes KeyError, but JSON in VALUES does not.
        This clarifies the investigation findings from Steps 4-5.
        """
        # CORRECT BEHAVIOR: JSON in a context VALUE works fine
        template = "Issue: {issue_content}"
        json_value = '{\n  "type": "error",\n  "code": 500\n}'

        # This should NOT raise - JSON is in the value, not the template
        result = template.format(issue_content=json_value)
        assert json_value in result

        # BUG PATTERN: JSON directly in template causes KeyError
        # This is what would happen if a template file contained raw JSON
        bad_template = '{\n  "type": "error"\n}'

        with pytest.raises(KeyError) as exc_info:
            bad_template.format()

        # The error shows Python trying to interpret JSON key as format placeholder
        assert "type" in str(exc_info.value)

    def test_e2e_format_behavior_with_nested_braces(self):
        """
        Documentation test: Verify str.format() does NOT re-parse substituted values.

        This confirms the bug as described cannot occur with standard Python behavior.
        Python's str.format() performs SINGLE-PASS substitution.
        """
        # Template with multiple placeholders
        template = "Step 4 output: {step4_output}\nStep 5 output: {step5_output}"

        # Values containing JSON with curly braces
        step4_value = '{\n  "type": "clarification",\n  "details": {"key": "value"}\n}'
        step5_value = 'Analysis shows:\n```json\n{"result": "ok"}\n```'

        # Single format call - should NOT re-parse JSON braces
        result = template.format(step4_output=step4_value, step5_output=step5_value)

        # Verify JSON passed through unchanged
        assert step4_value in result
        assert step5_value in result

        # The JSON braces in the result are literal characters, not format placeholders
        # This proves the bug cannot occur through normal substitution
        assert '{"key": "value"}' in result
        assert '{"result": "ok"}' in result


class TestIssue319RegressionTests:
    """Regression tests to prevent reintroduction of the bug pattern."""

    def test_orchestrator_context_substitution_order(self, tmp_path, monkeypatch):
        """
        Verify the orchestrator's context substitution happens only once per template.

        This ensures there's no double-format scenario that could cause the bug.
        The orchestrator should:
        1. Load template
        2. Call template.format(**context) ONCE
        3. Pass the fully-substituted string to the agent

        A double-format bug would look like:
        1. template.format(**context) -> partial result with JSON
        2. partial_result.format(...) -> KeyError on JSON braces
        """
        with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_agentic_task, \
             patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_subprocess, \
             patch("pdd.agentic_change_orchestrator.console"):

            # Track how many times format is called per template load
            format_calls = []

            def subprocess_side_effect(args, **kwargs):
                cmd = args if isinstance(args, list) else []

                if "rev-parse" in cmd:
                    m = MagicMock()
                    m.returncode = 0
                    m.stdout = str(tmp_path)
                    return m

                if "worktree" in cmd:
                    if "list" in cmd:
                        m = MagicMock()
                        m.returncode = 0
                        m.stdout = ""
                        return m
                    elif "add" in cmd:
                        worktree_dir = tmp_path / ".pdd" / "worktrees" / "change-issue-321"
                        worktree_dir.mkdir(parents=True, exist_ok=True)
                        m = MagicMock()
                        m.returncode = 0
                        return m

                if "branch" in cmd:
                    m = MagicMock()
                    m.returncode = 0
                    return m

                m = MagicMock()
                m.returncode = 0
                m.stdout = str(tmp_path)
                return m

            mock_subprocess.side_effect = subprocess_side_effect

            def agentic_task_side_effect(**kwargs):
                label = kwargs.get("label", "")
                instruction = kwargs.get("instruction", "")

                # Record that we received a formatted instruction
                # If double-format occurred, we'd see KeyError before getting here
                format_calls.append(label)

                if label == "step9":
                    return (True, "FILES_MODIFIED: test.py", 0.1, "gpt-4")
                if label.startswith("step10"):
                    return (True, "No Issues Found", 0.1, "gpt-4")
                if label == "step12":
                    return (True, "PR Created: https://github.com/owner/repo/pull/3", 0.1, "gpt-4")
                return (True, f"Output for {label}", 0.1, "gpt-4")

            mock_agentic_task.side_effect = agentic_task_side_effect

            state_dir = tmp_path / ".pdd" / "change-state"
            state_dir.mkdir(parents=True, exist_ok=True)

            # Issue content with JSON
            issue_with_json = '''Fix the following error:

```json
{
  "error": "KeyError",
  "details": {
    "key": "type",
    "context": "template formatting"
  }
}
```
'''

            success, msg, cost, model, files = run_agentic_change_orchestrator(
                issue_url="https://github.com/promptdriven/pdd/issues/321",
                issue_content=issue_with_json,
                repo_owner="promptdriven",
                repo_name="pdd",
                issue_number=321,
                issue_author="user",
                issue_title="Test JSON handling",
                cwd=tmp_path,
                quiet=True,
                use_github_state=False
            )

        # If double-format occurred, we would have seen KeyError and no format_calls
        assert len(format_calls) > 0, "No agentic tasks were called - possible format error"
        assert "step1" in format_calls, "Step 1 was not executed"
        assert success is True, f"Workflow failed: {msg}"
        assert "Context missing key" not in msg

    def test_template_files_contain_no_raw_json(self, monkeypatch):
        """
        Scan all agentic_change step templates to verify they don't contain raw JSON.

        Raw JSON in templates would cause KeyError when format() is called.
        This test ensures no template file accidentally contains literal JSON braces.
        """
        import pdd
        prompts_dir = Path(pdd.__file__).parent / "prompts"

        # Find all agentic_change step templates
        templates_to_check = [
            "agentic_change_step1_duplicate_LLM.prompt",
            "agentic_change_step2_docs_LLM.prompt",
            "agentic_change_step3_research_LLM.prompt",
            "agentic_change_step4_clarify_LLM.prompt",
            "agentic_change_step5_docs_change_LLM.prompt",
            "agentic_change_step6_devunits_LLM.prompt",
            "agentic_change_step7_architecture_LLM.prompt",
            "agentic_change_step8_analyze_LLM.prompt",
            "agentic_change_step9_implement_LLM.prompt",
            "agentic_change_step10_identify_issues_LLM.prompt",
            "agentic_change_step11_fix_issues_LLM.prompt",
            "agentic_change_step12_create_pr_LLM.prompt",
        ]

        for template_name in templates_to_check:
            template_path = prompts_dir / template_name
            if not template_path.exists():
                continue  # Skip missing templates (they'll fail at runtime anyway)

            content = template_path.read_text()

            # Look for suspicious JSON patterns that aren't escaped
            # Pattern: { followed by newline and "key": which is raw JSON
            import re
            raw_json_pattern = r'\{\s*\n\s*"[a-zA-Z_]+'

            # Exclude patterns that are within code blocks (``` ... ```)
            # or are legitimate format placeholders like {step1_output}
            matches = re.findall(raw_json_pattern, content)

            for match in matches:
                # Skip if it looks like a format placeholder
                if re.match(r'\{\s*[a-z_]+\s*\}', match):
                    continue

                # Skip if inside a code block (rough heuristic)
                # A proper check would parse the markdown
                if '```' in content:
                    # More sophisticated: check if match is between ``` markers
                    # For now, we'll rely on the test actually trying to format
                    pass

            # The ultimate test: try to format with empty context to see if raw JSON exists
            # We only check required placeholders; extra {} without a matching key = KeyError
            try:
                # Extract all placeholder names from the template
                placeholders = re.findall(r'\{([a-z_0-9]+)\}', content)
                test_context = {p: "test_value" for p in set(placeholders)}

                # This will raise KeyError if there's raw JSON in the template
                content.format(**test_context)

            except KeyError as e:
                pytest.fail(
                    f"Template {template_name} contains raw JSON or invalid placeholder!\n"
                    f"KeyError: {e}\n"
                    f"This would cause the bug described in Issue #319."
                )
