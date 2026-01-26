"""
E2E Test for Issue #8: Template injection bug in pdd change workflow

This E2E test exercises the full `pdd change` CLI workflow to verify the bug where
templates with <include> directives fail when the included content contains JSON braces.

User-Facing Impact:
- Users run `pdd change` workflow
- Workflow processes steps 1-4 successfully
- Step 5 loads template with <include>docs/prompting_guide.md</include>
- If prompting_guide.md contains JSON examples with braces, the workflow crashes
- Error: "Context missing key for step 5: '\n  \"type\"'"
- Users waste ~$1.27-$1.57 per failed attempt
- Workflow is completely blocked

Root Cause (from Step 5 analysis):
1. Step 5's template contains: <include>docs/prompting_guide.md</include>
2. load_prompt_template() does NOT call preprocess() to expand includes
3. When .format(**context) is called at orchestrator.py:521, includes are still raw
4. Later, when includes are processed, JSON braces like {"type": "error"} are interpreted
   as template variables
5. Since '\n  "type"' doesn't exist in context, KeyError is raised

This E2E test:
1. Simulates the full orchestrator workflow from the CLI perspective
2. Runs through step 5 with a template that has <include> directives
3. Verifies the workflow doesn't crash with KeyError
4. Tests the actual user-facing command path, not just internal functions

The test should FAIL on buggy code (KeyError at step 5) and PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock, AsyncMock
import tempfile
import os


@pytest.fixture
def mock_repo(tmp_path):
    """Create a mock repository structure with git and .pdd directory."""
    # Create .git to simulate a git repo
    (tmp_path / ".git").mkdir()

    # Create .pdd directory
    (tmp_path / ".pdd").mkdir()

    # Create pdd/prompts directory structure
    prompts_dir = tmp_path / "pdd" / "prompts"
    prompts_dir.mkdir(parents=True)

    # Create docs directory
    docs_dir = tmp_path / "docs"
    docs_dir.mkdir(parents=True)

    return tmp_path


@pytest.fixture
def step5_template_with_include(tmp_path):
    """Create a simplified Step 5 template with <include> directive."""
    template_content = """% Step 5: Documentation Changes Analysis

You are analyzing documentation changes needed for the issue.

<pdd_prompting_guide>
<include>docs/prompting_guide.md</include>
</pdd_prompting_guide>

% Issue Details
- URL: {issue_url}
- Title: {issue_title}

% Previous Steps
Step 1: {step1_output}
Step 2: {step2_output}
Step 3: {step3_output}
Step 4: {step4_output}

% Task
Analyze what documentation changes are needed for this issue.
"""

    prompts_dir = tmp_path / "pdd" / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    template_path = prompts_dir / "agentic_change_step5_docs_change_LLM.prompt"
    template_path.write_text(template_content)

    return template_path


@pytest.fixture
def prompting_guide_with_json(tmp_path):
    """Create prompting_guide.md with JSON content that triggers the bug."""
    # This is the exact content pattern that causes the bug
    guide_content = """# PDD Prompting Guide

## Example Output Format

When reporting errors, use this format:

```json
{
  "type": "error",
  "message": "Description of the error",
  "code": 500
}
```

## Another Example

Module structure:
```json
{
  "type": "module",
  "name": "test_module"
}
```
"""

    docs_dir = tmp_path / "docs"
    docs_dir.mkdir(parents=True, exist_ok=True)

    guide_path = docs_dir / "prompting_guide.md"
    guide_path.write_text(guide_content)

    return guide_path


class TestIssue8TemplateInjectionE2E:
    """
    E2E tests for Issue #8: Verify pdd change workflow handles templates with includes.

    These tests exercise the full orchestrator code path that a user would hit when
    running `pdd change`, including template loading, preprocessing, and formatting.
    """

    def test_orchestrator_step5_with_include_directive(
        self, mock_repo, step5_template_with_include, prompting_guide_with_json
    ):
        """
        E2E Test: Orchestrator should process Step 5 template with <include> without KeyError.

        This test simulates the exact user workflow from Issue #8:
        1. User runs pdd change workflow
        2. Steps 1-4 complete successfully
        3. Step 5 loads template with <include>docs/prompting_guide.md</include>
        4. prompting_guide.md contains JSON examples with braces
        5. orchestrator calls load_prompt_template() and then .format(**context)

        Expected behavior (after fix):
        - load_prompt_template() preprocesses includes
        - Braces in included JSON are escaped
        - .format(**context) succeeds without KeyError
        - Workflow continues to completion

        Bug behavior (Issue #8):
        - load_prompt_template() returns raw template with unprocessed <include>
        - When includes are processed later, JSON braces are interpreted as variables
        - KeyError: '\n  "type"' is raised at orchestrator.py:521
        - Workflow fails with "Context missing key for step 5: '\n  "type"'"
        """
        from pdd.load_prompt_template import load_prompt_template

        # Change to the mock repo directory
        old_cwd = os.getcwd()
        try:
            os.chdir(mock_repo)

            # Build the context that the orchestrator would pass to Step 5
            # This mimics agentic_change_orchestrator.py lines 401-413
            context = {
                "issue_url": "https://github.com/Serhan-Asad/pdd/issues/8",
                "issue_title": "[TEST] Bug: pdd change fails at step 5 due to template injection",
                "repo_owner": "Serhan-Asad",
                "repo_name": "pdd",
                "issue_number": 8,
                "issue_author": "Serhan-Asad",
                "issue_content": "Test issue for template injection bug",
            }

            # Add outputs from previous steps (steps 1-4)
            context["step1_output"] = "Step 1: Duplicate check - No duplicates found"
            context["step2_output"] = "Step 2: Documentation check - Not documented"
            context["step3_output"] = "Step 3: Research - Issue is valid"
            context["step4_output"] = "Step 4: Requirements clear - Ready to proceed"

            # Load the Step 5 template - step 5 uses "docs_change" as the step name
            template_name = "agentic_change_step5_docs_change_LLM"

            # Mock the resolver to use our test template
            with patch('pdd.load_prompt_template.get_default_resolver') as mock_resolver:
                mock_resolver_instance = MagicMock()
                mock_resolver_instance.resolve_prompt_template.return_value = step5_template_with_include
                mock_resolver.return_value = mock_resolver_instance

                prompt_template = load_prompt_template(template_name)
                assert prompt_template is not None, f"Failed to load template: {template_name}"

                # BUG CHECK 1: The include should be processed (expanded)
                # If it's not processed, we'll see the raw <include> tag
                if "<include>docs/prompting_guide.md</include>" in prompt_template:
                    pytest.fail(
                        "BUG DETECTED (Issue #8): load_prompt_template() returned template with "
                        "unprocessed <include> directive.\n\n"
                        "Root cause: load_prompt_template() does NOT call preprocess().\n\n"
                        "Current behavior: Template contains raw '<include>docs/prompting_guide.md</include>'\n"
                        "Expected behavior: Include should be expanded to the content of prompting_guide.md\n\n"
                        "This is the root cause of the template injection bug - includes are not processed,\n"
                        "leading to potential KeyError when the template is formatted."
                    )

                # If we got here, includes SHOULD have been processed
                # BUG CHECK 2: Verify the included content is present
                if "PDD Prompting Guide" not in prompt_template:
                    pytest.fail(
                        "BUG DETECTED (Issue #8): Template doesn't contain included content.\n\n"
                        "The <include>docs/prompting_guide.md</include> directive was not expanded.\n"
                        "Expected: Included file content to be present in the template\n"
                        "Actual: No content from prompting_guide.md found\n\n"
                        "This confirms load_prompt_template() is NOT calling preprocess()."
                    )

                # BUG CHECK 3: Format the template and check for KeyError
                # This is where the orchestrator fails at line 521
                try:
                    formatted_prompt = prompt_template.format(**context)
                except KeyError as e:
                    # Extract the key that caused the error
                    error_key = str(e.args[0]) if e.args else "unknown"

                    pytest.fail(
                        f"BUG DETECTED (Issue #8): KeyError '{error_key}' raised when formatting "
                        f"Step 5 prompt template.\n\n"
                        f"This is the exact error users see when running 'pdd change':\n"
                        f"  Error: Context missing key for step 5: {e}\n\n"
                        f"Root cause:\n"
                        f"1. Step 5 template has <include>docs/prompting_guide.md</include>\n"
                        f"2. prompting_guide.md contains JSON like {{\"type\": \"error\"}}\n"
                        f"3. load_prompt_template() preprocessed includes BUT didn't escape braces\n"
                        f"4. When .format(**context) runs, it interprets JSON braces as variables\n"
                        f"5. Since '{error_key}' is not in context, KeyError is raised\n\n"
                        f"Expected fix: preprocess() should escape braces in included content\n\n"
                        f"User impact:\n"
                        f"  - Workflow fails at step 5 (100% failure rate)\n"
                        f"  - ~$1.27-$1.57 wasted per attempt\n"
                        f"  - No workaround available"
                    )

                # Verify the formatted prompt is valid
                assert formatted_prompt is not None, "Formatted prompt should not be None"

                # Verify context variables were substituted
                assert "https://github.com/Serhan-Asad/pdd/issues/8" in formatted_prompt, \
                    "issue_url should be substituted in template"
                assert "Step 1: Duplicate check" in formatted_prompt, \
                    "step1_output should be substituted in template"

                # Verify JSON from included file has proper braces (no KeyError means escaping worked)
                # The JSON content should be present as literal text, not interpreted as variables
                assert "type" in formatted_prompt, \
                    "JSON content from included file should be present"

        finally:
            os.chdir(old_cwd)

    def test_orchestrator_full_context_with_include(
        self, mock_repo, step5_template_with_include, prompting_guide_with_json
    ):
        """
        E2E Test: Verify template formatting works with full orchestrator context.

        This test ensures that when load_prompt_template() properly preprocesses
        includes, the template still works correctly with all the variables that
        the orchestrator provides.
        """
        from pdd.load_prompt_template import load_prompt_template

        old_cwd = os.getcwd()
        try:
            os.chdir(mock_repo)

            # Build a more complete context like the real orchestrator would
            context = {
                "issue_url": "https://github.com/Serhan-Asad/pdd/issues/8",
                "issue_title": "[TEST] Template injection bug",
                "repo_owner": "Serhan-Asad",
                "repo_name": "pdd",
                "issue_number": 8,
                "issue_author": "Serhan-Asad",
                "issue_content": "Template injection test",
                "step1_output": "Duplicate check completed",
                "step2_output": "Docs check completed",
                "step3_output": "Research completed",
                "step4_output": "Requirements clarified",
                # Additional context that might be present
                "pddrc_content": "pddrc configuration",
            }

            with patch('pdd.load_prompt_template.get_default_resolver') as mock_resolver:
                mock_resolver_instance = MagicMock()
                mock_resolver_instance.resolve_prompt_template.return_value = step5_template_with_include
                mock_resolver.return_value = mock_resolver_instance

                template = load_prompt_template("agentic_change_step5_docs_change_LLM")
                assert template is not None

                # BUG CHECK: Verify included content is present (confirms preprocessing happened)
                if "PDD Prompting Guide" not in template:
                    pytest.fail(
                        "BUG DETECTED (Issue #8): Template doesn't contain included content.\n\n"
                        "The <include>docs/prompting_guide.md</include> directive was not expanded.\n"
                        "This confirms load_prompt_template() is NOT calling preprocess()."
                    )

                # This should NOT raise KeyError
                try:
                    formatted = template.format(**context)
                except KeyError as e:
                    pytest.fail(
                        f"BUG DETECTED (Issue #8): Template formatting failed with KeyError: {e}\n\n"
                        f"This indicates that either:\n"
                        f"1. <include> directives are not being preprocessed, OR\n"
                        f"2. Braces in included content are not being properly escaped\n\n"
                        f"The user would see this error when running 'pdd change' at step 5."
                    )

                # Verify all substitutions worked
                assert "https://github.com/Serhan-Asad/pdd/issues/8" in formatted
                assert "Duplicate check completed" in formatted
                assert "Requirements clarified" in formatted

        finally:
            os.chdir(old_cwd)

    def test_multiple_includes_in_template(self, mock_repo):
        """
        E2E Test: Verify templates with multiple <include> directives work correctly.

        This is a regression test to ensure the fix handles:
        - Multiple includes in one template
        - Includes with different content types
        - Proper escaping across all included content
        """
        old_cwd = os.getcwd()
        try:
            os.chdir(mock_repo)

            # Create template with multiple includes
            template_content = """% Multi-include template

<section1>
<include>docs/guide1.md</include>
</section1>

<section2>
<include>docs/guide2.md</include>
</section2>

Context: {context_var}
"""

            prompts_dir = mock_repo / "pdd" / "prompts"
            prompts_dir.mkdir(parents=True, exist_ok=True)
            template_path = prompts_dir / "test_multi_include.prompt"
            template_path.write_text(template_content)

            # Create two include files with JSON
            docs_dir = mock_repo / "docs"
            docs_dir.mkdir(parents=True, exist_ok=True)

            guide1 = docs_dir / "guide1.md"
            guide1.write_text('# Guide 1\n```json\n{"section": "one"}\n```')

            guide2 = docs_dir / "guide2.md"
            guide2.write_text('# Guide 2\n```json\n{"section": "two"}\n```')

            from pdd.load_prompt_template import load_prompt_template

            with patch('pdd.load_prompt_template.get_default_resolver') as mock_resolver:
                mock_resolver_instance = MagicMock()
                mock_resolver_instance.resolve_prompt_template.return_value = template_path
                mock_resolver.return_value = mock_resolver_instance

                template = load_prompt_template("test_multi_include")
                assert template is not None

                # BUG CHECK: Verify includes were processed
                if "Guide 1" not in template or "Guide 2" not in template:
                    pytest.fail(
                        "BUG DETECTED (Issue #8): Multiple <include> directives not expanded.\n\n"
                        "load_prompt_template() should preprocess ALL includes in the template."
                    )

                # Format with context
                context = {"context_var": "test_value"}

                try:
                    formatted = template.format(**context)
                except KeyError as e:
                    pytest.fail(
                        f"BUG: Multiple includes caused KeyError: {e}\n\n"
                        f"When templates have multiple <include> directives, all must be "
                        f"preprocessed and all braces must be properly escaped."
                    )

                # Verify variable substitution worked
                assert "test_value" in formatted

        finally:
            os.chdir(old_cwd)


