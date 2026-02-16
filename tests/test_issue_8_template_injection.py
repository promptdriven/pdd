"""
E2E Test for Issue #8: Template injection bug due to unprocessed <include> directives

This test suite verifies the bug where load_prompt_template() fails to preprocess <include>
directives before returning, causing issues when included files contain content with braces.

Root Cause (identified in Issue #8 Step 5):
1. Step 5's template contains: <include>docs/prompting_guide.md</include>
2. load_prompt_template() only reads the file - it does NOT call preprocess() to process includes
3. When the orchestrator later calls .format(**context), unprocessed includes remain in the template
4. If includes are eventually processed and contain JSON like {"type": "module"}, those braces
   may cause issues depending on the processing order

The Bug Location:
- pdd/load_prompt_template.py: load_prompt_template() function doesn't call preprocess()
- Expected: load_prompt_template() should call preprocess() to expand <include> directives

This test should FAIL on buggy code (include directives not processed) and PASS once
load_prompt_template() is fixed to call preprocess().
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
import os


class TestIssue8TemplateInjection:
    """
    Tests for Issue #8: Verify template injection bug due to unprocessed includes.

    These tests exercise the load_prompt_template() function to verify that it properly
    preprocesses <include> directives before returning the template.
    """

    def test_load_prompt_template_should_preprocess_includes(self, tmp_path):
        """
        Unit Test: load_prompt_template() should call preprocess() to expand <include> directives.

        This is the PRIMARY test for Issue #8. It verifies that load_prompt_template()
        preprocesses <include> tags before returning.

        Expected behavior (after fix):
        - load_prompt_template() calls preprocess() before returning
        - <include> directives are expanded
        - Returned template has no <include> tags

        Bug behavior (Issue #8):
        - load_prompt_template() returns raw file content
        - <include> tags remain in the template
        """
        # Create a minimal template with an include directive
        prompts_dir = tmp_path / "pdd" / "prompts"
        prompts_dir.mkdir(parents=True)

        template_content = "Before include\n<include>test.txt</include>\nAfter include\nVariable: {myvar}"
        template_path = prompts_dir / "test_template.prompt"
        template_path.write_text(template_content)

        # Create the file to be included with JSON content that has braces
        test_file = tmp_path / "test.txt"
        test_file.write_text('INCLUDED: {"key": "value"}')

        # Set up environment
        old_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)

            # Load the template
            from pdd.load_prompt_template import load_prompt_template

            with patch('pdd.load_prompt_template.get_default_resolver') as mock_resolver:
                mock_resolver_instance = MagicMock()
                mock_resolver_instance.resolve_prompt_template.return_value = template_path
                mock_resolver.return_value = mock_resolver_instance

                template = load_prompt_template("test_template")
                assert template is not None

                # BUG CHECK: The include directive should NOT be in the returned template
                # After the fix, preprocess() will have expanded it
                if "<include>" in template:
                    pytest.fail(
                        "BUG DETECTED (Issue #8): load_prompt_template() returned template with "
                        "unprocessed <include> directive.\n\n"
                        "The function should call preprocess() to expand includes before returning.\n\n"
                        f"Template content:\n{template}\n\n"
                        "Expected includes to be expanded.\n"
                        f"Actual: template still contains '<include>' tags"
                    )

                # If we got here, includes were processed! Now verify the template works correctly
                # Template variables like {myvar} should still work with .format()
                try:
                    formatted = template.format(myvar="TEST_VALUE")

                    # After formatting, we should have both the included content AND the variable substituted
                    assert "INCLUDED:" in formatted, "Include content should be present"
                    assert "TEST_VALUE" in formatted, "Template variable should be substituted"

                    # The JSON from the included file should have single braces (properly escaped during include)
                    # After .format(), double braces {{  should become single braces {
                    assert '{"key": "value"}' in formatted, "JSON from included file should have single braces after formatting"

                except KeyError as e:
                    pytest.fail(
                        f"BUG: After loading template, .format() raised KeyError: {e}\n\n"
                        f"This means either template variables weren't preserved correctly during preprocessing,\n"
                        f"or braces in included content weren't properly escaped."
                    )

        finally:
            os.chdir(old_cwd)

    def test_step5_template_has_unprocessed_include(self, tmp_path):
        """
        Regression Test: Verify that Step 5 template's <include> directive is processed.

        This test simulates the exact scenario from Issue #8:
        - Step 5 template contains <include>docs/prompting_guide.md</include>
        - prompting_guide.md contains JSON examples
        - load_prompt_template() should preprocess the include

        Bug behavior: <include> tag remains in template
        Expected behavior: Include is expanded and braces are escaped
        """
        # Set up the exact file structure from the bug report
        prompts_dir = tmp_path / "pdd" / "prompts"
        prompts_dir.mkdir(parents=True)

        # Step 5 template (simplified version of the real one)
        step5_template = """% Step 5: Documentation Changes

<pdd_prompting_guide>
<include>docs/prompting_guide.md</include>
</pdd_prompting_guide>

Issue: {issue_url}
Previous output: {step4_output}
"""

        template_path = prompts_dir / "agentic_change_step5_docs_change_LLM.prompt"
        template_path.write_text(step5_template)

        # prompting_guide.md with JSON (the trigger from Issue #8)
        docs_dir = tmp_path / "docs"
        docs_dir.mkdir(parents=True)

        guide_content = """# Prompting Guide

Example output format:
```json
{
  "type": "error",
  "message": "test"
}
```
"""

        guide_path = docs_dir / "prompting_guide.md"
        guide_path.write_text(guide_content)

        # Set up environment
        old_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)

            # Load template
            from pdd.load_prompt_template import load_prompt_template

            with patch('pdd.load_prompt_template.get_default_resolver') as mock_resolver:
                mock_resolver_instance = MagicMock()
                mock_resolver_instance.resolve_prompt_template.return_value = template_path
                mock_resolver.return_value = mock_resolver_instance

                template = load_prompt_template("agentic_change_step5_docs_change_LLM")
                assert template is not None

                # BUG CHECK: Include should be processed
                if "<include>docs/prompting_guide.md</include>" in template:
                    pytest.fail(
                        "BUG DETECTED (Issue #8): Step 5 template has unprocessed <include> directive.\n\n"
                        "load_prompt_template() should have called preprocess() to expand the include.\n\n"
                        "This is the root cause of the template injection bug in Issue #8."
                    )

                # If preprocessing worked, the guide content should be in the template
                assert "Prompting Guide" in template, \
                    "After preprocessing, included content should be in template"

                # Now verify formatting works without errors
                context = {
                    "issue_url": "https://github.com/Serhan-Asad/pdd/issues/8",
                    "step4_output": "Step 4 completed",
                }

                try:
                    formatted = template.format(**context)

                    # Verify variables were substituted
                    assert "https://github.com/Serhan-Asad/pdd/issues/8" in formatted
                    assert "Step 4 completed" in formatted

                    # Verify JSON from included file has proper single braces
                    assert '"type": "error"' in formatted
                    assert '"message": "test"' in formatted

                except KeyError as e:
                    pytest.fail(
                        f"BUG: Formatting failed with KeyError: {e}\n\n"
                        f"This means braces in the included content weren't properly escaped."
                    )

        finally:
            os.chdir(old_cwd)


class TestIssue8RootCauseVerification:
    """
    Root cause verification tests for Issue #8.

    These tests verify the specific function behavior that causes the bug:
    load_prompt_template() not calling preprocess().
    """

    def test_load_prompt_template_should_call_preprocess(self):
        """
        Specification Test: load_prompt_template() should call preprocess().

        This test verifies through mocking that load_prompt_template() calls preprocess()
        on the template content before returning it.

        Current behavior (BUG):
        - load_prompt_template() only reads the file and returns raw content
        - It does NOT call preprocess()
        - This leaves <include> directives unprocessed

        Expected behavior (AFTER FIX):
        - load_prompt_template() imports and calls preprocess()
        - <include> directives are expanded
        - Braces in included content are properly escaped
        - The returned template is ready for .format(**context)
        """
        from unittest.mock import mock_open

        # Create a mock template content
        template_content = "Test template with <include>file.txt</include>"

        # Set up mocks
        with patch('builtins.open', mock_open(read_data=template_content)):
            with patch('pdd.load_prompt_template.get_default_resolver') as mock_resolver:
                # Set up resolver to return a valid path
                mock_resolver_instance = MagicMock()
                mock_path = Path("/fake/path/template.prompt")
                mock_resolver_instance.resolve_prompt_template.return_value = mock_path
                mock_resolver.return_value = mock_resolver_instance

                # Try to patch preprocess - if it's not imported, this will fail
                try:
                    with patch('pdd.load_prompt_template.preprocess') as mock_preprocess:
                        mock_preprocess.return_value = "Preprocessed content"

                        from pdd.load_prompt_template import load_prompt_template
                        result = load_prompt_template("test_template")

                        # Verify preprocess was called
                        if not mock_preprocess.called:
                            pytest.fail(
                                "BUG DETECTED (Issue #8): load_prompt_template() does NOT call preprocess().\n\n"
                                "Root cause: The function at pdd/load_prompt_template.py loads the file "
                                "but returns raw content without preprocessing <include> directives.\n\n"
                                "Expected behavior: load_prompt_template() should call:\n"
                                "  from pdd.preprocess import preprocess\n"
                                "  preprocessed = preprocess(prompt_template)\n"
                                "  return preprocessed\n\n"
                                "This causes templates with <include> directives to fail when "
                                "included files contain JSON or other content with braces."
                            )

                        # After fix, result should be the preprocessed content
                        assert result == "Preprocessed content", \
                            "load_prompt_template should return preprocessed content"

                except AttributeError:
                    # preprocess is not imported in load_prompt_template
                    pytest.fail(
                        "BUG DETECTED (Issue #8): load_prompt_template() does NOT import preprocess.\n\n"
                        "Root cause: The module pdd/load_prompt_template.py doesn't import preprocess from pdd.preprocess.\n\n"
                        "Expected fix:\n"
                        "1. Add import: from pdd.preprocess import preprocess\n"
                        "2. Call it before returning: return preprocess(prompt_template)\n\n"
                        "This is the core issue preventing <include> directives from being processed."
                    )
