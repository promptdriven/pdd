"""
E2E Test for Issue #448: KeyError '"url"' in step 5 prompt template due to unescaped JSON braces

This E2E test exercises the prompt loading and formatting code path for Step 5 of the
agentic change workflow. It verifies that the orchestrator correctly handles templates
that include files containing JSON content.

The bug: The agentic_change_orchestrator.py does NOT call preprocess() before format().
When a template includes docs/prompting_guide.md (which contains JSON like {"url": "..."}),
and includes ARE expanded, the JSON curly braces cause KeyError during format().

The architecture orchestrator correctly handles this by calling:
    preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude_keys=...)

The change orchestrator is missing this preprocessing step.

This E2E test:
1. Loads the Step 5 template and preprocesses it (to expand includes)
2. Simulates the buggy behavior (no double_curly escaping)
3. Verifies that format() raises KeyError on the JSON content
4. Then verifies the correct fix (with double_curly_brackets=True) works

The test should FAIL on buggy code (the orchestrator doesn't use preprocess correctly)
and PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
import inspect


@pytest.fixture
def mock_cwd(tmp_path):
    """Create a mock working directory with .git to simulate a git repo."""
    (tmp_path / ".git").mkdir()
    (tmp_path / ".pdd").mkdir()
    return tmp_path


class TestIssue448Step5KeyErrorE2E:
    """
    E2E tests for Issue #448: Verify Step 5 prompt template formats without KeyError.

    These tests verify that the orchestrator correctly preprocesses templates before
    calling format(), which is required when templates include files with JSON content.
    """

    def test_step5_template_without_preprocessing_causes_keyerror(self, mock_cwd):
        """
        BUG REPRODUCTION TEST: Shows that expanding includes WITHOUT double_curly causes KeyError.

        This test demonstrates the bug:
        1. Load the template
        2. Expand includes (but DON'T escape curly braces)
        3. Try to format - this SHOULD raise KeyError

        This is what the current buggy orchestrator code effectively does.
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        # Build the context that the orchestrator passes to Step 5
        context = {
            "issue_url": "https://github.com/test/repo/issues/448",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 448,
            "issue_content": "Test issue content for bug #448",
            "step1_output": "Step 1 output",
            "step2_output": "Step 2 output",
            "step3_output": "Step 3 output",
            "step4_output": "Step 4 output",
        }

        # Load the Step 5 template
        template_name = "agentic_change_step5_docs_change_LLM"
        prompt_template = load_prompt_template(template_name)
        assert prompt_template is not None, f"Failed to load template: {template_name}"

        # Expand includes BUT don't escape curly braces (simulates the bug)
        # This is what happens when preprocess is called with double_curly_brackets=False
        processed_template = preprocess(
            prompt_template,
            recursive=True,
            double_curly_brackets=False,  # BUG: Should be True
            exclude_keys=[]
        )

        # Verify the processed template contains the JSON that causes the bug
        assert '{"url":' in processed_template or '"url"' in processed_template, \
            "Processed template should contain JSON from included files"

        # THE BUG: format() raises KeyError because JSON braces are interpreted as placeholders
        with pytest.raises(KeyError) as exc_info:
            processed_template.format(**context)

        # Verify it's the specific error from the bug report
        assert '"url"' in str(exc_info.value), \
            f"Expected KeyError for '\"url\"', got: {exc_info.value}"

    def test_step5_template_with_correct_preprocessing_works(self, mock_cwd):
        """
        FIX VERIFICATION TEST: Shows that preprocessing with double_curly=True prevents KeyError.

        This test demonstrates the fix:
        1. Load the template
        2. Preprocess with double_curly_brackets=True and exclude context keys
        3. Try to format - this SHOULD succeed

        This is what the architecture orchestrator does correctly.
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        # Build the context
        context = {
            "issue_url": "https://github.com/test/repo/issues/448",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 448,
            "issue_content": "Test issue content for bug #448",
            "step1_output": "Step 1 output",
            "step2_output": "Step 2 output",
            "step3_output": "Step 3 output",
            "step4_output": "Step 4 output",
        }

        # Load the Step 5 template
        template_name = "agentic_change_step5_docs_change_LLM"
        prompt_template = load_prompt_template(template_name)
        assert prompt_template is not None

        # Preprocess correctly - this is what the fix should do
        exclude_keys = list(context.keys())
        processed_template = preprocess(
            prompt_template,
            recursive=True,
            double_curly_brackets=True,  # CORRECT: Escapes literal braces
            exclude_keys=exclude_keys
        )

        # This should NOT raise KeyError
        try:
            formatted = processed_template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"Even with correct preprocessing, KeyError occurred: {e}\n"
                f"This suggests the fix implementation may have an issue."
            )

        # Verify context variables were substituted
        assert "https://github.com/test/repo/issues/448" in formatted
        assert "test/repo" in formatted

    def test_change_orchestrator_missing_preprocess_call(self):
        """
        CODE INSPECTION TEST: Verify the change orchestrator is missing the preprocess call.

        This test inspects the source code to confirm the bug exists.
        It should FAIL after the fix is applied (because the fix adds preprocess).
        """
        import pdd.agentic_change_orchestrator as change_orch

        source = inspect.getsource(change_orch)

        # Check if preprocess is imported
        has_preprocess_import = "from pdd.preprocess import preprocess" in source

        # Check if preprocess is called with double_curly_brackets=True
        has_double_curly_call = "double_curly_brackets=True" in source

        if has_preprocess_import and has_double_curly_call:
            # The fix has been applied - this is the expected state after fix
            pass
        else:
            # The bug is present - preprocess is not being used correctly
            pytest.fail(
                "BUG DETECTED (Issue #448): agentic_change_orchestrator.py is missing "
                "the preprocess() call with double_curly_brackets=True.\n\n"
                "Current state:\n"
                f"  - preprocess imported: {has_preprocess_import}\n"
                f"  - double_curly_brackets=True used: {has_double_curly_call}\n\n"
                "The fix requires:\n"
                "  1. Add: from pdd.preprocess import preprocess\n"
                "  2. Before format(), add:\n"
                "     exclude_keys = list(context.keys())\n"
                "     prompt_template = preprocess(prompt_template, recursive=True, "
                "double_curly_brackets=True, exclude_keys=exclude_keys)\n\n"
                "See agentic_architecture_orchestrator.py:299-302 for the correct pattern."
            )


class TestIssue448CompareOrchestrators:
    """
    Comparison tests between architecture and change orchestrators.

    The architecture orchestrator correctly uses preprocess() before format().
    These tests verify that pattern and check if the change orchestrator matches.
    """

    def test_architecture_orchestrator_has_correct_pattern(self):
        """Verify the architecture orchestrator has the correct preprocessing pattern."""
        import pdd.agentic_architecture_orchestrator as arch_orch

        source = inspect.getsource(arch_orch)

        # Verify the correct pattern exists
        assert "from pdd.preprocess import preprocess" in source, \
            "Architecture orchestrator should import preprocess"
        assert "double_curly_brackets=True" in source, \
            "Architecture orchestrator should use double_curly_brackets=True"
        assert "exclude_keys" in source, \
            "Architecture orchestrator should exclude context keys from escaping"

    def test_change_orchestrator_should_match_architecture_pattern(self):
        """
        Verify change orchestrator uses same pattern as architecture orchestrator.

        This test FAILS on buggy code and PASSES after the fix.
        """
        import pdd.agentic_change_orchestrator as change_orch
        import pdd.agentic_architecture_orchestrator as arch_orch

        change_source = inspect.getsource(change_orch)
        arch_source = inspect.getsource(arch_orch)

        # The architecture orchestrator definitely has this pattern
        assert "double_curly_brackets=True" in arch_source, \
            "Architecture orchestrator pattern check failed (test setup issue)"

        # The change orchestrator should have the same pattern
        if "double_curly_brackets=True" not in change_source:
            pytest.fail(
                "BUG (Issue #448): agentic_change_orchestrator.py does NOT use "
                "the same preprocessing pattern as agentic_architecture_orchestrator.py.\n\n"
                "The change orchestrator needs to add:\n"
                "  preprocess(prompt_template, recursive=True, double_curly_brackets=True, "
                "exclude_keys=exclude_keys)\n\n"
                "before calling prompt_template.format(**context)"
            )


class TestIssue448RegressionPrevention:
    """
    Regression prevention tests for Issue #448.

    These tests verify the conditions that trigger the bug are present.
    """

    def test_prompting_guide_contains_json_braces(self):
        """Verify docs/prompting_guide.md contains JSON that triggers the bug."""
        from pathlib import Path
        import pdd

        pdd_dir = Path(pdd.__file__).parent.parent
        prompting_guide = pdd_dir / "docs" / "prompting_guide.md"

        if not prompting_guide.exists():
            pytest.skip("docs/prompting_guide.md not found")

        content = prompting_guide.read_text()
        assert '{"url":' in content or '{"url"' in content, \
            "docs/prompting_guide.md should contain JSON with 'url' key"

    def test_step5_template_includes_prompting_guide(self):
        """Verify Step 5 template includes the prompting guide file."""
        from pathlib import Path
        import pdd

        pdd_dir = Path(pdd.__file__).parent
        template_path = pdd_dir / "prompts" / "agentic_change_step5_docs_change_LLM.prompt"

        if not template_path.exists():
            pytest.skip("Template file not found")

        content = template_path.read_text()
        assert "<include>" in content and "prompting_guide" in content, \
            "Step 5 template should include prompting_guide.md"

    def test_preprocess_expands_includes(self):
        """Verify that preprocess() expands <include> tags."""
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None

        # Raw template has <include> tags
        assert "<include>" in template, "Raw template should have <include> tags"

        # After preprocessing, includes should be expanded
        processed = preprocess(template, recursive=True, double_curly_brackets=False)
        assert "<include>" not in processed or len(processed) > len(template), \
            "Preprocessing should expand includes"


class TestIssue448OtherAffectedLocations:
    """
    Tests for other locations in agentic_change_orchestrator.py that may be affected.

    The root cause analysis identified format() calls at lines 713, 727, and 790
    that may also need the preprocessing fix.
    """

    def test_all_format_calls_should_be_preceded_by_preprocess(self):
        """
        Verify all format() calls on prompt templates have preprocess() before them.

        This test checks the source code structure to ensure the fix covers all
        locations where format() is called on templates.
        """
        import pdd.agentic_change_orchestrator as change_orch
        import re

        source = inspect.getsource(change_orch)

        # Find all lines that call format(**context) on templates
        # Pattern matches: something.format(**context) or something.format(**something)
        format_calls = re.findall(r'\w+\.format\(\*\*\w+\)', source)

        if not format_calls:
            pytest.skip("No format() calls found in source")

        # After the fix, preprocess should be used with double_curly_brackets=True
        if "double_curly_brackets=True" not in source:
            pytest.fail(
                f"BUG (Issue #448): Found {len(format_calls)} format() calls but no "
                f"preprocess(..., double_curly_brackets=True) call.\n\n"
                f"All template format() calls need preprocessing:\n"
                f"  - Line 598 (main step loop)\n"
                f"  - Line 713 (step 11)\n"
                f"  - Line 727 (step 12)\n"
                f"  - Line 790 (step 13)"
            )
