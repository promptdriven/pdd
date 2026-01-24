"""
E2E Test for Issue #357: KeyError 'N' in step 9 prompt template due to unescaped format placeholders

This E2E test exercises the full orchestrator code path for Step 9 of the agentic e2e fix workflow.
It verifies that the prompt template at pdd/prompts/agentic_e2e_fix_step9_verify_all_LLM.prompt
can be loaded and formatted without raising KeyError on unescaped placeholders.

The bug: Lines 126-127 of the Step 9 template use single braces {N}/{M} instead of double braces
{{N}}/{{M}} in the "MAX_CYCLES_REACHED" section:

    - Unit tests: {N}/{M} pass ({K} still failing)   <- BUG: unescaped
    - E2E tests: {N}/{M} pass ({K} still failing)    <- BUG: unescaped

When the orchestrator calls prompt_template.format(**context), Python interprets {N}, {M}, {K}
as variable substitutions. Since these keys don't exist in the context dictionary, it raises
KeyError: 'N'.

This is inconsistent with other sections in the same file that correctly use double braces:
- Lines 84-85: {{N}}/{{M}} pass (correct)
- Lines 104-105: {{N}}/{{M}} pass ({{K}} still failing) (correct)

This E2E test:
1. Sets up a mock environment for the orchestrator
2. Simulates reaching Step 9 with all prerequisite step outputs
3. Calls the orchestrator's prompt loading and formatting code
4. Verifies no KeyError is raised on the template placeholders

The test should FAIL on buggy code (KeyError: 'N') and PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock, AsyncMock
import tempfile


@pytest.fixture
def mock_cwd(tmp_path):
    """Create a mock working directory with .git to simulate a git repo."""
    (tmp_path / ".git").mkdir()
    (tmp_path / ".pdd").mkdir()
    return tmp_path


class TestIssue357Step9KeyErrorE2E:
    """
    E2E tests for Issue #357: Verify Step 9 prompt template formats without KeyError.

    These tests exercise the orchestrator's prompt loading and formatting code path
    without mocking the buggy component (the template and its formatting).
    """

    def test_step9_orchestrator_formats_prompt_without_keyerror(self, mock_cwd):
        """
        E2E Test: Orchestrator Step 9 should load and format prompt without KeyError.

        This test exercises the actual orchestrator code that loads the Step 9 template
        and formats it with context. The bug at lines 126-127 causes KeyError: 'N'
        when formatting.

        Expected behavior (after fix):
        - Prompt loads successfully
        - format(**context) succeeds without KeyError
        - Escaped placeholders {{N}}/{{M}} become literal {N}/{M} in output

        Bug behavior (Issue #357):
        - KeyError: 'N' is raised at line 405 of agentic_e2e_fix_orchestrator.py
        - The workflow fails with "Fatal error: 'N'"
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.agentic_e2e_fix_orchestrator import STEP_NAMES

        # Build the context that the orchestrator would pass to Step 9
        # This mimics agentic_e2e_fix_orchestrator.py lines 376-403
        context = {
            "issue_url": "https://github.com/test/repo/issues/357",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 357,
            "cycle_number": 5,  # Max cycles to trigger MAX_CYCLES_REACHED section
            "max_cycles": 5,
            "issue_content": "Test issue content for bug #357",
            "protect_tests": "false",
            "protect_tests_flag": "",
            "next_cycle": 6,  # cycle_number + 1
        }

        # Add all previous step outputs (steps 1-8)
        for prev_step in range(1, 9):
            context[f"step{prev_step}_output"] = f"Mock output for step {prev_step}"

        # Add derived variables that Step 9 might need
        context["dev_units_identified"] = "test_module"

        # Load the Step 9 template - this is the REAL template, not mocked
        step_num = 9
        step_name = STEP_NAMES[step_num]
        template_name = f"agentic_e2e_fix_step{step_num}_{step_name}_LLM"

        prompt_template = load_prompt_template(template_name)
        assert prompt_template is not None, f"Failed to load template: {template_name}"

        # THE BUG CHECK: This line should NOT raise KeyError: 'N'
        # Bug location: agentic_e2e_fix_orchestrator.py:405
        # Bug cause: Lines 126-127 of the template have {N}/{M} instead of {{N}}/{{M}}
        try:
            formatted_prompt = prompt_template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"BUG DETECTED (Issue #357): KeyError '{e.args[0]}' raised when formatting "
                f"Step 9 prompt template.\n\n"
                f"This confirms the bug at lines 126-127 of {template_name}.prompt:\n"
                f"  - Unit tests: {{N}}/{{M}} pass ({{K}} still failing)  <- should be double braces\n"
                f"  - E2E tests: {{N}}/{{M}} pass ({{K}} still failing)   <- should be double braces\n\n"
                f"The orchestrator context does not include 'N', 'M', or 'K' keys because they "
                f"are meant to be literal placeholders in the output, not variables to substitute."
            )

        # Verify the formatted prompt contains the expected literal placeholders
        # After proper escaping, {{N}}/{{M}} should become {N}/{M} in the output
        assert "{N}" in formatted_prompt, \
            "Escaped {{N}} should become literal {N} in formatted output"
        assert "{M}" in formatted_prompt, \
            "Escaped {{M}} should become literal {M} in formatted output"
        assert "{K}" in formatted_prompt, \
            "Escaped {{K}} should become literal {K} in formatted output"

        # Verify context variables were actually substituted
        assert "https://github.com/test/repo/issues/357" in formatted_prompt, \
            "issue_url should be substituted"
        assert "357" in formatted_prompt, \
            "issue_number should be substituted"
        assert "5/5" in formatted_prompt or "5}/{max_cycles}" not in formatted_prompt, \
            "cycle_number/max_cycles should be substituted"

    def test_step9_all_template_sections_format_correctly(self, mock_cwd):
        """
        E2E Test: All three output sections of Step 9 template should format correctly.

        The template has three sections with example output formats:
        1. "ALL_TESTS_PASS" section (lines 84-85) - correctly uses {{N}}/{{M}}
        2. "CONTINUE_CYCLE" section (lines 104-105) - correctly uses {{N}}/{{M}}
        3. "MAX_CYCLES_REACHED" section (lines 126-127) - BUG: uses {N}/{M}

        This test verifies all sections can be formatted without error.
        """
        from pdd.load_prompt_template import load_prompt_template

        context = {
            "issue_url": "https://github.com/test/repo/issues/357",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 357,
            "cycle_number": 3,
            "max_cycles": 5,
            "issue_content": "Test issue",
            "protect_tests": "false",
            "protect_tests_flag": "",
            "next_cycle": 4,
        }

        for i in range(1, 9):
            context[f"step{i}_output"] = f"Step {i} output"

        template = load_prompt_template("agentic_e2e_fix_step9_verify_all_LLM")
        assert template is not None

        # This should NOT raise KeyError
        try:
            formatted = template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"BUG DETECTED (Issue #357): KeyError '{e.args[0]}' during formatting.\n"
                f"One of the template sections has unescaped format placeholders."
            )

        # Count occurrences of {N}/{M} pattern (literal, after formatting)
        # All three sections should have these patterns after proper escaping
        n_m_count = formatted.count("{N}/{M}")
        assert n_m_count >= 2, (
            f"Expected at least 2 occurrences of '{{N}}/{{M}}' pattern in formatted output "
            f"(from ALL_TESTS_PASS and CONTINUE_CYCLE sections), found {n_m_count}.\n"
            f"This may indicate the bug where unescaped placeholders cause KeyError."
        )

    def test_orchestrator_step9_integration_with_mock_llm(self, mock_cwd, monkeypatch):
        """
        E2E Integration Test: Run orchestrator through Step 9 with mocked LLM.

        This test exercises more of the orchestrator code path by:
        1. Calling run_agentic_e2e_fix_orchestrator with mocked LLM
        2. Simulating progression through all 9 steps
        3. Verifying the orchestrator doesn't crash at Step 9 due to KeyError

        Note: We mock run_agentic_task to avoid actual LLM calls, but the prompt
        loading and formatting code (where the bug is) is NOT mocked.
        """
        import sys
        from pathlib import Path

        # Set up environment
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Track which steps were attempted
        steps_attempted = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """
            Mock that lets us track which steps are called and what prompts are used.

            IMPORTANT: This mock is called AFTER the prompt template is loaded and
            formatted, so if there's a KeyError in formatting, this mock won't be
            reached and the test will fail with KeyError.
            """
            # Extract step number from label (e.g., "cycle1_step9")
            import re
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_attempted.append(step_num)

            # Return success to allow workflow to continue
            # For Step 9, return MAX_CYCLES_REACHED to end the workflow
            if "step9" in label:
                return (True, "MAX_CYCLES_REACHED - tests still failing", 0.001, "mock-model")
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

        # Patch the LLM task runner and state management
        with patch('pdd.agentic_e2e_fix_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_e2e_fix_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_e2e_fix_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_e2e_fix_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

                        try:
                            success, message, cost, model, files = run_agentic_e2e_fix_orchestrator(
                                issue_url="https://github.com/test/repo/issues/357",
                                issue_content="Test issue for bug #357",
                                repo_owner="test",
                                repo_name="repo",
                                issue_number=357,
                                issue_author="test-user",
                                issue_title="Test Issue 357",
                                cwd=mock_cwd,
                                max_cycles=1,  # Single cycle to reach Step 9 quickly
                                resume=False,
                                verbose=False,
                                quiet=True,
                                use_github_state=False,
                                protect_tests=False
                            )
                        except KeyError as e:
                            pytest.fail(
                                f"BUG DETECTED (Issue #357): Orchestrator raised KeyError '{e.args[0]}' "
                                f"during Step 9 prompt formatting.\n\n"
                                f"Steps attempted before crash: {steps_attempted}\n\n"
                                f"This confirms the bug at lines 126-127 of the Step 9 template."
                            )

        # Verify Step 9 was attempted (meaning all steps including Step 9 were formatted)
        assert 9 in steps_attempted, (
            f"Step 9 should have been attempted. Steps attempted: {steps_attempted}\n"
            f"If Step 9 wasn't reached, there may be an earlier issue."
        )


class TestIssue357RegressionPrevention:
    """
    Regression prevention tests for Issue #357.

    These tests check for the specific pattern that causes the bug:
    unescaped format placeholders in prompt template example sections.
    """

    def test_step9_template_has_consistent_escaping(self):
        """
        Regression Test: All example placeholder patterns in Step 9 should use double braces.

        This test scans the raw template content (before formatting) to verify
        that all instances of patterns like {N}/{M} are properly escaped as {{N}}/{{M}}.
        """
        from pdd.load_prompt_template import load_prompt_template
        import re

        # Load raw template content
        template = load_prompt_template("agentic_e2e_fix_step9_verify_all_LLM")
        assert template is not None

        # Find all single-brace patterns that look like example placeholders
        # We're looking for {N}, {M}, {K} etc. that should be {{N}}, {{M}}, {{K}}
        # Note: We need to check the RAW template before formatting

        # Get the raw template string from the module
        from pathlib import Path
        import pdd
        pdd_dir = Path(pdd.__file__).parent
        template_path = pdd_dir / "prompts" / "agentic_e2e_fix_step9_verify_all_LLM.prompt"

        raw_content = template_path.read_text()

        # Pattern to find single-braced uppercase letters (likely example placeholders)
        # This will match {N}, {M}, {K} but NOT {{N}}, {{M}}, {{K}}
        # The negative lookbehind (?<!{) and negative lookahead (?!}) ensure we don't match double braces
        single_brace_pattern = r'(?<!\{)\{([A-Z])\}(?!\})'

        matches = re.findall(single_brace_pattern, raw_content)

        if matches:
            # Find the line numbers where these occur
            lines_with_bugs = []
            for i, line in enumerate(raw_content.split('\n'), 1):
                if re.search(single_brace_pattern, line):
                    lines_with_bugs.append((i, line.strip()))

            pytest.fail(
                f"BUG DETECTED (Issue #357): Found unescaped single-brace placeholders in template.\n\n"
                f"Unescaped placeholders found: {set(matches)}\n\n"
                f"Lines with bugs:\n" +
                "\n".join(f"  Line {num}: {line}" for num, line in lines_with_bugs) +
                f"\n\nThese should use double braces (e.g., {{{{N}}}}/{{{{M}}}}) to escape them."
            )
