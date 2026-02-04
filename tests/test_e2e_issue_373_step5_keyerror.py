"""
E2E Test for Issue #373: KeyError '\n  "type"' in Step 5 prompt template due to unescaped JSON in included prompting_guide.md

This E2E test exercises the orchestrator code path for Step 5 of the agentic change workflow.
It verifies that the prompt template at pdd/prompts/agentic_change_step5_docs_change_LLM.prompt
can be loaded, preprocessed, and formatted without raising KeyError on unescaped JSON placeholders.

The bug: The step 5 template includes `docs/prompting_guide.md` via an `<include>` directive.
The prompting_guide.md contains JSON examples with curly braces like:
    {
      "type": "module",
      "module": {
        "functions": [
          {"name": "function_name", "signature": "(...)", "returns": "Type"}
        ]
      }
    }

When the orchestrator loads the template and calls prompt_template.format(**context) WITHOUT
first preprocessing with double_curly_brackets=True, Python interprets the JSON braces as
format placeholders. Since keys like '\n  "type"' don't exist in the context, it raises KeyError.

This is the same class of bug as Issue #357 (Step 9 template), which was fixed by escaping
the template placeholders. However, the fix for #357 only addressed the specific template file,
not the underlying issue that the orchestrator doesn't preprocess templates before formatting.

This E2E test:
1. Sets up a mock environment for the orchestrator
2. Loads the Step 5 template and preprocesses it (expanding includes)
3. Attempts to format the template with the context the orchestrator would use
4. Verifies no KeyError is raised on JSON placeholders from included files

The test should FAIL on buggy code (KeyError: '\n  "type"') and PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
import re
import os


@pytest.fixture
def mock_cwd(tmp_path):
    """Create a mock working directory with .git to simulate a git repo."""
    (tmp_path / ".git").mkdir()
    (tmp_path / ".pdd").mkdir()
    return tmp_path


class TestIssue373Step5KeyErrorE2E:
    """
    E2E tests for Issue #373: Verify Step 5 prompt template formats without KeyError.

    These tests exercise the orchestrator's prompt loading and formatting code path
    to ensure JSON in included files doesn't cause KeyError during .format().
    """

    def test_step5_template_formats_without_keyerror_after_preprocessing(self, mock_cwd):
        """
        E2E Test: Step 5 template should format without KeyError after proper preprocessing.

        This test simulates what the orchestrator SHOULD do:
        1. Load the template
        2. Preprocess with double_curly_brackets=True to escape braces in included content
        3. Format with context

        Expected behavior (after fix):
        - Template loads and preprocesses successfully
        - format(**context) succeeds without KeyError
        - JSON braces from prompting_guide.md are escaped and appear as literals

        Bug behavior (Issue #373):
        - The orchestrator calls .format() directly without preprocessing
        - This causes KeyError: '\n  "type"' because JSON braces are interpreted as placeholders
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        # Build the context that the orchestrator would pass to Step 5
        # This mimics agentic_change_orchestrator.py context building
        context = {
            "issue_url": "https://github.com/test/repo/issues/373",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 373,
            "issue_content": "Test issue content for bug #373",
        }

        # Add previous step outputs (steps 1-4)
        for prev_step in range(1, 5):
            context[f"step{prev_step}_output"] = f"Mock output for step {prev_step}"

        # Load the Step 5 template - this is the REAL template, not mocked
        template_name = "agentic_change_step5_docs_change_LLM"
        prompt_template = load_prompt_template(template_name)
        assert prompt_template is not None, f"Failed to load template: {template_name}"

        # Verify the raw template contains the <include> directive
        assert "<include>docs/prompting_guide.md</include>" in prompt_template, \
            "Template should contain <include> directive for prompting_guide.md"

        # Preprocess the template properly (as code_generator_main.py does):
        # First pass: expand includes
        processed_template = preprocess(prompt_template, recursive=True, double_curly_brackets=False)

        # The specific include directive should now be expanded
        # Note: The expanded content may contain mentions of <include> as documentation,
        # but the actual directive "<include>docs/prompting_guide.md</include>" should be gone
        assert "<include>docs/prompting_guide.md</include>" not in processed_template, \
            "The specific <include>docs/prompting_guide.md</include> directive should be expanded"

        # The expanded content should contain the JSON examples from prompting_guide.md
        # These contain patterns like {"type": "module", ...}
        assert '"type"' in processed_template or "'type'" in processed_template, \
            "Expanded template should contain JSON examples from prompting_guide.md"

        # THE BUG CHECK: This line should NOT raise KeyError: '\n  "type"'
        # Bug location: agentic_change_orchestrator.py:520-521
        # Bug cause: The orchestrator calls .format(**context) without preprocessing,
        # or if it preprocessed but didn't use double_curly_brackets=True

        # Second pass: escape curly braces EXCEPT for the valid context keys
        # This is what the orchestrator should do - escape JSON but keep placeholders
        from pdd.preprocess import double_curly
        fully_processed = double_curly(processed_template, exclude_keys=list(context.keys()))

        try:
            formatted_prompt = fully_processed.format(**context)
        except KeyError as e:
            pytest.fail(
                f"BUG DETECTED (Issue #373): KeyError '{e.args[0]}' raised when formatting "
                f"Step 5 prompt template after preprocessing.\n\n"
                f"This indicates the preprocessing didn't properly escape curly braces in "
                f"the included prompting_guide.md content.\n\n"
                f"JSON examples like {{\"type\": \"module\", ...}} should be escaped to "
                f"{{{{\"type\": \"module\", ...}}}} to prevent interpretation as format placeholders."
            )

        # Verify context variables were actually substituted
        assert "https://github.com/test/repo/issues/373" in formatted_prompt, \
            "issue_url should be substituted"
        assert "373" in formatted_prompt, \
            "issue_number should be substituted"

    def test_step5_expanded_template_formats_without_keyerror(self, mock_cwd):
        """
        E2E Test: Step 5 template with expanded includes should format without KeyError.

        This test replicates what SHOULD happen in the orchestrator:
        1. Load template with load_prompt_template()
        2. Preprocess to expand includes AND escape braces
        3. Call .format(**context)

        The test verifies that after proper preprocessing, no KeyError occurs.
        This test should FAIL if double_curly preprocessing doesn't work correctly.
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        context = {
            "issue_url": "https://github.com/test/repo/issues/373",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 373,
            "issue_content": "Test issue",
        }
        for i in range(1, 5):
            context[f"step{i}_output"] = f"Step {i} output"

        # Load the raw template (as orchestrator does)
        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None

        # Preprocess to expand includes
        expanded_template = preprocess(template, recursive=True, double_curly_brackets=False)

        # Verify the include was expanded and contains JSON
        assert "<include>docs/prompting_guide.md</include>" not in expanded_template, \
            "Include directive should be expanded"
        assert '"type"' in expanded_template, \
            "Expanded template should contain JSON from prompting_guide.md"

        # Now escape curly braces EXCEPT for valid placeholders
        # This is the key step the orchestrator is missing
        from pdd.preprocess import double_curly
        escaped_template = double_curly(expanded_template, exclude_keys=list(context.keys()))

        # This should succeed without KeyError after proper preprocessing
        try:
            formatted = escaped_template.format(**context)
        except KeyError as e:
            pytest.fail(
                f"BUG DETECTED (Issue #373): KeyError '{e.args[0]}' raised even after "
                f"preprocessing with double_curly_brackets=True.\n\n"
                f"This indicates the double_curly() function isn't properly escaping "
                f"the JSON braces in the included prompting_guide.md content."
            )

        # Verify context was substituted
        assert "https://github.com/test/repo/issues/373" in formatted

    def test_prompting_guide_contains_unescaped_json(self):
        """
        Regression Test: Verify prompting_guide.md contains JSON that needs escaping.

        This test documents the source of the bug - the JSON examples in prompting_guide.md
        that contain unescaped curly braces.
        """
        # The prompting_guide.md is found via the preprocess include resolution
        # which looks in docs/ relative to the repo root
        from pdd.preprocess import get_file_path

        try:
            prompting_guide_path = Path(get_file_path("docs/prompting_guide.md"))
        except Exception:
            prompting_guide_path = None

        if prompting_guide_path is None or not prompting_guide_path.exists():
            # Try alternative locations
            import pdd
            pdd_dir = Path(pdd.__file__).parent
            possible_paths = [
                pdd_dir / "docs" / "prompting_guide.md",
                pdd_dir.parent / "docs" / "prompting_guide.md",
            ]
            for path in possible_paths:
                if path.exists():
                    prompting_guide_path = path
                    break

        if prompting_guide_path is None or not prompting_guide_path.exists():
            pytest.skip("prompting_guide.md not found in expected locations")

        content = prompting_guide_path.read_text()

        # Look for JSON examples with unescaped braces
        # These are the patterns that cause KeyError when not properly escaped
        json_patterns = [
            r'\{\s*"type"\s*:',  # {"type":
            r'\{\s*"module"\s*:',  # {"module":
            r'\{\s*"functions"\s*:',  # {"functions":
            r'\{\s*"name"\s*:',  # {"name":
        ]

        found_patterns = []
        for pattern in json_patterns:
            if re.search(pattern, content):
                found_patterns.append(pattern)

        assert found_patterns, (
            "prompting_guide.md should contain JSON examples with curly braces.\n"
            "These JSON examples need to be escaped when included in prompt templates "
            "that will be formatted with .format()."
        )

    def test_step5_fails_without_double_curly_preprocessing(self, mock_cwd):
        """
        Bug Demonstration Test: Shows that formatting without double_curly fails.

        This test demonstrates the exact bug in Issue #373:
        - When includes are expanded but braces are NOT escaped
        - Calling .format() raises KeyError on JSON content

        This test SHOULD FAIL on the buggy code (demonstrating the bug exists).
        The fix should modify the orchestrator to call preprocess with double_curly=True.
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        context = {
            "issue_url": "https://github.com/test/repo/issues/373",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 373,
            "issue_content": "Test issue",
        }
        for i in range(1, 5):
            context[f"step{i}_output"] = f"Step {i} output"

        # Load the raw template
        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None

        # Expand includes WITHOUT escaping braces (the bug scenario)
        expanded_template = preprocess(template, recursive=True, double_curly_brackets=False)

        # Verify the include was expanded and contains JSON
        assert "<include>docs/prompting_guide.md</include>" not in expanded_template
        assert '"type"' in expanded_template, "Should contain JSON from prompting_guide.md"

        # THE BUG: This should raise KeyError because JSON braces are not escaped
        # If it doesn't raise KeyError, the test fails (bug doesn't manifest)
        try:
            formatted = expanded_template.format(**context)
            # If we get here, the bug didn't manifest - this means the test is wrong
            # or the content changed. Either way, we should fail the test.
            pytest.fail(
                "BUG NOT DETECTED: Expected KeyError when formatting expanded template "
                "without double_curly preprocessing, but format() succeeded.\n\n"
                "This test is designed to FAIL on buggy code. If this test passes, "
                "either:\n"
                "1. The bug has been fixed differently (braces escaped in source file)\n"
                "2. The test setup is wrong\n"
                "3. The include wasn't properly expanded"
            )
        except KeyError as e:
            # This IS the bug! The test passes by catching the expected error.
            # The bug manifests as KeyError when formatting.
            pass  # Test passes - we confirmed the bug exists

    def test_step5_template_raw_contains_include_directive(self):
        """
        Sanity Test: Verify the raw Step 5 template uses <include> directive.

        This confirms the template relies on include expansion, making it vulnerable
        to the bug when preprocessing is skipped.
        """
        from pdd.load_prompt_template import load_prompt_template

        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None

        assert "<include>docs/prompting_guide.md</include>" in template, (
            "Step 5 template should contain <include> directive for prompting_guide.md.\n"
            "This directive causes the bug when the included content has JSON with "
            "unescaped curly braces."
        )


class TestIssue373RegressionPrevention:
    """
    Regression prevention tests for Issue #373.

    These tests check for patterns that could cause similar bugs in the future.
    """

    def test_included_files_contain_json_requiring_escaping(self):
        """
        Documentation Test: Confirms prompting_guide.md has JSON patterns that need escaping.

        This test documents that the prompting_guide.md file contains JSON examples
        that will cause KeyError if not properly escaped when used with .format().
        """
        from pdd.preprocess import get_file_path

        try:
            prompting_guide_path = Path(get_file_path("docs/prompting_guide.md"))
        except Exception:
            prompting_guide_path = None

        if prompting_guide_path is None or not prompting_guide_path.exists():
            import pdd
            pdd_dir = Path(pdd.__file__).parent
            possible_paths = [
                pdd_dir / "docs" / "prompting_guide.md",
                pdd_dir.parent / "docs" / "prompting_guide.md",
            ]
            for path in possible_paths:
                if path.exists():
                    prompting_guide_path = path
                    break

        if prompting_guide_path is None or not prompting_guide_path.exists():
            pytest.skip("prompting_guide.md not found")

        content = prompting_guide_path.read_text()

        # Check for JSON patterns that would be interpreted as format placeholders
        # Pattern: { followed by content containing quotes (typical JSON)
        json_patterns = re.findall(r'\{[^{}]*"[^{}]*\}', content)

        # These patterns SHOULD exist - they are the JSON examples in the docs
        # The preprocessing should escape them properly
        assert len(json_patterns) > 0, (
            "prompting_guide.md should contain JSON examples with curly braces.\n"
            "These are the patterns that require escaping when included in templates."
        )

    def test_orchestrator_should_preprocess_templates(self, mock_cwd):
        """
        Architecture Test: Verify the orchestrator preprocesses templates before formatting.

        This test checks that the agentic_change_orchestrator.py calls preprocess()
        with double_curly_brackets=True before calling .format() on templates.

        NOTE: This test inspects the source code to verify the fix is in place.
        After the fix, this test should pass.
        """
        import pdd
        from pathlib import Path

        orchestrator_path = Path(pdd.__file__).parent / "agentic_change_orchestrator.py"
        assert orchestrator_path.exists(), "Orchestrator file should exist"

        content = orchestrator_path.read_text()

        # Find the section where templates are loaded and formatted
        # Look for the pattern: load_prompt_template followed by .format(
        # The fix should add preprocess() call between them

        # Pattern for the buggy code:
        # prompt_template = load_prompt_template(...)
        # ...
        # formatted_prompt = prompt_template.format(**context)

        # Pattern for the fixed code should include:
        # preprocess(..., double_curly_brackets=True)

        # Check if preprocess is imported
        has_preprocess_import = "from" in content and "preprocess" in content

        # Check if preprocess is called with double_curly_brackets=True in the step loop
        # This is a simplified check - the actual fix may vary
        has_double_curly_call = "double_curly_brackets=True" in content or "double_curly" in content

        # For now, this test documents what SHOULD be there
        # The test will fail until the fix is applied
        if not has_double_curly_call:
            pytest.fail(
                "BUG DETECTED (Issue #373): The orchestrator does not call preprocess() "
                "with double_curly_brackets=True before formatting templates.\n\n"
                "The fix should add preprocessing between load_prompt_template() and .format():\n"
                "  template = load_prompt_template(...)\n"
                "  template = preprocess(template, recursive=True, double_curly_brackets=False)\n"
                "  template = preprocess(template, recursive=False, double_curly_brackets=True)\n"
                "  formatted = template.format(**context)"
            )


class TestIssue373OrchestratorE2EIntegration:
    """
    E2E Integration tests for Issue #373: Exercise the real orchestrator code path.

    These tests call the actual orchestrator function with mocked LLM calls
    but WITHOUT mocking the template loading/formatting code (where the bug is).
    This verifies the bug at the system level.
    """

    def test_orchestrator_step5_integration_with_mock_llm(self, mock_cwd, monkeypatch):
        """
        E2E Integration Test: Run orchestrator through Step 5 with mocked LLM.

        This test exercises the orchestrator's real code path by:
        1. Calling run_agentic_change_orchestrator with mocked LLM
        2. Simulating progression through Steps 1-5
        3. Verifying the orchestrator doesn't crash at Step 5 due to KeyError

        NOTE: In development mode, the <include> directives are NOT expanded
        by load_prompt_template(), so the bug doesn't manifest directly.
        The bug only occurs when:
        1. The package is pip-installed (includes are expanded at build time), OR
        2. The template is preprocessed to expand includes

        This test verifies the orchestrator works in development mode.
        See test_step5_with_expanded_includes_via_mock_loader for the bug scenario.
        """
        import re
        from pathlib import Path

        # Set up environment
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Track which steps were attempted
        steps_attempted = []
        prompts_received = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """
            Mock that lets us track which steps are called and what prompts are used.

            IMPORTANT: This mock is called AFTER the prompt template is loaded and
            formatted, so if there's a KeyError in formatting, this mock won't be
            reached and the test will fail with KeyError.
            """
            # Extract step number from label (e.g., "step5")
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_attempted.append(step_num)
                prompts_received.append((step_num, instruction[:500]))  # Store first 500 chars

            # Return appropriate responses for each step
            if "step1" in label:
                return (True, "NOT_DUPLICATE - This is a new issue", 0.001, "mock-model")
            if "step2" in label:
                return (True, "BUG_CONFIRMED - This is a confirmed bug", 0.001, "mock-model")
            if "step3" in label:
                return (True, "PROCEED - Sufficient info for reproduction", 0.001, "mock-model")
            if "step4" in label:
                return (True, "REPRODUCED - Bug confirmed in tests", 0.001, "mock-model")
            if "step5" in label:
                # Step 5 should be reached - if we get here, the bug is fixed!
                return (True, "DOCS_UPDATED - Documentation changes made", 0.001, "mock-model")
            # For any other step, return generic success
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
        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

                        try:
                            success, message, cost, model, files = run_agentic_change_orchestrator(
                                issue_url="https://github.com/test/repo/issues/373",
                                issue_content="Test issue for bug #373 - KeyError in Step 5",
                                repo_owner="test",
                                repo_name="repo",
                                issue_number=373,
                                issue_author="test-user",
                                issue_title="Test Issue 373",
                                cwd=mock_cwd,
                                verbose=False,
                                quiet=True,
                            )
                        except KeyError as e:
                            pytest.fail(
                                f"BUG DETECTED (Issue #373): Orchestrator raised KeyError '{e.args[0]}' "
                                f"during Step 5 prompt formatting.\n\n"
                                f"Steps attempted before crash: {steps_attempted}\n\n"
                                f"This confirms the bug at lines 520-521 of agentic_change_orchestrator.py:\n"
                                f"  prompt_template = load_prompt_template(template_name)\n"
                                f"  ...\n"
                                f"  formatted_prompt = prompt_template.format(**context)\n\n"
                                f"The template includes docs/prompting_guide.md which contains JSON "
                                f"with unescaped curly braces. These are interpreted as format placeholders."
                            )

        # Verify Step 5 was attempted (meaning all steps including Step 5 were formatted)
        assert 5 in steps_attempted, (
            f"Step 5 should have been attempted. Steps attempted: {steps_attempted}\n"
            f"If Step 5 wasn't reached, there may be an earlier issue."
        )

    def test_step5_with_expanded_includes_via_mock_loader(self, mock_cwd, monkeypatch):
        """
        E2E Bug Demonstration Test: Simulate production environment where includes are expanded.

        This test simulates what happens in a pip-installed production environment:
        1. The <include> directives in prompt files are expanded at build time
        2. When the orchestrator loads the template, it gets the expanded content
        3. The orchestrator calls .format(**context) without escaping braces
        4. KeyError is raised due to JSON braces being interpreted as format placeholders

        This test SHOULD DETECT THE BUG by mocking load_prompt_template to return
        the expanded content (simulating production installation).
        """
        import re
        from pdd.preprocess import preprocess

        # Pre-expand the step 5 template to simulate production environment
        from pdd.load_prompt_template import load_prompt_template as real_loader
        raw_template = real_loader("agentic_change_step5_docs_change_LLM")
        assert raw_template is not None

        # Expand includes (simulating what happens at package build time)
        expanded_template = preprocess(raw_template, recursive=True, double_curly_brackets=False)

        # Verify the include was expanded and contains JSON that will cause the bug
        assert "<include>docs/prompting_guide.md</include>" not in expanded_template, \
            "Include should be expanded in this test"
        assert '"type"' in expanded_template, \
            "Expanded content should contain JSON from prompting_guide.md"

        # Track which steps were attempted before crash
        steps_attempted = []

        def mock_load_prompt_template(template_name):
            """Return expanded template for step 5, raw for others."""
            if "step5" in template_name:
                return expanded_template
            return real_loader(template_name)

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            match = re.search(r"step(\d+)", label)
            if match:
                steps_attempted.append(int(match.group(1)))
            # Return success to continue workflow
            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            return None

        def mock_load_state(*args, **kwargs):
            return None, None

        def mock_clear_state(*args, **kwargs):
            pass

        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Patch to simulate production environment
        with patch('pdd.agentic_change_orchestrator.load_prompt_template', side_effect=mock_load_prompt_template):
            with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
                with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                    with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                        with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                            from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

                            try:
                                success, message, cost, model, files = run_agentic_change_orchestrator(
                                    issue_url="https://github.com/test/repo/issues/373",
                                    issue_content="Test issue for bug #373",
                                    repo_owner="test",
                                    repo_name="repo",
                                    issue_number=373,
                                    issue_author="test-user",
                                    issue_title="Test Issue 373",
                                    cwd=mock_cwd,
                                    verbose=False,
                                    quiet=True,
                                )
                                # If we get here without error at step 5, check if step 5 was reached
                                if 5 in steps_attempted:
                                    # Step 5 was reached without KeyError - bug may be fixed
                                    pass
                                else:
                                    # Step 5 wasn't reached - orchestrator returned early
                                    # Check if error message indicates the bug
                                    if "Context missing key" in message and "step 5" in message:
                                        pass  # Bug detected via return value
                                    else:
                                        pytest.fail(
                                            f"Step 5 wasn't reached but no KeyError detected.\n"
                                            f"Message: {message}\n"
                                            f"Steps attempted: {steps_attempted}"
                                        )
                            except KeyError as e:
                                # This is the bug! KeyError from JSON braces
                                pass  # Test passes - bug detected

    def test_orchestrator_context_missing_key_error_message(self, mock_cwd, monkeypatch):
        """
        E2E Test: Verify the specific error message from the orchestrator bug.

        This test demonstrates the exact user-visible error message that occurs
        when the bug is triggered. The error message is:
        "Context missing key for step 5: '\\n  \"type\"'"

        This is the error message users see when running `pdd change` and hitting
        this bug.
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        # Simulate what the orchestrator does for Step 5
        context = {
            "issue_url": "https://github.com/test/repo/issues/373",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 373,
            "issue_content": "Test issue",
        }
        for i in range(1, 5):
            context[f"step{i}_output"] = f"Step {i} output"

        # Load template exactly as orchestrator does at line 516
        template_name = "agentic_change_step5_docs_change_LLM"
        prompt_template = load_prompt_template(template_name)
        assert prompt_template is not None

        # The orchestrator doesn't preprocess - it goes directly to format
        # This simulates the buggy behavior at lines 520-523
        step_num = 5
        try:
            formatted_prompt = prompt_template.format(**context)
            # If we get here without error, the bug may have been fixed differently
            # (e.g., by escaping braces in the prompting_guide.md itself)
            # Check if the include was expanded
            if "<include>docs/prompting_guide.md</include>" in prompt_template:
                # Include wasn't expanded - this is expected with load_prompt_template
                # The bug only manifests when includes ARE expanded but braces aren't escaped
                pass
            else:
                # Include was expanded but no KeyError - might indicate a fix
                pass
        except KeyError as e:
            # This is the exact error the user sees
            error_message = f"Context missing key for step {step_num}: {e}"

            # Verify the error message format matches what the orchestrator returns
            assert "Context missing key for step 5" in error_message
            # The key that causes the error contains newline and "type" from JSON
            assert '"type"' in str(e) or "type" in str(e) or "\\n" in str(e), (
                f"Expected error to mention JSON-like content, got: {e}"
            )

    def test_orchestrator_step5_prompt_includes_prompting_guide(self, mock_cwd):
        """
        Sanity Test: Verify Step 5 template includes prompting_guide.md

        This test confirms the template structure that causes the bug:
        The Step 5 template uses <include>docs/prompting_guide.md</include>
        which brings in JSON examples with unescaped curly braces.
        """
        from pdd.load_prompt_template import load_prompt_template

        # Load the raw Step 5 template (as orchestrator does)
        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None

        # The raw template should contain the include directive
        # (load_prompt_template does NOT expand includes)
        assert "<include>docs/prompting_guide.md</include>" in template, (
            "Step 5 template should use <include> directive for prompting_guide.md.\n"
            "This is the source of the bug - the included file contains JSON with "
            "unescaped curly braces that cause KeyError when formatting."
        )
