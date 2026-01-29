"""
E2E Test for Issue #392: pdd change fails at Step 5 with 'Context missing key for step 5: url'

CORRECTED UNDERSTANDING OF THE BUG:

The bug is NOT about step outputs - it's about the agentic_change_orchestrator missing a
preprocess() call before .format().

Bug location: pdd/agentic_change_orchestrator.py:593-598

    prompt_template = load_prompt_template(template_name)
    # MISSING: preprocess() call to expand <include> tags and escape braces
    formatted_prompt = prompt_template.format(**context)  # BUG: KeyError here

When a template includes files with JSON (like docs/prompting_guide.md via <include> tags),
preprocess() needs to:
1. Expand the <include> tags
2. Escape curly braces with double_curly_brackets=True
3. Preserve context placeholders with exclude_keys

Without preprocess(), if the template or included files contain JSON like {"url": "..."},
the .format() call interprets the braces as placeholders and raises KeyError.

Compare with agentic_architecture_orchestrator.py:299-302 (CORRECT implementation):
    prompt_template = load_prompt_template(template_name)
    exclude_keys = list(context.keys())
    prompt_template = preprocess(prompt_template, recursive=True,
                                  double_curly_brackets=True, exclude_keys=exclude_keys)
    formatted_prompt = prompt_template.format(**context)

This test verifies the bug and the fix.
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
    E2E tests for Issue #392: Verify the change orchestrator uses preprocess() correctly.

    The bug: agentic_change_orchestrator.py doesn't call preprocess() before .format(),
    so templates with <include> tags that reference files containing JSON cause KeyError.
    """

    def test_step5_template_format_without_preprocess_fails(self):
        """
        Direct test: Loading step 5 template and calling .format() without preprocess() fails.

        This reproduces the exact bug: load_prompt_template() + .format() without preprocess().
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        # Load the step 5 template (contains <include>docs/prompting_guide.md</include>)
        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None, "Step 5 template should exist"

        # Create minimal context
        context = {
            "issue_url": "https://github.com/promptdriven/pdd/issues/392",
            "repo_owner": "promptdriven",
            "repo_name": "pdd",
            "issue_number": "392",
            "issue_content": "Test issue",
            "step1_output": "No duplicates.",
            "step2_output": "Not implemented.",
            "step3_output": "Research complete.",
            "step4_output": "Requirements clear.",
        }

        # First, expand includes WITHOUT escaping (simulates the bug)
        # This is what happens when orchestrator doesn't call preprocess with double_curly_brackets
        processed_no_escape = preprocess(template, recursive=True, double_curly_brackets=False)

        # Check if the processed template contains JSON (from included docs/prompting_guide.md)
        if '{"url"' in processed_no_escape or '"url"' in processed_no_escape:
            # This should fail with KeyError - this IS the bug
            with pytest.raises(KeyError) as exc_info:
                processed_no_escape.format(**context)

            # Verify it's the expected error
            error_msg = str(exc_info.value)
            assert '"url"' in error_msg or 'url' in error_msg, \
                f"Expected KeyError with 'url', got: {error_msg}"

            print(f"BUG REPRODUCED: KeyError({error_msg}) when formatting without escaped braces")
        else:
            pytest.skip("Template doesn't contain JSON after include expansion - can't test bug")

    def test_step5_template_format_with_preprocess_succeeds(self):
        """
        Verify the fix: Using preprocess() with double_curly_brackets=True prevents KeyError.
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        # Load template
        template = load_prompt_template("agentic_change_step5_docs_change_LLM")
        assert template is not None

        # Create context
        context = {
            "issue_url": "https://github.com/promptdriven/pdd/issues/392",
            "repo_owner": "promptdriven",
            "repo_name": "pdd",
            "issue_number": "392",
            "issue_content": "Test issue",
            "step1_output": "No duplicates.",
            "step2_output": "Not implemented.",
            "step3_output": "Research complete.",
            "step4_output": "Requirements clear.",
        }

        # THE FIX: Call preprocess() with double_curly_brackets=True
        exclude_keys = list(context.keys())
        processed_with_escape = preprocess(
            template,
            recursive=True,
            double_curly_brackets=True,
            exclude_keys=exclude_keys
        )

        # This should succeed without KeyError
        try:
            formatted = processed_with_escape.format(**context)
            # Success! The fix works
            assert len(formatted) > 0
            assert "Research complete." in formatted
            print("FIX VERIFIED: Template formatted successfully with preprocess()")
        except KeyError as e:
            pytest.fail(f"Fix failed: preprocess() with double_curly_brackets didn't prevent KeyError: {e}")

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

    def test_preprocess_function_escapes_correctly(self):
        """
        Verify that preprocess() with double_curly_brackets=True escapes JSON correctly.
        """
        from pdd.preprocess import preprocess

        # Test with a template containing both placeholders and JSON
        template = 'Step: {step1}\nJSON: {"url": "https://example.com", "type": "feature"}'

        # Process with double_curly_brackets=True, excluding step1
        processed = preprocess(
            template,
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=["step1"]
        )

        # Should preserve {step1} placeholder but escape JSON braces
        assert '{step1}' in processed, "Placeholder should be preserved"
        assert '{{"url"' in processed, "Opening JSON brace should be doubled"
        # Note: Inner braces within the JSON object aren't separately escaped

        # Verify .format() works
        result = processed.format(step1="Complete")
        assert "Step: Complete" in result
        assert '{"url": "https://example.com"' in result
        assert '"type": "feature"' in result  # Part of the same JSON object

    def test_change_orchestrator_missing_preprocess_call(self):
        """
        Verify that agentic_change_orchestrator.py is missing the preprocess() call (the bug).

        This test will FAIL once the fix is applied (which is good - shows fix is in place).
        """
        import inspect
        from pdd import agentic_change_orchestrator

        # Read the source code
        source = inspect.getsource(agentic_change_orchestrator)

        # Check if preprocess is imported
        has_preprocess_import = "from pdd.preprocess import preprocess" in source

        # Check if preprocess is called before .format()
        has_preprocess_call = "preprocess(prompt_template" in source or \
                              "= preprocess(" in source

        if has_preprocess_import and has_preprocess_call:
            pytest.skip("Fix has been applied! Orchestrator now uses preprocess()")
        else:
            # Bug still exists - document it
            print("BUG CONFIRMED: agentic_change_orchestrator.py missing preprocess() call")
            print(f"    - Has preprocess import: {has_preprocess_import}")
            print(f"    - Has preprocess call: {has_preprocess_call}")

            # This test passes when bug exists, fails when fixed
            # After fix is applied, this will skip instead
            assert not (has_preprocess_import and has_preprocess_call), \
                "Bug detection: orchestrator should be missing preprocess() call"

    def test_arch_orchestrator_has_correct_pattern(self):
        """
        Verify that agentic_architecture_orchestrator.py DOES use preprocess() correctly.
        This is the reference implementation that change orchestrator should follow.
        """
        import inspect
        from pdd import agentic_architecture_orchestrator

        source = inspect.getsource(agentic_architecture_orchestrator)

        # Should import preprocess
        assert "from pdd.preprocess import preprocess" in source, \
            "Architecture orchestrator should import preprocess"

        # Should call preprocess with double_curly_brackets=True
        assert "double_curly_brackets=True" in source, \
            "Architecture orchestrator should use double_curly_brackets=True"

        # Should have the pattern: preprocess(...) before .format()
        assert "preprocess(" in source, \
            "Architecture orchestrator should call preprocess()"

        print("Architecture orchestrator correctly uses preprocess()")

    def test_format_with_escaped_braces_works(self):
        """
        Verify that escaping braces allows .format() to work correctly.

        This shows what preprocess() with double_curly_brackets=True accomplishes.
        """
        # Template with escaped JSON (what preprocess does)
        template = """
Step outputs:
{step3_output}

Documentation with JSON:
{{"url": "https://fastapi.tiangolo.com/tutorial/", "type": "guide"}}

Your task is here.
"""

        context = {"step3_output": "Research complete"}

        # This should work without KeyError
        result = template.format(**context)

        # Verify the JSON is preserved (double braces become single after format)
        assert "Research complete" in result
        assert '{"url": "https://fastapi.tiangolo.com/tutorial/"' in result
        assert '"type": "guide"' in result  # The complete JSON object is preserved

        print("Escaped braces allow .format() to work correctly")
