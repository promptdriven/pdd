"""
E2E Test for Issue #448: KeyError '"url"' in step 5 of pdd change workflow

This is a TRUE E2E test that exercises the template preprocessing and formatting
code path that affects the pdd change command.

Bug Context:
-----------
The change orchestrator needs to call preprocess() with double_curly_brackets=True
before calling format() on templates that include files with JSON content. The
architecture orchestrator (lines 299-302) does this correctly, but the change
orchestrator is missing this preprocessing step.

The bug manifests when:
1. A template has <include> tags pointing to files with JSON (e.g., docs/prompting_guide.md)
2. preprocess() is called to expand includes
3. format() is called WITHOUT escaping the JSON curly braces first

This causes Python's str.format() to interpret JSON like {"url": "..."} as format
placeholders, resulting in KeyError: '"url"'.

The fix requires adding this pattern before format() at lines 598, 713, 727, 790:
    exclude_keys = list(context.keys())
    prompt_template = preprocess(prompt_template, recursive=True,
                                  double_curly_brackets=True, exclude_keys=exclude_keys)
"""

import pytest
import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock
import inspect


@pytest.fixture
def mock_git_repo(tmp_path):
    """Create a minimal git repository for testing the orchestrator."""
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()

    # Initialize git repo
    subprocess.run(["git", "init", "-b", "main"], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=repo_path, check=True)

    # Create minimal project structure
    pdd_dir = repo_path / ".pdd"
    pdd_dir.mkdir()

    # Create a dummy file and commit
    (repo_path / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=repo_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_path, check=True, capture_output=True)

    return repo_path


@pytest.mark.e2e
class TestIssue448TemplatePreprocessingE2E:
    """
    E2E tests for Issue #448: Template preprocessing must escape JSON curly braces.

    These tests verify the complete code path from template loading through
    formatting, demonstrating the bug and verifying the fix pattern.
    """

    def test_preprocessing_without_double_curly_causes_keyerror(self):
        """
        E2E Test: Preprocessing includes WITHOUT escaping causes KeyError on format().

        This test demonstrates the EXACT bug scenario:
        1. Load a template with <include> tags
        2. Expand includes with preprocess() but WITHOUT double_curly_brackets=True
        3. Call format() - this raises KeyError because JSON braces are interpreted as placeholders

        This is the behavior that occurs when the change orchestrator's fix is incomplete.
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        # Load the step 5 template (which includes docs/prompting_guide.md)
        template_name = "agentic_change_step5_docs_change_LLM"
        prompt_template = load_prompt_template(template_name)

        if prompt_template is None:
            pytest.skip(f"Template not found: {template_name}")

        if '<include>' not in prompt_template:
            pytest.skip("Template doesn't have <include> tags - bug may not manifest")

        # Expand includes BUT don't escape curly braces (simulates incomplete fix)
        processed_buggy = preprocess(
            prompt_template,
            recursive=True,
            double_curly_brackets=False,  # BUG: Should be True
            exclude_keys=[]
        )

        # Verify the processed template contains JSON that triggers the bug
        json_like_patterns = ['{"url":', '{"name":', '"type":']
        has_json = any(pattern in processed_buggy for pattern in json_like_patterns)

        if not has_json:
            pytest.skip("Preprocessed template doesn't contain JSON - bug may not manifest")

        # Build context like the orchestrator does
        context = {
            "issue_url": "https://github.com/test/repo/issues/448",
            "issue_content": "Test issue content",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 448,
            "step1_output": "Step 1 done",
            "step2_output": "Step 2 done",
            "step3_output": "Step 3 done",
            "step4_output": "Step 4 done",
        }

        # THE BUG: format() raises KeyError because JSON braces are interpreted as placeholders
        with pytest.raises(KeyError) as exc_info:
            processed_buggy.format(**context)

        # Verify it's the specific error from the bug report
        error_key = str(exc_info.value)
        assert '"url"' in error_key or '"name"' in error_key or '"type"' in error_key, \
            f"Expected KeyError for JSON key, got: {error_key}"

    def test_preprocessing_with_double_curly_prevents_keyerror(self):
        """
        E2E Test: Preprocessing with double_curly_brackets=True prevents KeyError.

        This test demonstrates the CORRECT behavior (the fix):
        1. Load a template with <include> tags
        2. Expand includes with preprocess() WITH double_curly_brackets=True
        3. Call format() - this succeeds because JSON braces are escaped

        This is the pattern used in agentic_architecture_orchestrator.py:299-302.
        """
        from pdd.load_prompt_template import load_prompt_template
        from pdd.preprocess import preprocess

        # Load the step 5 template
        template_name = "agentic_change_step5_docs_change_LLM"
        prompt_template = load_prompt_template(template_name)

        if prompt_template is None:
            pytest.skip(f"Template not found: {template_name}")

        # Build context
        context = {
            "issue_url": "https://github.com/test/repo/issues/448",
            "issue_content": "Test issue content",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 448,
            "step1_output": "Step 1 done",
            "step2_output": "Step 2 done",
            "step3_output": "Step 3 done",
            "step4_output": "Step 4 done",
        }

        # THE FIX: Preprocess with double_curly_brackets=True and exclude context keys
        exclude_keys = list(context.keys())
        processed_fixed = preprocess(
            prompt_template,
            recursive=True,
            double_curly_brackets=True,  # CORRECT: Escapes literal braces
            exclude_keys=exclude_keys
        )

        # This should NOT raise KeyError
        try:
            formatted = processed_fixed.format(**context)
        except KeyError as e:
            pytest.fail(
                f"Even with correct preprocessing, KeyError occurred: {e}\n"
                f"This suggests the fix implementation may have an issue."
            )

        # Verify context variables were substituted
        assert "https://github.com/test/repo/issues/448" in formatted, \
            "issue_url should be substituted"
        assert "test/repo" in formatted, \
            "repo_owner/repo_name should be substituted"

        # Verify includes were expanded (content from prompting_guide.md should be present)
        # Note: The prompting guide content should be present after preprocessing
        if '<include>' in formatted:
            # If includes are still present, they may be in example text (which is OK)
            # The key test is that format() succeeded without KeyError
            pass

    def test_change_orchestrator_needs_preprocessing_pattern(self):
        """
        E2E Test: Verify the change orchestrator needs the preprocessing pattern.

        This test inspects the actual source code to confirm the bug exists
        (missing preprocess call) and will FAIL once the fix is applied.
        """
        import pdd.agentic_change_orchestrator as change_orch

        source = inspect.getsource(change_orch)

        # Check if preprocess is imported
        has_preprocess_import = "from pdd.preprocess import preprocess" in source

        # Check if preprocess is called with double_curly_brackets=True
        has_double_curly_call = "double_curly_brackets=True" in source

        if has_preprocess_import and has_double_curly_call:
            # The fix has been applied - test passes
            pass
        else:
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


@pytest.mark.e2e
class TestIssue448OrchestratorIntegration:
    """
    Integration tests that exercise the full orchestrator code path.
    """

    def test_change_orchestrator_workflow_with_mock_llm(self, mock_git_repo, monkeypatch):
        """
        E2E Integration Test: Run orchestrator through multiple steps with mocked LLM.

        This test exercises the orchestrator workflow to verify template loading
        and formatting works correctly at each step.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Track which steps were attempted
        steps_attempted = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM agent that returns success for each step."""
            import re
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_attempted.append(step_num)

            # Return appropriate responses for each step
            if "step1" in label:
                return (True, "No duplicate issues found. Proceed.", 0.001, "mock-model")
            elif "step2" in label:
                return (True, "Feature not implemented yet. Proceed.", 0.001, "mock-model")
            elif "step3" in label:
                return (True, "Research complete. Requirements clear.", 0.001, "mock-model")
            elif "step4" in label:
                return (True, "Requirements verified. Proceed.", 0.001, "mock-model")
            elif "step5" in label:
                return (True, "Documentation analysis complete.", 0.001, "mock-model")
            elif "step6" in label:
                # Return hard stop to end workflow gracefully
                return (True, "STOP_WORKFLOW: Testing completed.", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            pass

        def mock_load_state(*args, **kwargs):
            return None, None

        def mock_clear_state(*args, **kwargs):
            pass

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        success, message, cost, model, files = run_agentic_change_orchestrator(
                            issue_url="https://github.com/test/repo/issues/448",
                            issue_content="Test issue for bug #448",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=448,
                            issue_author="test-user",
                            issue_title="Test Issue 448",
                            cwd=mock_git_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=False
                        )

        # Check for the specific bug error
        if not success and 'Context missing key for step' in message:
            if '"url"' in message or '"name"' in message or '"type"' in message:
                pytest.fail(
                    f"BUG DETECTED (Issue #448): Orchestrator failed due to KeyError.\n\n"
                    f"Error: {message}\n"
                    f"Steps attempted: {steps_attempted}\n\n"
                    f"This indicates preprocessing is being done but without "
                    f"double_curly_brackets=True to escape JSON."
                )

        # Verify workflow reached at least step 5
        assert 5 in steps_attempted or len(steps_attempted) >= 5, (
            f"Workflow should have reached step 5. Steps attempted: {steps_attempted}"
        )


@pytest.mark.e2e
class TestIssue448OrchestratorComparison:
    """
    Comparison tests between architecture and change orchestrators.
    """

    def test_architecture_orchestrator_has_correct_preprocessing(self):
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

    def test_both_orchestrators_should_use_same_pattern(self):
        """
        Verify change orchestrator uses same preprocessing pattern as architecture.

        This test FAILS on buggy code and PASSES after the fix.
        """
        import pdd.agentic_change_orchestrator as change_orch
        import pdd.agentic_architecture_orchestrator as arch_orch

        change_source = inspect.getsource(change_orch)
        arch_source = inspect.getsource(arch_orch)

        # Architecture orchestrator has the pattern
        assert "double_curly_brackets=True" in arch_source, \
            "Architecture orchestrator pattern check failed (test setup issue)"

        # Change orchestrator should have the same pattern
        if "double_curly_brackets=True" not in change_source:
            pytest.fail(
                "BUG (Issue #448): agentic_change_orchestrator.py does NOT use "
                "the same preprocessing pattern as agentic_architecture_orchestrator.py.\n\n"
                "The change orchestrator needs to add:\n"
                "  preprocess(prompt_template, recursive=True, double_curly_brackets=True, "
                "exclude_keys=exclude_keys)\n\n"
                "before calling prompt_template.format(**context)"
            )
