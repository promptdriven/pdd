"""
E2E Test for Issue #838: pdd bug generates structural tests instead of behavioral tests.

Bug Context:
-----------
The bug workflow's Step 8 (test plan) and Step 9 (test generation) prompts lacked
guidance to block structural/shape anti-patterns like `inspect.signature()`,
`hasattr()`, and `sig.parameters`. This allowed the LLM to generate tests that
pass by merely adding parameters to function signatures without implementing
actual behavior.

This E2E test exercises the full orchestrator pipeline — loading prompt templates,
preprocessing, formatting with context, and passing to run_agentic_task — to verify
that the rendered prompts for Steps 8 and 9 contain structural anti-pattern blocking.
Unlike the unit tests (which read prompt files directly), this test verifies the
prompts survive the full load → preprocess → format → dispatch pipeline.
"""

import subprocess
import re

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock


@pytest.fixture
def mock_git_repo(tmp_path):
    """Create a minimal git repository for testing the orchestrator."""
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()

    subprocess.run(["git", "init", "-b", "main"], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=repo_path, check=True)

    pdd_dir = repo_path / ".pdd"
    pdd_dir.mkdir()

    (repo_path / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=repo_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_path, check=True, capture_output=True)

    return repo_path


STRUCTURAL_ANTI_PATTERNS = [
    "inspect.signature()",
    "hasattr()",
    "sig.parameters",
]


@pytest.mark.e2e
class TestIssue838StructuralTestBlockingE2E:
    """
    E2E tests for Issue #838: verify the orchestrator's rendered prompts for
    Steps 8 and 9 contain structural anti-pattern blocking guidance.
    """

    def test_step8_rendered_prompt_blocks_structural_patterns(self, mock_git_repo, monkeypatch):
        """
        E2E Test: Run the orchestrator through Step 8 and capture the rendered
        prompt instruction. Verify it contains structural anti-pattern blocking.

        Before the fix, the Step 8 prompt had zero mentions of inspect.signature(),
        hasattr(), or sig.parameters — allowing the LLM to design structural test plans.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        captured_instructions = {}

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Capture the instruction text for each step."""
            captured_instructions[label] = instruction

            # Stop after step 8 by returning a STOP_CONDITION
            if "step8" in label:
                return (True, "STOP_CONDITION: Test plan complete (E2E capture)", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            """No-op save."""
            pass

        def mock_load_state(*args, **kwargs):
            """Return no saved state."""
            return None, None

        def mock_clear_state(*args, **kwargs):
            """No-op clear."""
            pass

        from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

        with patch('pdd.agentic_bug_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_bug_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_bug_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_bug_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        run_agentic_bug_orchestrator(
                            issue_url="https://github.com/test/repo/issues/838",
                            issue_content="Test issue: structural tests instead of behavioral",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=838,
                            issue_author="test-user",
                            issue_title="Structural test blocking",
                            cwd=mock_git_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                        )

        # Verify Step 8 instruction was captured
        assert "step8" in captured_instructions, (
            "Step 8 instruction was not captured — orchestrator did not reach Step 8."
        )

        step8_instruction = captured_instructions["step8"].lower()

        # Verify each structural anti-pattern is blocked in the rendered prompt
        for pattern in STRUCTURAL_ANTI_PATTERNS:
            assert pattern in step8_instruction, (
                f"BUG DETECTED (Issue #838): The rendered Step 8 prompt sent to the LLM "
                f"does NOT mention '{pattern}' as a blocked anti-pattern. "
                f"Without this guidance, the LLM can generate structural test plans "
                f"that pass by merely adding parameters to function signatures."
            )

    def test_step9_rendered_prompt_blocks_structural_patterns(self, mock_git_repo, monkeypatch):
        """
        E2E Test: Run the orchestrator through Step 9 and capture the rendered
        prompt instruction. Verify it contains structural anti-pattern blocking.

        Before the fix, the Step 9 prompt only had a weak one-liner about
        'testing behavior' and had no explicit mention of inspect.signature(),
        hasattr(), or sig.parameters as blocked patterns.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        captured_instructions = {}

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Capture the instruction text for each step."""
            captured_instructions[label] = instruction

            # Stop after step 9 by returning a STOP_CONDITION
            if "step9" in label:
                return (True, "STOP_CONDITION: Test generated (E2E capture)", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            """No-op save."""
            pass

        def mock_load_state(*args, **kwargs):
            """Return no saved state."""
            return None, None

        def mock_clear_state(*args, **kwargs):
            """No-op clear."""
            pass

        from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

        with patch('pdd.agentic_bug_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_bug_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_bug_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_bug_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        run_agentic_bug_orchestrator(
                            issue_url="https://github.com/test/repo/issues/838",
                            issue_content="Test issue: structural tests instead of behavioral",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=838,
                            issue_author="test-user",
                            issue_title="Structural test blocking",
                            cwd=mock_git_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                        )

        # Verify Step 9 instruction was captured
        assert "step9" in captured_instructions, (
            "Step 9 instruction was not captured — orchestrator did not reach Step 9."
        )

        step9_instruction = captured_instructions["step9"].lower()

        # Verify each structural anti-pattern is blocked in the rendered prompt
        for pattern in STRUCTURAL_ANTI_PATTERNS:
            assert pattern in step9_instruction, (
                f"BUG DETECTED (Issue #838): The rendered Step 9 prompt sent to the LLM "
                f"does NOT mention '{pattern}' as a blocked anti-pattern. "
                f"Without this guidance, the LLM generates structural test code "
                f"like `assert 'quiet' in sig.parameters` instead of behavioral tests."
            )

    def test_step9_rendered_prompt_has_bad_good_code_examples(self, mock_git_repo, monkeypatch):
        """
        E2E Test: Verify the rendered Step 9 prompt contains both BAD and GOOD
        code examples showing structural vs behavioral testing patterns.

        This is critical because the LLM needs concrete examples — not just
        abstract instructions — to avoid generating structural tests.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        captured_instructions = {}

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Capture the instruction text for each step."""
            captured_instructions[label] = instruction

            if "step9" in label:
                return (True, "STOP_CONDITION: Test generated (E2E capture)", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            """No-op save."""
            pass

        def mock_load_state(*args, **kwargs):
            """Return no saved state."""
            return None, None

        def mock_clear_state(*args, **kwargs):
            """No-op clear."""
            pass

        from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

        with patch('pdd.agentic_bug_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_bug_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_bug_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_bug_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        run_agentic_bug_orchestrator(
                            issue_url="https://github.com/test/repo/issues/838",
                            issue_content="Test issue: structural tests instead of behavioral",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=838,
                            issue_author="test-user",
                            issue_title="Structural test blocking",
                            cwd=mock_git_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                        )

        assert "step9" in captured_instructions, (
            "Step 9 instruction was not captured."
        )

        step9_instruction = captured_instructions["step9"].lower()

        # Must have BAD example with the exact anti-pattern from issue #838
        has_bad_example = (
            "bad" in step9_instruction
            and "inspect.signature" in step9_instruction
        )
        assert has_bad_example, (
            "BUG DETECTED (Issue #838): The rendered Step 9 prompt does NOT contain "
            "a BAD code example showing the inspect.signature anti-pattern. "
            "Without a concrete negative example, the LLM defaults to structural tests."
        )

        # Must have GOOD example with behavioral testing (mock/patch)
        has_good_example = (
            "good" in step9_instruction
            and ("patch" in step9_instruction or "mock" in step9_instruction)
        )
        assert has_good_example, (
            "BUG DETECTED (Issue #838): The rendered Step 9 prompt does NOT contain "
            "a GOOD code example showing behavioral testing with mocks/patches."
        )
