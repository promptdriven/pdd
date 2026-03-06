"""
Tests for Issue #643: _check_hard_stop doesn't detect stop conditions due to
casing mismatch between orchestrator checks and prompt-instructed LLM output.

Bug: The orchestrator checks for "Clarification Needed" (title case) and
"Architectural Decision Needed" (title case), but the prompts instruct the LLM
to output "STOP_CONDITION: Clarification needed" and "STOP_CONDITION:
Architectural decision needed" (lowercase). The strings don't match, so the
workflow never stops.

These tests verify:
1. _check_hard_stop detects the STOP_CONDITION format the prompts actually produce
2. _check_hard_stop handles case-insensitive matching
3. Prompts contain the correct STOP_CONDITION markers
4. Integration: orchestrator halts when step output contains prompt-format stops
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

from pdd.agentic_change_orchestrator import _check_hard_stop


# ---------------------------------------------------------------------------
# Unit Tests: _check_hard_stop with prompt-instructed output formats
# ---------------------------------------------------------------------------

class TestCheckHardStopStep4ClarificationBug:
    """Tests for Step 4 clarification stop condition (issue #643)."""

    def test_step4_detects_stop_condition_format(self):
        """_check_hard_stop must detect 'STOP_CONDITION: Clarification needed'
        — the exact format the step 4 prompt instructs the LLM to output."""
        output = (
            "After reviewing the issue, several requirements are unclear.\n"
            "I've posted clarification questions to the GitHub issue.\n\n"
            "STOP_CONDITION: Clarification needed"
        )
        result = _check_hard_stop(step_num=4, output=output)
        assert result is not None, (
            "BUG #643: _check_hard_stop fails to detect 'STOP_CONDITION: Clarification needed' "
            "because it only checks for 'Clarification Needed' (title case)"
        )

    def test_step4_detects_lowercase_clarification_needed(self):
        """_check_hard_stop must detect 'Clarification needed' (lowercase 'n')
        since that's what the prompt instructs."""
        output = "Clarification needed — posted questions to the issue."
        result = _check_hard_stop(step_num=4, output=output)
        assert result is not None, (
            "BUG #643: _check_hard_stop fails on 'Clarification needed' (lowercase) "
            "because it only checks for 'Clarification Needed' (title case 'N')"
        )

    def test_step4_still_detects_title_case(self):
        """Regression: the original title-case format must still work."""
        output = "Clarification Needed — requirements are ambiguous."
        result = _check_hard_stop(step_num=4, output=output)
        assert result is not None, (
            "Regression: _check_hard_stop should still detect 'Clarification Needed'"
        )


class TestCheckHardStopStep7ArchitectureBug:
    """Tests for Step 7 architectural stop condition (issue #643)."""

    def test_step7_detects_stop_condition_format(self):
        """_check_hard_stop must detect 'STOP_CONDITION: Architectural decision needed'
        — the exact format the step 7 prompt instructs the LLM to output."""
        output = (
            "The architecture needs review before proceeding.\n"
            "Posted questions to the GitHub issue.\n\n"
            "STOP_CONDITION: Architectural decision needed"
        )
        result = _check_hard_stop(step_num=7, output=output)
        assert result is not None, (
            "BUG #643: _check_hard_stop fails to detect 'STOP_CONDITION: Architectural decision needed' "
            "because it only checks for 'Architectural Decision Needed' (title case)"
        )

    def test_step7_detects_lowercase_decision_needed(self):
        """_check_hard_stop must detect 'Architectural decision needed' (lowercase)
        since that's what the prompt instructs."""
        output = "Architectural decision needed — awaiting input."
        result = _check_hard_stop(step_num=7, output=output)
        assert result is not None, (
            "BUG #643: _check_hard_stop fails on 'Architectural decision needed' (lowercase) "
            "because it only checks for 'Architectural Decision Needed' (title case)"
        )

    def test_step7_still_detects_title_case(self):
        """Regression: the original title-case format must still work."""
        output = "Architectural Decision Needed — awaiting input."
        result = _check_hard_stop(step_num=7, output=output)
        assert result is not None, (
            "Regression: _check_hard_stop should still detect 'Architectural Decision Needed'"
        )


# ---------------------------------------------------------------------------
# Prompt Validation Tests
# ---------------------------------------------------------------------------

class TestPromptStopConditionMarkers:
    """Verify that the prompts contain the STOP_CONDITION markers."""

    def _find_prompt_dir(self):
        """Locate the prompts directory."""
        return Path(__file__).parent.parent / "pdd" / "prompts"

    def test_step4_prompt_has_stop_condition(self):
        """Step 4 prompt must contain STOP_CONDITION: Clarification needed."""
        prompt_path = self._find_prompt_dir() / "agentic_change_step4_clarify_LLM.prompt"
        content = prompt_path.read_text()
        assert "STOP_CONDITION: Clarification needed" in content, (
            "Step 4 prompt must instruct LLM to output 'STOP_CONDITION: Clarification needed'"
        )

    def test_step7_prompt_has_stop_condition(self):
        """Step 7 prompt must contain STOP_CONDITION: Architectural decision needed."""
        prompt_path = self._find_prompt_dir() / "agentic_change_step7_architecture_LLM.prompt"
        content = prompt_path.read_text()
        assert "STOP_CONDITION: Architectural decision needed" in content, (
            "Step 7 prompt must instruct LLM to output 'STOP_CONDITION: Architectural decision needed'"
        )


# ---------------------------------------------------------------------------
# Integration Tests: Full orchestrator flow with prompt-format stop output
# ---------------------------------------------------------------------------

class TestOrchestratorHaltsOnPromptFormatStop:
    """Integration tests that the orchestrator actually halts when steps
    output the STOP_CONDITION format the prompts instruct."""

    @patch("pdd.agentic_change_orchestrator.post_step_comment")
    @patch("pdd.agentic_change_orchestrator.console")
    @patch("pdd.agentic_change_orchestrator.preprocess", side_effect=lambda prompt, **kw: prompt)
    @patch("pdd.agentic_change_orchestrator.clear_workflow_state")
    @patch("pdd.agentic_change_orchestrator.save_workflow_state")
    @patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None))
    @patch("pdd.agentic_change_orchestrator.load_prompt_template", return_value="mock prompt")
    @patch("pdd.agentic_change_orchestrator.run_agentic_task")
    @patch("pdd.agentic_change_orchestrator.subprocess.run")
    def test_step4_halts_on_stop_condition_format(
        self, mock_subprocess, mock_run, mock_template, mock_load_state,
        mock_save_state, mock_clear_state, mock_preprocess, mock_console,
        mock_post_comment, tmp_path
    ):
        """Orchestrator must halt at Step 4 when LLM outputs the prompt-instructed
        STOP_CONDITION format, not continue to Step 5+."""
        # Mock git worktree setup
        mock_subprocess.return_value = MagicMock(returncode=0, stdout=str(tmp_path))

        # Steps 1-3 succeed, Step 4 outputs the prompt-instructed stop format
        # Provide enough outputs for all 10 steps in case the bug causes continuation
        def run_side_effect(**kwargs):
            label = kwargs.get("label", "")
            if label == "step4":
                return (True, "Questions posted.\n\nSTOP_CONDITION: Clarification needed", 0.01, "gpt-4")
            if label == "step9":
                return (True, "FILES_MODIFIED: file.py", 0.01, "gpt-4")
            return (True, f"Output for {label}", 0.01, "gpt-4")
        mock_run.side_effect = run_side_effect

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        result = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="Test body",
            repo_owner="test",
            repo_name="repo",
            issue_number=643,
            issue_author="user",
            issue_title="Test issue",
            cwd=tmp_path,
        )

        # The orchestrator should have stopped after Step 4
        # If the bug is present, it will continue past step 4 and call run_agentic_task 5+ times
        assert mock_run.call_count <= 4, (
            f"BUG #643: Orchestrator continued past Step 4 (called run_agentic_task "
            f"{mock_run.call_count} times). It should halt when the LLM outputs "
            f"'STOP_CONDITION: Clarification needed'"
        )

    @patch("pdd.agentic_change_orchestrator.post_step_comment")
    @patch("pdd.agentic_change_orchestrator.console")
    @patch("pdd.agentic_change_orchestrator.preprocess", side_effect=lambda prompt, **kw: prompt)
    @patch("pdd.agentic_change_orchestrator.clear_workflow_state")
    @patch("pdd.agentic_change_orchestrator.save_workflow_state")
    @patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None))
    @patch("pdd.agentic_change_orchestrator.load_prompt_template", return_value="mock prompt")
    @patch("pdd.agentic_change_orchestrator.run_agentic_task")
    @patch("pdd.agentic_change_orchestrator.subprocess.run")
    def test_step7_halts_on_stop_condition_format(
        self, mock_subprocess, mock_run, mock_template, mock_load_state,
        mock_save_state, mock_clear_state, mock_preprocess, mock_console,
        mock_post_comment, tmp_path
    ):
        """Orchestrator must halt at Step 7 when LLM outputs the prompt-instructed
        STOP_CONDITION format, not continue to Step 8+."""
        mock_subprocess.return_value = MagicMock(returncode=0, stdout=str(tmp_path))

        # Steps 1-6 succeed, Step 7 outputs the prompt-instructed stop format
        # Provide enough outputs for all 10 steps in case the bug causes continuation
        def run_side_effect(**kwargs):
            label = kwargs.get("label", "")
            if label == "step7":
                return (True, "Posted arch questions.\n\nSTOP_CONDITION: Architectural decision needed", 0.01, "gpt-4")
            if label == "step9":
                return (True, "FILES_MODIFIED: file.py", 0.01, "gpt-4")
            return (True, f"Output for {label}", 0.01, "gpt-4")
        mock_run.side_effect = run_side_effect

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        result = run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="Test body",
            repo_owner="test",
            repo_name="repo",
            issue_number=643,
            issue_author="user",
            issue_title="Test issue",
            cwd=tmp_path,
        )

        assert mock_run.call_count <= 7, (
            f"BUG #643: Orchestrator continued past Step 7 (called run_agentic_task "
            f"{mock_run.call_count} times). It should halt when the LLM outputs "
            f"'STOP_CONDITION: Architectural decision needed'"
        )
