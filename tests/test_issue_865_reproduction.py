"""Regression tests for issue #865: LLMs don't reliably emit structured control tokens.

Originally written as reproduction tests by pdd-bug (PR #867), then converted
to regression guards after the fix landed. Each test preserves the real-world
LLM output from the evidence section of issue #865.

Three layers of the bug (all now fixed):
1. Step 1 prompt had zero mention of ALL_TESTS_PASS; Step 3 prompt had no MANDATORY section
2. Even Step 9's MANDATORY instruction was insufficient (intermittent)
3. Orchestrator used exact substring matching with no semantic fallback
"""

from __future__ import annotations

import pytest
from unittest.mock import patch

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator


@pytest.fixture
def e2e_fix_mock_dependencies(tmp_path):
    """Mock all external dependencies for orchestrator tests."""
    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit, \
         patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check_e2e, \
         patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output", return_value=None):

        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"
        mock_load_state.return_value = (None, None)
        mock_save_state.return_value = None
        mock_hashes.return_value = {}
        mock_commit.return_value = (True, "No changes to commit")
        mock_check_e2e.return_value = (True, "")

        yield mock_run, mock_load, mock_console


@pytest.fixture
def e2e_fix_default_args(tmp_path):
    """Default arguments for run_agentic_e2e_fix_orchestrator."""
    return {
        "issue_url": "http://github.com/owner/repo/issues/1",
        "issue_content": "Bug description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Bug Title",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "resume": False,
        "use_github_state": False,
    }


class TestIssue865Layer1PromptInstructions:
    """Layer 1: Step 1 and Step 3 prompts now have MANDATORY control token instructions."""

    def test_step1_prompt_has_all_tests_pass_instruction(self):
        """Step 1 prompt must mention ALL_TESTS_PASS as a required token.

        Previously: Step 1 prompt had zero mention of ALL_TESTS_PASS.
        Fix: Added MANDATORY section matching Step 9's pattern.
        """
        from pdd.load_prompt_template import load_prompt_template
        template = load_prompt_template("agentic_e2e_fix_step1_unit_tests_LLM")

        assert "ALL_TESTS_PASS" in template, (
            "Step 1 prompt must mention ALL_TESTS_PASS so the LLM knows to emit it."
        )

    def test_step3_prompt_has_mandatory_section_for_not_a_bug(self):
        """Step 3 prompt must have MANDATORY instruction for NOT_A_BUG.

        Previously: Step 3 listed NOT_A_BUG as a status but had no MANDATORY section.
        Fix: Added MANDATORY section telling the LLM the orchestrator parses for it.
        """
        from pdd.load_prompt_template import load_prompt_template
        template = load_prompt_template("agentic_e2e_fix_step3_root_cause_LLM")

        assert "NOT_A_BUG" in template, "Step 3 must list NOT_A_BUG as a category"
        assert "MANDATORY" in template, (
            "Step 3 must have a MANDATORY section for NOT_A_BUG."
        )

    def test_step9_prompt_has_mandatory_section(self):
        """Step 9 prompt correctly has the MANDATORY section (reference for fix)."""
        from pdd.load_prompt_template import load_prompt_template
        template = load_prompt_template("agentic_e2e_fix_step9_verify_all_LLM")

        assert "MANDATORY" in template, "Step 9 should have MANDATORY section"
        assert "ALL_TESTS_PASS" in template
        assert "CONTINUE_CYCLE" in template
        assert "MAX_CYCLES_REACHED" in template


class TestIssue865Layer3SemanticDetection:
    """Layer 3: Orchestrator now detects paraphrased control tokens via semantic fallback.

    These tests use real-world LLM outputs from the issue evidence to verify
    that the three-tier detection (exact → case-insensitive → semantic regex)
    catches them.
    """

    def test_step3_paraphrased_not_a_bug_detected(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Step 3 says 'it is already fixed' — semantic fallback detects NOT_A_BUG.

        Real-world case from pdd_cloud#600: LLM said 'it is already fixed on
        this branch' and 'I did not make code changes' but never emitted NOT_A_BUG.
        Previously: workflow ran all 9 steps × 5 cycles (45 calls).
        Now: exits early at Step 3 (3 calls).
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step3' in label:
                # Real-world paraphrase from pdd_cloud#600 - no exact NOT_A_BUG token
                return (True, (
                    "## Root Cause Analysis\n"
                    "After investigation, it is already fixed on this branch. "
                    "I did not make code changes. This is not a bug — the reported "
                    "behavior is expected and working correctly."
                ), 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "CONTINUE_CYCLE", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Fixed: semantic fallback detects "already fixed" / "not a bug" / "expected behavior"
        assert mock_run.call_count == 3, (
            f"Expected 3 calls (early exit at Step 3 via semantic detection) "
            f"but got {mock_run.call_count}."
        )

    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_step2_paraphrased_all_tests_pass_detected(
        self, mock_extract, mock_verify,
        e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """Step 2 says 'both passed' — semantic fallback detects ALL_TESTS_PASS.

        Real-world case from pdd_cloud#600: LLM said 'Verified with npx jest...
        both passed' but never emitted ALL_TESTS_PASS.
        Previously: workflow ran all 9 steps × 5 cycles (45 calls).
        Now: exits early at Step 2 (2 calls).
        """
        mock_run, _, _ = e2e_fix_mock_dependencies
        mock_extract.return_value = ["test_foo.py"]
        mock_verify.return_value = (True, "All tests passed")

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step2' in label:
                # Real-world paraphrase from pdd_cloud#600 - no exact ALL_TESTS_PASS token
                return (True, (
                    "## E2E Test Results\n"
                    "Verified with npx jest -- both passed.\n"
                    "All 2 tests passed successfully. 2/2 passing."
                ), 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "CONTINUE_CYCLE", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Fixed: semantic fallback detects "both passed" and "2/2 passing"
        assert mock_run.call_count == 2, (
            f"Expected 2 calls (early exit at Step 2 via semantic detection) "
            f"but got {mock_run.call_count}."
        )
        assert success is True

    def test_step9_paraphrased_all_pass_detected(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Step 9 says '18/18 pass' — semantic fallback detects ALL_TESTS_PASS.

        Real-world case from pdd_cloud#673: Step 9 had MANDATORY instructions
        but LLM still didn't emit any token.
        Previously: workflow stopped with safety error.
        Now: detects ALL_TESTS_PASS via semantic patterns.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                # No exact control token — just paraphrased results
                return (True, (
                    "## Final Verification\n"
                    "All 18 tests pass. 18/18 passing.\n"
                    "The fix is complete and all tests are green."
                ), 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Fixed: semantic fallback detects "All 18 tests pass" and "18/18 passing"
        assert success is True, (
            f"Expected success via semantic detection but got success={success}, msg={msg}"
        )

    def test_step3_case_insensitive_not_a_bug_detected(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Step 3 says 'not_a_bug' in lowercase — case-insensitive match detects it.

        Previously: exact match `"NOT_A_BUG" in step_output` missed lowercase.
        Now: case-insensitive tier catches it.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step3' in label:
                return (True, "**Status:** not_a_bug\nThis is not actually a bug.", 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "CONTINUE_CYCLE", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Fixed: case-insensitive detection catches lowercase "not_a_bug"
        assert mock_run.call_count == 3, (
            f"Expected 3 calls (early exit at Step 3) but got {mock_run.call_count}."
        )
