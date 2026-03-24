"""E2E tests for issue #903: convergence detection in the fix orchestrator.

These tests exercise the full orchestrator workflow end-to-end, simulating
realistic multi-cycle scenarios that match the original bug report
(pdd_cloud#591: 5 cycles when only 2 needed, cycles 3-5 wasted).

Unlike the unit tests in test_agentic_e2e_fix_orchestrator.py which test
individual convergence checks in isolation, these E2E tests verify the
complete workflow behavior from entry to exit, asserting on workflow-level
outcomes (total cycles, cost, step execution counts).
"""
import re
from typing import Dict, List
from unittest.mock import patch, MagicMock

import pytest
from pathlib import Path

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator


@pytest.fixture
def e2e_orchestrator_mocks(tmp_path):
    """Mock external dependencies for full E2E orchestrator runs.

    Only mocks external I/O (LLM calls, git, state persistence, console).
    Does NOT mock any orchestrator-internal logic (convergence checks,
    step routing, cycle control) — those are exercised for real.
    """
    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit, \
         patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check_e2e, \
         patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output", return_value=None) as mock_classify, \
         patch("pdd.agentic_e2e_fix_orchestrator.post_final_comment") as mock_post_comment:

        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"
        mock_load_state.return_value = (None, None)
        mock_save_state.return_value = None
        mock_hashes.return_value = {}
        mock_commit.return_value = (True, "No changes to commit")
        mock_check_e2e.return_value = (True, "")

        yield {
            "mock_run": mock_run,
            "mock_load": mock_load,
            "mock_console": mock_console,
            "mock_hashes": mock_hashes,
        }


@pytest.fixture
def orchestrator_args(tmp_path):
    """Standard arguments matching a realistic pdd-fix invocation."""
    return {
        "issue_url": "https://github.com/promptdriven/pdd_cloud/issues/591",
        "issue_content": (
            "Title: Fix auth middleware token storage\n\n"
            "Description:\nAuth middleware stores tokens in plaintext.\n\n"
            "Comments:\n"
        ),
        "repo_owner": "promptdriven",
        "repo_name": "pdd_cloud",
        "issue_number": 591,
        "issue_author": "gltanaka",
        "issue_title": "Fix auth middleware token storage",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "resume": False,
        "use_github_state": False,
    }


def _extract_step_labels(mock_run) -> List[str]:
    """Extract step labels from all run_agentic_task calls."""
    return [call.kwargs.get("label", "") for call in mock_run.call_args_list]


def _count_cycles(labels: List[str]) -> int:
    """Count how many distinct cycles ran based on step labels."""
    cycles = set()
    for label in labels:
        match = re.match(r"cycle(\d+)_", label)
        if match:
            cycles.add(int(match.group(1)))
    return len(cycles)


class TestE2EWastedCyclesScenario:
    """Reproduces the exact scenario from pdd_cloud#591: cycles 3-5 run with
    0 dev units, wasting time and cost.

    This is the primary E2E test. It simulates a realistic 5-cycle workflow
    where cycle 1 makes real fixes, cycle 2 finds 0 dev units remaining,
    but the buggy orchestrator continues through cycles 3-5 anyway.
    """

    def test_zero_dev_units_stops_workflow_after_one_wasted_cycle(
        self, e2e_orchestrator_mocks, orchestrator_args
    ):
        """Full workflow: cycle 1 fixes code, cycle 2 finds 0 dev units.
        Orchestrator should stop — not run cycles 3-5.

        Bug: The orchestrator runs all 5 cycles even when cycles 2+ find
        'DEV_UNITS_IDENTIFIED: 0'. Steps 6-8 still execute uselessly.
        """
        mock_run = e2e_orchestrator_mocks["mock_run"]
        orchestrator_args["max_cycles"] = 5

        def realistic_side_effect(*args, **kwargs):
            """Simulate realistic LLM outputs across multiple cycles."""
            label = kwargs.get("label", "")

            # Cycle 1: real work happens — dev units found and fixed
            if "cycle1_step5" in label:
                return (True, "DEV_UNITS_IDENTIFIED: auth_module\n1/1 Dev Units Needed Fix", 0.15, "gpt-4")
            if "cycle1_step9" in label:
                return (True, "Tests still failing after fixes. CONTINUE_CYCLE", 0.12, "gpt-4")

            # Cycles 2-5: 0 dev units — no work left to do
            if "step5" in label:
                return (True, "DEV_UNITS_IDENTIFIED: 0/0\n0/0 Dev Units Needed Fix", 0.10, "gpt-4")
            if "step9" in label:
                return (True, "Some tests still failing. CONTINUE_CYCLE", 0.10, "gpt-4")

            return (True, f"Output for {label}", 0.10, "gpt-4")

        mock_run.side_effect = realistic_side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **orchestrator_args
        )

        labels = _extract_step_labels(mock_run)
        cycles_run = _count_cycles(labels)

        # After cycle 2 finds 0 dev units, cycles 3-5 should NOT run.
        # The buggy code runs all 5 cycles = 45 step calls.
        # Fixed code should stop at cycle 2 or earlier = at most 18 step calls.
        assert cycles_run <= 2, (
            f"Expected at most 2 cycles (cycle 1 fixes code, cycle 2 finds 0 dev units "
            f"and stops), but {cycles_run} cycles ran. "
            f"Cycles 3+ are wasted — they find 0 dev units and make no progress. "
            f"Labels: {labels}"
        )

    def test_wasted_cycles_inflate_total_cost(
        self, e2e_orchestrator_mocks, orchestrator_args
    ):
        """The wasted cycles cause 2-3x cost inflation.

        Each cycle costs ~$0.80 (9 steps * ~$0.09/step). Running 5 cycles
        instead of 2 wastes ~$2.40. This test verifies the cost impact.
        """
        mock_run = e2e_orchestrator_mocks["mock_run"]
        orchestrator_args["max_cycles"] = 5

        step_calls = [0]

        def cost_tracking_side_effect(*args, **kwargs):
            """Each step costs $0.10 to make the math easy."""
            label = kwargs.get("label", "")
            step_calls[0] += 1

            if "step5" in label:
                return (True, "DEV_UNITS_IDENTIFIED: 0\n0 Dev Units Needed Fix", 0.10, "gpt-4")
            if "step9" in label:
                return (True, "Tests still failing. CONTINUE_CYCLE", 0.10, "gpt-4")
            return (True, f"Output for {label}", 0.10, "gpt-4")

        mock_run.side_effect = cost_tracking_side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **orchestrator_args
        )

        # With 0 dev units from the start, only 1 cycle should run.
        # Buggy code runs all 5 cycles = 45 calls * $0.10 = $4.50.
        # Fixed code should run at most 1 cycle = 9 calls * $0.10 = $0.90.
        # We allow 2 cycles for tolerance.
        max_acceptable_cost = 2 * 9 * 0.10  # 2 cycles max
        assert cost <= max_acceptable_cost, (
            f"Total cost ${cost:.2f} exceeds acceptable maximum ${max_acceptable_cost:.2f}. "
            f"With 0 dev units, at most 2 cycles should run. "
            f"Got {step_calls[0]} step calls across "
            f"{_count_cycles(_extract_step_labels(mock_run))} cycles."
        )


class TestE2ENoFileChangesConvergence:
    """E2E test for the no-progress detection bug: when a cycle makes zero
    code changes, the orchestrator should stop instead of repeating."""

    def test_full_workflow_stops_when_no_files_change_across_cycles(
        self, e2e_orchestrator_mocks, orchestrator_args
    ):
        """Simulate 3-cycle workflow where no files ever change.

        The orchestrator should detect that cycle 1 made zero code changes
        and stop before starting cycle 2.
        """
        mock_run = e2e_orchestrator_mocks["mock_run"]
        orchestrator_args["max_cycles"] = 3

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step5" in label:
                return (True, "DEV_UNITS_IDENTIFIED: auth_module\n1 dev unit needs fixing.", 0.10, "gpt-4")
            if "step9" in label:
                return (True, "Tests still failing after attempted fix. CONTINUE_CYCLE", 0.10, "gpt-4")
            return (True, f"Output for {label}", 0.10, "gpt-4")

        mock_run.side_effect = side_effect

        # _get_file_hashes returns {} every time (default from fixture),
        # meaning no files changed. The orchestrator should detect this
        # and stop instead of running 3 identical cycles.
        run_agentic_e2e_fix_orchestrator(**orchestrator_args)

        labels = _extract_step_labels(mock_run)
        cycles_run = _count_cycles(labels)

        # With zero file changes, the orchestrator should stop after cycle 1.
        # Buggy code runs all 3 cycles (27 step calls).
        assert cycles_run <= 1, (
            f"Expected at most 1 cycle when no files changed, but {cycles_run} "
            f"cycles ran ({mock_run.call_count} total step calls). "
            f"The orchestrator should detect zero progress and stop."
        )


class TestE2EStep9TestScoping:
    """E2E test verifying that the Step 9 prompt correctly scopes test
    execution to issue-related tests only, not the full test suite."""

    def test_step9_prompt_in_workflow_does_not_run_all_tests(
        self, e2e_orchestrator_mocks, orchestrator_args
    ):
        """Run a full single-cycle workflow and verify the Step 9 prompt
        that gets formatted and sent to the LLM does not contain
        'pytest tests/ -v' (which runs ALL tests)."""
        mock_run = e2e_orchestrator_mocks["mock_run"]
        mock_load = e2e_orchestrator_mocks["mock_load"]
        orchestrator_args["max_cycles"] = 1

        # Use the real Step 9 prompt template from the repo (not PDD_PATH)
        import pathlib
        repo_prompts = pathlib.Path(__file__).parent.parent / "pdd" / "prompts"

        def load_side_effect(name):
            """Load real prompts for Step 9, generic for others."""
            if "step9" in name:
                prompt_file = repo_prompts / f"{name}.prompt"
                if prompt_file.exists():
                    return prompt_file.read_text()
            return "Prompt for {issue_number}"

        mock_load.side_effect = load_side_effect

        captured_step9_prompt = []

        def capture_side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            instruction = kwargs.get("instruction", "") or (args[0] if args else "")
            if "step9" in label:
                captured_step9_prompt.append(instruction)
                return (True, "ALL_TESTS_PASS", 0.10, "gpt-4")
            if "step5" in label:
                return (True, "DEV_UNITS_IDENTIFIED: auth_module\n1 dev unit.", 0.10, "gpt-4")
            return (True, f"Output for {label}", 0.10, "gpt-4")

        mock_run.side_effect = capture_side_effect

        run_agentic_e2e_fix_orchestrator(**orchestrator_args)

        assert len(captured_step9_prompt) > 0, (
            "Step 9 was never called — test setup error"
        )

        step9_text = captured_step9_prompt[0]
        # The old buggy prompt contained "Run all unit tests: `pytest tests/ -v`"
        # The fixed prompt should NOT contain this instruction.
        assert "pytest tests/ -v" not in step9_text, (
            "Step 9 prompt sent to LLM still contains 'pytest tests/ -v' which runs "
            "ALL tests. Pre-existing failures in unrelated tests should not drive "
            "cycle decisions. The prompt should scope to issue-related tests only."
        )
