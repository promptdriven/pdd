"""
E2E Test for Issue #791: pdd fix E2E test step times out on every cycle

Bug Context:
-----------
During `pdd fix`, Step 2 (E2E test check) times out on every cycle with
"All agent providers failed: anthropic: Timeout expired". The E2E tests
require playwright/browser/dev-server that the executor VM doesn't have.
The step is architecturally unable to succeed, yet it is retried identically
on every cycle because:

1. No pre-flight check exists to detect missing E2E infrastructure
2. step_outputs is cleared between cycles (line 859), destroying failure memory

This wastes ~15-20 minutes per timeout, accumulating ~45-60 minutes over 3 cycles.

These E2E tests exercise the full orchestrator code path (run_agentic_e2e_fix_orchestrator)
with minimal mocking — only external I/O (LLM calls, state persistence, console) is mocked.
The buggy orchestrator logic itself runs unmodified.
"""

import re
import subprocess

import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator


@pytest.fixture
def mock_git_repo(tmp_path):
    """Create a minimal git repository for testing the orchestrator."""
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()

    subprocess.run(["git", "init", "-b", "main"], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=repo_path, check=True, capture_output=True)

    pdd_dir = repo_path / ".pdd"
    pdd_dir.mkdir()

    (repo_path / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_path, check=True, capture_output=True)

    return repo_path


@pytest.fixture
def orchestrator_io_mocks():
    """Mock only external I/O for the orchestrator — not the buggy logic.

    Mocks:
    - run_agentic_task: LLM task execution (external API)
    - load_prompt_template: Prompt file I/O
    - console: Rich console output
    - load_workflow_state / save_workflow_state / clear_workflow_state: State persistence
    - _get_file_hashes: Git filesystem operations
    - _commit_and_push: Git push operations
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
         patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output", return_value=None):

        mock_load.return_value = "Prompt for {issue_number}"
        mock_load_state.return_value = (None, None)
        mock_save_state.return_value = None
        mock_hashes.return_value = {}
        mock_commit.return_value = (True, "No changes to commit")
        mock_check_e2e.return_value = (True, "")  # Default: E2E environment available

        yield {
            "run": mock_run,
            "load": mock_load,
            "console": mock_console,
            "check_e2e": mock_check_e2e,
        }


@pytest.mark.e2e
class TestIssue791E2ETimeoutRetry:
    """
    E2E tests for Issue #791: Step 2 timeout retried on every cycle.

    These tests exercise the real orchestrator loop logic to demonstrate
    that Step 2 timeouts are not remembered across cycles.
    """

    def test_step2_timeout_retried_every_cycle(self, mock_git_repo, orchestrator_io_mocks):
        """
        E2E Bug Reproduction: Step 2 times out identically on every cycle.

        Scenario: Step 2 returns a timeout error. The orchestrator should
        remember this failure and skip Step 2 on subsequent cycles.

        BUG: On current code, step_outputs is cleared between cycles (line 859),
        so Step 2 is dispatched to the LLM agent again in cycle 2 and cycle 3,
        each time consuming a full timeout.

        This test FAILS on the buggy code because Step 2 is dispatched 3 times
        (once per cycle) instead of just once.
        """
        mock_run = orchestrator_io_mocks["run"]

        step2_dispatch_count = 0

        def side_effect(*args, **kwargs):
            nonlocal step2_dispatch_count
            label = kwargs.get('label', '')

            if 'step2' in label:
                step2_dispatch_count += 1
                # Simulate the real bug: timeout on E2E test step
                return (False, "All agent providers failed: anthropic: Timeout expired", 0.1, "gpt-4")

            if 'step9' in label:
                # Cycle 1-2: continue, Cycle 3: max reached
                if 'cycle1' in label or 'cycle2' in label:
                    return (True, "CONTINUE_CYCLE", 0.1, "gpt-4")
                return (True, "MAX_CYCLES_REACHED", 0.1, "gpt-4")

            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            issue_url="https://github.com/test/repo/issues/791",
            issue_content="E2E test step times out on every cycle",
            repo_owner="test",
            repo_name="repo",
            issue_number=791,
            issue_author="test-user",
            issue_title="E2E timeout retry bug",
            cwd=mock_git_repo,
            verbose=False,
            quiet=True,
            max_cycles=3,
            resume=False,
            use_github_state=False,
        )

        # The fix should ensure Step 2 is only dispatched ONCE.
        # On the buggy code, it is dispatched 3 times (once per cycle).
        assert step2_dispatch_count == 1, (
            f"BUG DETECTED (Issue #791): Step 2 was dispatched {step2_dispatch_count} times "
            f"across 3 cycles. After timing out in cycle 1, it should be remembered as "
            f"'skipped' and not retried in cycles 2-3. This wastes ~15-20 min per timeout.\n"
            f"Root cause: step_outputs is cleared between cycles (line 859), "
            f"destroying the timeout failure memory."
        )

    def test_step2_consumes_timeout_without_preflight(self, mock_git_repo, orchestrator_io_mocks):
        """
        E2E Bug Reproduction: Step 2 is dispatched to LLM without pre-flight check.

        Scenario: The executor environment has no playwright/browser/dev-server.
        Step 2 should detect this BEFORE dispatching to the LLM agent.

        BUG: On current code, there is no _check_e2e_environment function.
        Step 2 always dispatches to the LLM, which then tries to run E2E tests
        in an environment that can't support them, consuming a full 240s timeout.

        This test FAILS on the buggy code because Step 2 IS dispatched to the
        LLM agent even though no E2E environment exists.
        """
        mock_run = orchestrator_io_mocks["run"]

        steps_dispatched = []

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            match = re.search(r'step(\d+)', label)
            if match:
                steps_dispatched.append(int(match.group(1)))

            if 'step2' in label:
                return (True, "E2E tests executed", 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        # Patch _check_e2e_environment to simulate missing E2E infra.
        # On buggy code, this function doesn't exist, so the patch target
        # will raise AttributeError — which IS the bug.
        try:
            with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check:
                mock_check.return_value = (False, "playwright not installed; no dev server on localhost:3000")

                success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                    issue_url="https://github.com/test/repo/issues/791",
                    issue_content="E2E test step times out",
                    repo_owner="test",
                    repo_name="repo",
                    issue_number=791,
                    issue_author="test-user",
                    issue_title="E2E timeout",
                    cwd=mock_git_repo,
                    verbose=False,
                    quiet=True,
                    max_cycles=1,
                    resume=False,
                    use_github_state=False,
                )

                # Verify Step 2 was NOT dispatched to LLM
                assert 2 not in steps_dispatched, (
                    f"BUG DETECTED (Issue #791): Step 2 was dispatched to the LLM agent "
                    f"despite E2E environment being unavailable. Steps dispatched: {steps_dispatched}\n"
                    f"Expected: _check_e2e_environment should prevent Step 2 dispatch."
                )

        except AttributeError as e:
            if "_check_e2e_environment" in str(e):
                pytest.fail(
                    "BUG DETECTED (Issue #791): _check_e2e_environment function does not exist "
                    "in the orchestrator module. Without this pre-flight check, Step 2 always "
                    "dispatches E2E tests to the LLM agent, consuming a full 240s timeout "
                    "in environments without playwright/browser/dev-server infrastructure."
                )
            raise

    def test_full_workflow_cost_with_repeated_timeouts(self, mock_git_repo, orchestrator_io_mocks):
        """
        E2E Cost Impact: Measure wasted cost from repeated Step 2 timeouts.

        Scenario: Step 2 times out on each cycle. The test verifies total cost
        includes repeated Step 2 timeout costs (demonstrating waste).

        After fix: Step 2 should only incur cost once, then be skipped (zero cost).
        """
        mock_run = orchestrator_io_mocks["run"]

        STEP2_TIMEOUT_COST = 0.50  # Simulated cost per Step 2 timeout

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')

            if 'step2' in label:
                return (False, "All agent providers failed: anthropic: Timeout expired", STEP2_TIMEOUT_COST, "gpt-4")
            if 'step9' in label:
                if 'cycle1' in label or 'cycle2' in label:
                    return (True, "CONTINUE_CYCLE", 0.05, "gpt-4")
                return (True, "MAX_CYCLES_REACHED", 0.05, "gpt-4")
            return (True, f"Output for {label}", 0.05, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, total_cost, model, files = run_agentic_e2e_fix_orchestrator(
            issue_url="https://github.com/test/repo/issues/791",
            issue_content="E2E test step times out on every cycle",
            repo_owner="test",
            repo_name="repo",
            issue_number=791,
            issue_author="test-user",
            issue_title="E2E timeout retry bug",
            cwd=mock_git_repo,
            verbose=False,
            quiet=True,
            max_cycles=3,
            resume=False,
            use_github_state=False,
        )

        # Count how many Step 2 timeout costs were incurred
        step2_calls = [c for c in mock_run.call_args_list if 'step2' in c.kwargs.get('label', '')]
        step2_total_cost = len(step2_calls) * STEP2_TIMEOUT_COST

        # After fix: Step 2 should only cost $0.50 (1 timeout, then skipped).
        # On buggy code: Step 2 costs $1.50 (3 timeouts, $0.50 each).
        assert step2_total_cost <= STEP2_TIMEOUT_COST, (
            f"BUG DETECTED (Issue #791): Step 2 timeout cost ${step2_total_cost:.2f} "
            f"across {len(step2_calls)} dispatch(es). Expected at most ${STEP2_TIMEOUT_COST:.2f} "
            f"(1 timeout, then skipped). Wasted: ${step2_total_cost - STEP2_TIMEOUT_COST:.2f}.\n"
            f"Total workflow cost: ${total_cost:.2f}"
        )
