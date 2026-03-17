"""
E2E Test for Issue #830: pdd-fix workflow silently stalls after Step 9

Bug Context:
-----------
The pdd-fix (e2e_fix) workflow has three distinct bugs that together cause
silent stalls and wasted compute:

1. Step 9 missing loop control token: When Step 9 output has no recognized
   loop control token (ALL_TESTS_PASS, CONTINUE_CYCLE, MAX_CYCLES_REACHED),
   the orchestrator defaults to CONTINUE_CYCLE, starting an unnecessary Cycle 2.

2. subprocess.run() missing start_new_session=True: Timeout kills only the
   direct child process. Grandchild processes spawned by CLI tools become
   orphans and hang indefinitely (e.g., Cycle 2 Step 2 hung permanently).

3. save_workflow_state() returns stale github_comment_id when GitHub save
   fails, causing GitHub issue comments to diverge from actual execution state.

These E2E tests exercise the full orchestrator code path (run_agentic_e2e_fix_orchestrator)
with minimal mocking — only external I/O (LLM calls, state persistence, console) is mocked.
The buggy orchestrator logic itself runs unmodified.
"""

import re
import subprocess

import pytest
from unittest.mock import patch, MagicMock, call
from pathlib import Path

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator
from pdd.agentic_common import save_workflow_state


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
    - _check_e2e_environment: E2E infra check
    """
    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit, \
         patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check_e2e:

        mock_load.return_value = "Prompt for {issue_number}"
        mock_load_state.return_value = (None, None)
        mock_save_state.return_value = None
        mock_hashes.return_value = {}
        mock_commit.return_value = (True, "No changes to commit")
        mock_check_e2e.return_value = (True, "")

        yield {
            "run": mock_run,
            "load": mock_load,
            "console": mock_console,
            "save_state": mock_save_state,
            "check_e2e": mock_check_e2e,
        }


@pytest.mark.e2e
class TestIssue830NoLoopControlTokenE2E:
    """
    E2E tests for Bug 1: Step 9 missing loop control token causes unnecessary Cycle 2.

    When Step 9 output has no recognized token, the orchestrator should
    treat it as terminal and break. On the buggy code, it defaults to
    CONTINUE_CYCLE and starts Cycle 2.
    """

    def test_missing_token_causes_unnecessary_cycle2(self, mock_git_repo, orchestrator_io_mocks):
        """
        E2E Bug Reproduction: Step 9 with no loop control token starts Cycle 2.

        Scenario: All 9 steps complete in Cycle 1. Step 9 returns verification
        output but no control token. On buggy code, the orchestrator logs a
        warning and falls through to cycle increment, starting Cycle 2.

        This test FAILS on the buggy code because Cycle 2 steps are executed.
        """
        mock_run = orchestrator_io_mocks["run"]

        cycles_started = []
        steps_per_cycle = {}

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            # Track which cycle/step is being executed
            cycle_match = re.search(r'cycle(\d+)', label)
            step_match = re.search(r'step(\d+)', label)
            if cycle_match and step_match:
                cycle = int(cycle_match.group(1))
                step = int(step_match.group(1))
                if cycle not in steps_per_cycle:
                    steps_per_cycle[cycle] = []
                    cycles_started.append(cycle)
                steps_per_cycle[cycle].append(step)

            if 'step9' in label:
                # Real scenario from issue #830: Step 9 output with NO control token
                return (True, "Verification complete. 3 tests pass, 0 failures.", 0.26, "claude-3-opus")
            return (True, f"Output for {label}", 0.10, "claude-3-opus")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            issue_url="https://github.com/test/repo/issues/830",
            issue_content="Workflow stalls after Step 9 missing loop control token",
            repo_owner="test",
            repo_name="repo",
            issue_number=830,
            issue_author="test-user",
            issue_title="Workflow stall after Step 9",
            cwd=mock_git_repo,
            verbose=False,
            quiet=True,
            max_cycles=3,
            resume=False,
            use_github_state=False,
        )

        # Bug: orchestrator starts Cycle 2 because it defaults to CONTINUE_CYCLE
        # Fix: missing token should be treated as terminal (break)
        assert len(cycles_started) == 1, (
            f"BUG DETECTED (Issue #830 Bug 1): Orchestrator started {len(cycles_started)} cycles "
            f"({cycles_started}) when Step 9 had no loop control token. "
            f"Expected 1 cycle only — missing token should break the loop, not default to CONTINUE_CYCLE.\n"
            f"Steps per cycle: {steps_per_cycle}"
        )

    def test_full_workflow_reproduces_production_stall(self, mock_git_repo, orchestrator_io_mocks):
        """
        E2E Bug Reproduction: Full reproduction of production issue #824 stall.

        Simulates the exact sequence from Cloud Run logs:
        - Cycle 1: Steps 1-8 succeed, Step 9 returns no control token
        - Cycle 2: Step 1 succeeds, Step 2 times out (hangs)

        On buggy code, this runs Cycle 2 and Step 2 is dispatched.
        On fixed code, the loop should break after Cycle 1 Step 9.
        """
        mock_run = orchestrator_io_mocks["run"]

        cycle2_step2_reached = False

        def side_effect(*args, **kwargs):
            nonlocal cycle2_step2_reached
            label = kwargs.get('label', '')

            # Cycle 1 Step 1: timeout (matches production)
            if label == "cycle1_step1":
                return (False, "All agent providers failed: anthropic: Timeout expired", 0.0, "claude-3-opus")

            # Cycle 1 Steps 2-8: succeed normally
            if 'cycle1' in label and 'step9' not in label:
                return (True, f"Output for {label}", 0.10, "claude-3-opus")

            # Cycle 1 Step 9: no loop control token (the bug trigger)
            if label == "cycle1_step9":
                return (True, "Final verification complete. Tests checked.", 0.26, "claude-3-opus")

            # Cycle 2 Step 2: this should NOT be reached
            if label == "cycle2_step2":
                cycle2_step2_reached = True
                # Simulate the hang from production (return timeout)
                return (False, "All agent providers failed: anthropic: Timeout expired", 0.50, "claude-3-opus")

            # Cycle 2 Step 9
            if 'cycle2' in label and 'step9' in label:
                return (True, "MAX_CYCLES_REACHED", 0.05, "claude-3-opus")

            return (True, f"Output for {label}", 0.05, "claude-3-opus")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            issue_url="https://github.com/test/repo/issues/830",
            issue_content="Workflow stalls - reproduction of issue #824",
            repo_owner="test",
            repo_name="repo",
            issue_number=830,
            issue_author="test-user",
            issue_title="Production stall reproduction",
            cwd=mock_git_repo,
            verbose=False,
            quiet=True,
            max_cycles=3,
            resume=False,
            use_github_state=False,
        )

        assert not cycle2_step2_reached, (
            "BUG DETECTED (Issue #830): Cycle 2 Step 2 was reached after Step 9 had no "
            "loop control token. This is the exact production failure: Cycle 2 Step 2 hung "
            "indefinitely in Cloud Run. The orchestrator should have broken out of the loop "
            "after Cycle 1 Step 9."
        )

    def test_missing_token_total_cost_limited_to_one_cycle(self, mock_git_repo, orchestrator_io_mocks):
        """
        E2E Cost Impact: Missing token should not double the cost via Cycle 2.

        In production (issue #824), the unnecessary Cycle 2 added ~$0.75 in
        wasted spend before hanging. With the fix, cost should be limited to
        a single cycle.
        """
        mock_run = orchestrator_io_mocks["run"]

        COST_PER_STEP = 0.10
        STEP9_COST = 0.26

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "Verification done. No token.", STEP9_COST, "claude-3-opus")
            return (True, f"Output for {label}", COST_PER_STEP, "claude-3-opus")

        mock_run.side_effect = side_effect

        success, msg, total_cost, model, files = run_agentic_e2e_fix_orchestrator(
            issue_url="https://github.com/test/repo/issues/830",
            issue_content="Cost test for missing token",
            repo_owner="test",
            repo_name="repo",
            issue_number=830,
            issue_author="test-user",
            issue_title="Cost test",
            cwd=mock_git_repo,
            verbose=False,
            quiet=True,
            max_cycles=3,
            resume=False,
            use_github_state=False,
        )

        # 1 cycle = 8 steps at $0.10 + 1 step at $0.26 = $1.06
        one_cycle_cost = (8 * COST_PER_STEP) + STEP9_COST
        # Allow small margin for floating point
        assert total_cost <= one_cycle_cost + 0.01, (
            f"BUG DETECTED (Issue #830): Total cost ${total_cost:.2f} exceeds single cycle "
            f"cost ${one_cycle_cost:.2f}. Missing loop control token caused unnecessary "
            f"additional cycles, wasting budget."
        )


@pytest.mark.e2e
class TestIssue830SubprocessTimeoutE2E:
    """
    E2E tests for Bug 2: subprocess.run missing start_new_session=True.

    When a subprocess times out, only the direct child is killed. Without
    start_new_session=True, grandchild processes from CLI tools (claude, gemini)
    become orphans and hang the container indefinitely.
    """

    def test_run_agentic_task_timeout_kills_process_group(self, mock_git_repo):
        """
        E2E Bug Detection: Verify subprocess.run uses start_new_session=True.

        This test inspects the actual subprocess.run call in _run_with_provider
        to verify it includes start_new_session=True for proper process group
        cleanup on timeout.
        """
        import inspect
        from pdd.agentic_common import _run_with_provider

        source = inspect.getsource(_run_with_provider)

        # Check that subprocess.run call includes start_new_session=True
        # The function has a single subprocess.run call that needs this kwarg
        assert "start_new_session=True" in source or "start_new_session = True" in source, (
            "BUG DETECTED (Issue #830 Bug 2): _run_with_provider's subprocess.run() call "
            "does not include start_new_session=True. When a timeout kills the direct child "
            "process, grandchild processes (from CLI tools like 'claude' or 'gemini') become "
            "orphans and hang indefinitely. This caused Cycle 2 Step 2 to hang permanently "
            "in production (Cloud Run execution pdd-executor-job-728mc).\n"
            "Fix: add start_new_session=True to subprocess.run(), matching the pattern in "
            "sync_orchestration.py and fix_code_loop.py."
        )


@pytest.mark.e2e
class TestIssue830StateDivergenceE2E:
    """
    E2E tests for Bug 3: save_workflow_state returns stale ID on GitHub failure.

    The orchestrator calls save_workflow_state() after each step. When GitHub
    save fails, the function returns the old github_comment_id instead of None,
    making the orchestrator think the save succeeded. This causes GitHub issue
    comments to show last_completed_step: 3 while local state is at step 9.
    """

    def test_state_divergence_through_full_workflow(self, mock_git_repo, orchestrator_io_mocks):
        """
        E2E Bug Reproduction: GitHub state diverges from local state.

        Simulates the production scenario: GitHub save fails silently after
        Step 3. The orchestrator continues to Step 9, but save_workflow_state
        returns the stale comment_id, so the caller can't detect the failure.

        On buggy code: save_workflow_state returns stale ID (12345), not None.
        On fixed code: save_workflow_state returns None when GitHub save fails.
        """
        mock_save = orchestrator_io_mocks["save_state"]

        # Simulate: GitHub save works for steps 1-3, then fails for steps 4-9
        github_save_results = {}
        stale_comment_id = 12345

        call_counter = [0]

        def save_side_effect(*args, **kwargs):
            call_counter[0] += 1
            step = call_counter[0]
            if step <= 3:
                # First 3 saves succeed
                return stale_comment_id
            else:
                # Steps 4+ fail: simulate GitHub save returning None
                # On buggy code, save_workflow_state returns stale_comment_id anyway
                return None

        mock_save.side_effect = save_side_effect

        mock_run = orchestrator_io_mocks["run"]

        def run_side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.10, "claude-3-opus")
            return (True, f"Output for {label}", 0.10, "claude-3-opus")

        mock_run.side_effect = run_side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            issue_url="https://github.com/test/repo/issues/830",
            issue_content="State divergence test",
            repo_owner="test",
            repo_name="repo",
            issue_number=830,
            issue_author="test-user",
            issue_title="State divergence test",
            cwd=mock_git_repo,
            verbose=False,
            quiet=True,
            max_cycles=1,
            resume=False,
            use_github_state=True,
        )

        # The workflow should complete successfully (ALL_TESTS_PASS in Step 9)
        assert success, f"Expected workflow success but got: {msg}"

        # Now test the underlying save_workflow_state function directly
        # to verify it returns None (not stale ID) when GitHub save fails
        from pdd.agentic_common import save_workflow_state as real_save

        state = {"last_completed_step": 9, "step_outputs": {}}
        state_dir = mock_git_repo / ".pdd" / "state"

        with patch("pdd.agentic_common._should_use_github_state") as mock_should, \
             patch("pdd.agentic_common.github_save_state") as mock_gh_save:
            mock_should.return_value = True
            mock_gh_save.return_value = None  # GitHub save fails

            result = real_save(
                cwd=mock_git_repo,
                issue_number=830,
                workflow_type="e2e_fix",
                state=state,
                state_dir=state_dir,
                repo_owner="test",
                repo_name="repo",
                use_github_state=True,
                github_comment_id=stale_comment_id,
            )

        assert result is None or result != stale_comment_id, (
            f"BUG DETECTED (Issue #830 Bug 3): save_workflow_state returned stale "
            f"comment_id {result} when GitHub save failed. Should return None so the "
            f"orchestrator can detect state divergence. In production, this caused "
            f"GitHub to show last_completed_step: 3 while local state was at step 9."
        )

    def test_save_workflow_state_propagates_failure(self, mock_git_repo):
        """
        E2E Bug Detection: save_workflow_state must propagate GitHub failure.

        Direct test of the save_workflow_state function with a failed GitHub save.
        This is the core of Bug 3 — the function masks failures by returning
        the stale github_comment_id.
        """
        state_dir = mock_git_repo / ".pdd" / "state"
        state = {"last_completed_step": 7, "step_outputs": {"7": "ok"}}
        stale_id = 99999

        with patch("pdd.agentic_common._should_use_github_state") as mock_should, \
             patch("pdd.agentic_common.github_save_state") as mock_gh_save:
            mock_should.return_value = True
            mock_gh_save.return_value = None  # GitHub API failed

            result = save_workflow_state(
                cwd=mock_git_repo,
                issue_number=830,
                workflow_type="e2e_fix",
                state=state,
                state_dir=state_dir,
                repo_owner="test",
                repo_name="repo",
                use_github_state=True,
                github_comment_id=stale_id,
            )

        # Local state should be saved regardless
        local_file = state_dir / "e2e_fix_state_830.json"
        assert local_file.exists(), "Local state file should always be saved"

        # But the return value must signal the GitHub failure
        assert result != stale_id, (
            f"BUG DETECTED (Issue #830 Bug 3): save_workflow_state returned stale "
            f"github_comment_id {stale_id} instead of None when GitHub save failed. "
            f"This masks the failure — the orchestrator continues thinking GitHub "
            f"state is in sync when it's actually stuck at an earlier step."
        )
