"""
E2E Test for Issue #902: No aggregate timeout or error classification in agentic provider fallback.

Bug Context:
-----------
During `pdd fix` runs, the provider fallback in run_agentic_task() has several failure
modes that waste time and money:

1. Linear backoff (docstring claims exponential): retry_delay * attempt instead of
   retry_delay * 2^(attempt-1)
2. No jitter: concurrent jobs retry at identical intervals (thundering herd)
3. No aggregate timeout: 3 providers x 3 retries = 9 * step_timeout with no cap
4. No error classification: permanent errors (auth, invalid param) retried identically
   to transient errors (rate limit, 5xx)

These E2E tests exercise the full code path from the orchestrator level through
run_agentic_task() and _run_with_provider(), mocking only at the subprocess boundary
(external CLI tools). The buggy retry/backoff/timeout logic runs unmodified.
"""

import json
import os
import re
import subprocess
import time

import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

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
def orchestrator_mocks_with_real_retry():
    """Mock orchestrator I/O but let run_agentic_task execute its real retry logic.

    Unlike the standard orchestrator_io_mocks that mock run_agentic_task itself,
    this fixture keeps run_agentic_task real and only mocks:
    - _subprocess_run: the subprocess boundary (CLI tool execution)
    - _find_cli_binary: CLI binary discovery
    - load_prompt_template: prompt file I/O
    - console (orchestrator): Rich console output from orchestrator
    - load_workflow_state / save_workflow_state / clear_workflow_state: state persistence
    - _get_file_hashes / _commit_and_push: git operations
    - _check_e2e_environment: E2E infra check
    - time.sleep in agentic_common: prevent actual waits during tests
    """
    with patch("pdd.agentic_common._subprocess_run") as mock_subprocess, \
         patch("pdd.agentic_common._find_cli_binary") as mock_which, \
         patch("pdd.agentic_common._load_model_data", return_value=None), \
         patch("pdd.agentic_common.time.sleep") as mock_sleep, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit, \
         patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check_e2e, \
         patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output", return_value=None):

        mock_which.return_value = "/bin/claude"
        mock_load.return_value = "Prompt for {issue_number}"
        mock_load_state.return_value = (None, None)
        mock_save_state.return_value = None
        mock_hashes.return_value = {}
        mock_commit.return_value = (True, "No changes to commit")
        mock_check_e2e.return_value = (True, "")

        yield {
            "subprocess": mock_subprocess,
            "which": mock_which,
            "sleep": mock_sleep,
            "console": mock_console,
        }


def _make_subprocess_success(result_text="ALL_TESTS_PASS - Task completed successfully with verified output.", cost=0.05):
    """Create a mock successful subprocess result.

    Note: result_text includes ALL_TESTS_PASS so Step 9 output triggers the
    orchestrator's loop termination token detection, preventing Cycle 2.
    """
    resp = MagicMock()
    resp.returncode = 0
    resp.stdout = json.dumps({
        "result": result_text,
        "total_cost_usd": cost,
    })
    resp.stderr = ""
    return resp


def _make_subprocess_failure(stderr="Error: unknown failure"):
    """Create a mock failed subprocess result."""
    resp = MagicMock()
    resp.returncode = 1
    resp.stdout = ""
    resp.stderr = stderr
    return resp


# ---------------------------------------------------------------------------
# E2E Test: Linear backoff (should be exponential)
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestE2EIssue902ExponentialBackoff:
    """E2E test: The orchestrator's retry path uses linear backoff instead of exponential.

    When a step fails and is retried, the backoff delays should be exponential
    (5, 10, 20, ...) not linear (5, 10, 15, ...). This test exercises the full
    orchestrator -> run_agentic_task -> _run_with_provider path and inspects the
    actual sleep calls.
    """

    def test_orchestrator_step_retries_use_exponential_backoff(
        self, mock_git_repo, orchestrator_mocks_with_real_retry
    ):
        """E2E: Orchestrator step retry delays follow exponential pattern.

        With DEFAULT_MAX_RETRIES=3, there are only 2 retry sleeps (between 3 attempts).
        Linear and exponential produce the same first 2 delays (5, 10), so we need
        at least 4 retries to distinguish them:
        - Linear (buggy):      5, 10, 15
        - Exponential (fixed): 5, 10, 20

        We patch DEFAULT_MAX_RETRIES at the orchestrator's import to 4, giving us
        3 sleep calls for the first step's retries.

        BUG: Line 865: backoff = retry_delay * attempt (linear).
        """
        mocks = orchestrator_mocks_with_real_retry
        mock_subprocess = mocks["subprocess"]
        mock_sleep = mocks["sleep"]

        call_count = [0]

        def subprocess_side_effect(*args, **kwargs):
            call_count[0] += 1
            # First 3 calls fail (step 1 retries), then all succeed
            if call_count[0] <= 3:
                return _make_subprocess_failure("Error: transient server error 500")
            return _make_subprocess_success()

        mock_subprocess.side_effect = subprocess_side_effect

        # Patch DEFAULT_MAX_RETRIES to 4 at the orchestrator's import location
        # so we get 3 sleep calls (enough to distinguish linear from exponential)
        with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test-key"}, clear=True), \
             patch("pdd.agentic_e2e_fix_orchestrator.DEFAULT_MAX_RETRIES", 4):
            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/902",
                issue_content="Test exponential backoff",
                repo_owner="test",
                repo_name="repo",
                issue_number=902,
                issue_author="test-user",
                issue_title="Exponential backoff test",
                cwd=mock_git_repo,
                verbose=False,
                quiet=True,
                max_cycles=1,
                resume=False,
                use_github_state=False,
            )

        # Extract sleep delays from step 1's retries
        sleep_delays = [c.args[0] for c in mock_sleep.call_args_list if c.args]

        # We need at least 3 delays from step 1's retries
        assert len(sleep_delays) >= 3, (
            f"Expected at least 3 sleep calls from step 1 retries, got {len(sleep_delays)}: {sleep_delays}"
        )

        # The third delay distinguishes exponential from linear:
        # Linear: 5*1, 5*2, 5*3 = 5, 10, 15
        # Exponential with additive jitter: 5*2^0 + [0, 5], 5*2^1 + [0, 5], 5*2^2 + [0, 5]
        # so the third delay must land in [20, 25]. Any value >= 20 confirms
        # exponential growth with jitter instead of the linear value 15.
        third_delay = sleep_delays[2]
        assert third_delay >= 20, (
            f"BUG DETECTED (Issue #902): Retry backoff is linear, not exponential.\n"
            f"  Sleep delays: {sleep_delays[:3]}\n"
            f"  Third delay: {third_delay} (linear: 15, exponential+jitter: [20, 25])\n"
            f"  Line 865: backoff = retry_delay * attempt (should be retry_delay * 2^(attempt-1))"
        )


# ---------------------------------------------------------------------------
# E2E Test: No jitter in retry delays
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestE2EIssue902Jitter:
    """E2E test: Retry delays have no jitter, causing thundering herd.

    When multiple jobs hit the same provider and fail, they all retry at exactly
    the same intervals. With jitter, delays should be randomized.
    """

    def test_orchestrator_retry_delays_include_jitter(
        self, mock_git_repo, orchestrator_mocks_with_real_retry
    ):
        """E2E: Two runs of the same failing step produce different sleep delays.

        BUG: On current code, delays are deterministic (no jitter).
        EXPECTED: Delays should include random jitter.
        """
        mocks = orchestrator_mocks_with_real_retry
        mock_subprocess = mocks["subprocess"]
        mock_sleep = mocks["sleep"]

        all_delays = []

        for run_idx in range(2):
            mock_sleep.reset_mock()
            mock_subprocess.reset_mock()

            step_call_count = [0]

            def subprocess_side_effect(*args, **kwargs):
                step_call_count[0] += 1
                # First 2 calls fail (retries for step 1), then all succeed
                if step_call_count[0] <= 2:
                    return _make_subprocess_failure("Error: 500 Internal Server Error")
                return _make_subprocess_success()

            mock_subprocess.side_effect = subprocess_side_effect

            with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test-key"}, clear=True):
                run_agentic_e2e_fix_orchestrator(
                    issue_url="https://github.com/test/repo/issues/902",
                    issue_content="Test jitter",
                    repo_owner="test",
                    repo_name="repo",
                    issue_number=902,
                    issue_author="test-user",
                    issue_title="Jitter test",
                    cwd=mock_git_repo,
                    verbose=False,
                    quiet=True,
                    max_cycles=1,
                    resume=False,
                    use_github_state=False,
                )

            delays = [c.args[0] for c in mock_sleep.call_args_list if c.args]
            all_delays.append(delays)

        # Both runs must have produced retry sleeps (non-vacuous assertion)
        assert len(all_delays[0]) > 0, (
            "Expected at least one retry sleep in run 1, but no sleep calls were recorded."
        )
        assert len(all_delays[1]) > 0, (
            "Expected at least one retry sleep in run 2, but no sleep calls were recorded."
        )

        # With jitter, the delays from two runs should differ
        # Without jitter (buggy), they are identical
        assert all_delays[0] != all_delays[1], (
            f"BUG DETECTED (Issue #902): Retry delays are deterministic (no jitter).\n"
            f"  Run 1 delays: {all_delays[0]}\n"
            f"  Run 2 delays: {all_delays[1]}\n"
            f"  Concurrent jobs will retry at identical intervals (thundering herd)."
        )


# ---------------------------------------------------------------------------
# E2E Test: No aggregate timeout across providers
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestE2EIssue902AggregateTimeout:
    """E2E test: No aggregate timeout across providers during orchestrator step.

    With multiple providers and retries, the total attempt count per step
    grows unbounded. An aggregate timeout should cap total elapsed time.
    """

    def test_orchestrator_step_respects_aggregate_timeout(
        self, mock_git_repo, orchestrator_mocks_with_real_retry
    ):
        """E2E: Steps that fail across all providers should be time-bounded.

        Scenario: All providers fail for every step. With time advancing 100s
        per subprocess call and default timeout of 600s, the aggregate time
        budget (2x timeout = 1200s) should be exhausted well before all
        step×provider×retry combinations are attempted.

        BUG: All attempts are made with no aggregate timeout enforcement.
        EXPECTED: Significantly fewer total attempts when aggregate timeout
        should have been exceeded.
        """
        mocks = orchestrator_mocks_with_real_retry
        mock_subprocess = mocks["subprocess"]

        # All subprocess calls fail
        mock_subprocess.return_value = _make_subprocess_failure("Error: timeout")

        # Simulate time advancing 100s per subprocess call
        original_time = time.time
        base_time = original_time()

        def fake_time():
            """Advance clock by 100s per subprocess call."""
            return base_time + (mock_subprocess.call_count * 100)

        with patch.dict(os.environ, {
            "ANTHROPIC_API_KEY": "key",
            "GEMINI_API_KEY": "key",
            "OPENAI_API_KEY": "key",
        }, clear=True):
            with patch("pdd.agentic_common.time.time", side_effect=fake_time):
                success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                    issue_url="https://github.com/test/repo/issues/902",
                    issue_content="Test aggregate timeout",
                    repo_owner="test",
                    repo_name="repo",
                    issue_number=902,
                    issue_author="test-user",
                    issue_title="Aggregate timeout test",
                    cwd=mock_git_repo,
                    verbose=False,
                    quiet=True,
                    max_cycles=1,
                    resume=False,
                    use_github_state=False,
                )

        total_attempts = mock_subprocess.call_count
        total_simulated_time = total_attempts * 100

        # With aggregate timeout, the total across all steps should be bounded.
        # Without it (buggy), the code makes every attempt regardless of elapsed time.
        # 3 steps * 9 attempts = 27 total calls without any aggregate timeout.
        # The fixed code makes 19 calls (Step 1 = 9, Step 1 retry = 9, Step 2 starts and hits budget).
        # Any value < 27 confirms that at least some attempts were capped by the aggregate budget.
        assert total_attempts < 27, (
            f"BUG DETECTED (Issue #902): {total_attempts} total subprocess calls were made "
            f"(simulated elapsed time: {total_simulated_time}s). No aggregate timeout is "
            f"enforced — cascading provider failures run unbounded (expected < 27)."
        )


# ---------------------------------------------------------------------------
# E2E Test: No error classification (permanent errors retried)
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestE2EIssue902ErrorClassification:
    """E2E test: Permanent errors (auth, invalid param) get identical retry treatment.

    When a provider returns an auth failure or invalid parameter error, the code
    should fail fast and move to the next provider. Instead, it retries identically
    to transient errors, wasting time and money.
    """

    def test_orchestrator_auth_failure_not_retried(
        self, mock_git_repo, orchestrator_mocks_with_real_retry
    ):
        """E2E: Auth failure should not trigger retries across the workflow.

        Scenario: Every subprocess call returns an auth failure. With
        DEFAULT_MAX_RETRIES=3, each step gets 2 retry sleeps (between 3 attempts).
        With 9 steps × 2 sleeps = 18 total sleeps on buggy code.

        BUG: Auth failures trigger retry sleeps identical to transient errors.
        EXPECTED: Auth failure (permanent) should skip retries — 0 sleeps total.
        """
        mocks = orchestrator_mocks_with_real_retry
        mock_subprocess = mocks["subprocess"]
        mock_sleep = mocks["sleep"]

        # All calls return auth failure
        mock_subprocess.return_value = _make_subprocess_failure(
            "Exit code 1: authentication failed - invalid API key"
        )

        with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test-key"}, clear=True):
            run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/902",
                issue_content="Test error classification",
                repo_owner="test",
                repo_name="repo",
                issue_number=902,
                issue_author="test-user",
                issue_title="Error classification test",
                cwd=mock_git_repo,
                verbose=False,
                quiet=True,
                max_cycles=1,
                resume=False,
                use_github_state=False,
            )

        # Auth failure is permanent — should not trigger retry sleeps.
        sleep_count = mock_sleep.call_count
        assert sleep_count == 0, (
            f"BUG DETECTED (Issue #902): Auth failure (permanent error) triggered "
            f"{sleep_count} retry sleep(s) across the workflow. Permanent errors "
            f"should fail fast without retrying — each retry wastes time on an "
            f"error that will never succeed."
        )

    def test_orchestrator_rate_limit_retried_and_succeeds(
        self, mock_git_repo, orchestrator_mocks_with_real_retry
    ):
        """E2E: Rate limit (transient) should still be retried and succeed.

        Scenario: Each step's first subprocess call gets rate limited, second succeeds.
        This verifies that transient error retry behavior (which is correct) is preserved.
        """
        mocks = orchestrator_mocks_with_real_retry
        mock_subprocess = mocks["subprocess"]

        def subprocess_side_effect(*args, **kwargs):
            """Alternate: odd calls fail with rate limit, even calls succeed."""
            current = mock_subprocess.call_count
            if current % 2 == 1:
                return _make_subprocess_failure("Error: 429 Too Many Requests - rate limit exceeded")
            return _make_subprocess_success()

        mock_subprocess.side_effect = subprocess_side_effect

        with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test-key"}, clear=True):
            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/902",
                issue_content="Test rate limit retry",
                repo_owner="test",
                repo_name="repo",
                issue_number=902,
                issue_author="test-user",
                issue_title="Rate limit retry test",
                cwd=mock_git_repo,
                verbose=False,
                quiet=True,
                max_cycles=1,
                resume=False,
                use_github_state=False,
            )

        # Rate limit is transient — should be retried and eventually succeed
        assert success, (
            "Rate limit errors (transient) should be retried and succeed. "
            "This behavior should be preserved by the fix."
        )
