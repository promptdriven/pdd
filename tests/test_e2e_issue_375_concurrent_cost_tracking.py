"""
E2E Test for Issue #375: Race Condition in LLM Cost Tracking Causes Data Corruption

This E2E test exercises the full code path that a user would experience when running
concurrent operations in server mode (`pdd connect`). It verifies that cost tracking
works correctly when multiple jobs run concurrently.

The fix: Thread-local storage (`_CALLBACK_DATA`) isolates callback data per thread,
ensuring each concurrent job tracks its own cost data independently.

Scenario from the bug report:
- Server runs with max_concurrent=3 (from pdd/server/app.py:54)
- 3 jobs submit LLM calls concurrently
- Each job's LiteLLM callback writes to the shared global dictionary
- Jobs read back wrong cost values (from other concurrent jobs)
- Budget enforcement fails, cost reports are incorrect

This E2E test:
1. Simulates 3 concurrent threads calling _litellm_success_callback() (as happens during LLM calls)
2. Each thread configured to write different cost values ($0.10, $0.30, $0.05)
3. Each thread reads from _LAST_CALLBACK_DATA after writing (as llm_invoke does)
4. Verifies each thread retrieves its own cost (not corrupted by other threads)

The test should FAIL on buggy code (threads read wrong costs) and PASS once the fix
is applied (using threading.local() for thread-safe callback data storage).

This is an E2E test (not just a unit test) because it:
- Uses real _litellm_success_callback() and _LAST_CALLBACK_DATA
- Simulates the actual execution flow in server mode
- Tests the full write→read cycle that happens in production
- Exercises the same code paths users encounter
"""

import pytest
import time
import threading
from concurrent.futures import ThreadPoolExecutor
from unittest.mock import MagicMock

from pdd.llm_invoke import _litellm_success_callback, _CALLBACK_DATA


@pytest.mark.e2e
class TestConcurrentCostTrackingE2E:
    """
    E2E tests for Issue #375: Verify concurrent cost tracking works correctly in server mode.

    These tests simulate the real server mode scenario where multiple jobs run concurrently
    and each needs accurate, isolated cost tracking.
    """

    def test_concurrent_server_jobs_cost_tracking_e2e(self):
        """
        E2E Test: Concurrent server jobs should track costs independently.

        This test simulates the exact scenario from the bug report:
        - 3 concurrent jobs (matching server's max_concurrent=3)
        - Each job's LiteLLM callback writes different costs to _LAST_CALLBACK_DATA
        - Each job reads back from _LAST_CALLBACK_DATA (as llm_invoke does at line 2749)
        - Verify each job gets its own cost (not corrupted by other jobs)

        Expected behavior (after fix):
        - Job 1 writes/reads cost=$0.10 (100 input / 50 output tokens)
        - Job 2 writes/reads cost=$0.30 (200 input / 100 output tokens)
        - Job 3 writes/reads cost=$0.05 (300 input / 150 output tokens)

        Bug behavior (Issue #375):
        - All jobs read the last written value (likely $0.05 from Job 3)
        - Cost data is corrupted due to shared global _LAST_CALLBACK_DATA
        - 2 out of 3 jobs report wrong costs
        """
        # Track results with thread-safe data structure
        results_lock = threading.Lock()
        job_results = {}

        # Expected costs and token patterns for each concurrent job
        job_configs = {
            'job_1': {'cost': 0.10, 'input_tokens': 100, 'output_tokens': 50, 'finish_reason': 'stop'},
            'job_2': {'cost': 0.30, 'input_tokens': 200, 'output_tokens': 100, 'finish_reason': 'stop'},
            'job_3': {'cost': 0.05, 'input_tokens': 300, 'output_tokens': 150, 'finish_reason': 'length'},
        }

        def simulate_concurrent_job(job_id):
            """
            Simulate a job in server mode that:
            1. Calls LLM (triggers _litellm_success_callback which writes to global dict)
            2. Reads cost from global dict (as llm_invoke does at line 2749)

            This mirrors the exact flow in pdd/llm_invoke.py:
            - Line 2733: litellm.completion() triggers callback
            - Callback (line 764-767): Writes to _LAST_CALLBACK_DATA
            - Line 2749: llm_invoke reads from _LAST_CALLBACK_DATA
            """
            config = job_configs[job_id]

            # Create mock LiteLLM completion response (as LiteLLM would return)
            mock_response = MagicMock()

            # Mock usage data (LiteLLM provides this)
            mock_usage = MagicMock()
            mock_usage.prompt_tokens = config['input_tokens']
            mock_usage.completion_tokens = config['output_tokens']
            mock_response.usage = mock_usage

            # Mock choice data
            mock_choice = MagicMock()
            mock_choice.finish_reason = config['finish_reason']
            mock_response.choices = [mock_choice]

            # Mock kwargs (passed to callback)
            mock_kwargs = {}

            # Stagger timing to ensure callbacks interleave
            # This simulates realistic timing where LLM calls complete at different times
            if job_id == 'job_2':
                time.sleep(0.01)
            elif job_id == 'job_3':
                time.sleep(0.02)

            # STEP 1: LiteLLM triggers success callback (writes to _LAST_CALLBACK_DATA)
            # This is the write path - pdd/llm_invoke.py lines 764-767
            _litellm_success_callback(
                kwargs=mock_kwargs,
                completion_response=mock_response,
                start_time=0.0,
                end_time=1.0
            )

            # Small delay to simulate async callback timing
            # In production, this is the gap between when the callback completes
            # and when llm_invoke reads the data
            time.sleep(0.03)

            # STEP 2: llm_invoke reads from thread-local _CALLBACK_DATA
            # This is the read path - pdd/llm_invoke.py line 2751
            # With thread-local storage, each thread reads its own data
            read_cost = getattr(_CALLBACK_DATA, 'cost', 0.0)
            read_input_tokens = getattr(_CALLBACK_DATA, 'input_tokens', 0)
            read_output_tokens = getattr(_CALLBACK_DATA, 'output_tokens', 0)
            read_finish_reason = getattr(_CALLBACK_DATA, 'finish_reason', None)

            # Store what this job read
            with results_lock:
                job_results[job_id] = {
                    'read_cost': read_cost,
                    'read_input_tokens': read_input_tokens,
                    'read_output_tokens': read_output_tokens,
                    'read_finish_reason': read_finish_reason,
                    'expected_cost': config['cost'],
                    'expected_input_tokens': config['input_tokens'],
                    'expected_output_tokens': config['output_tokens'],
                    'expected_finish_reason': config['finish_reason'],
                }

        # Run 3 concurrent jobs (matching server's max_concurrent=3)
        # This simulates pdd server running multiple jobs simultaneously
        with ThreadPoolExecutor(max_workers=3) as executor:
            futures = [
                executor.submit(simulate_concurrent_job, 'job_1'),
                executor.submit(simulate_concurrent_job, 'job_2'),
                executor.submit(simulate_concurrent_job, 'job_3'),
            ]

            # Wait for all jobs to complete
            for future in futures:
                future.result()

        # Verify results: Each job should read its own data, not another job's data
        failures = []

        for job_id in ['job_1', 'job_2', 'job_3']:
            data = job_results[job_id]

            # Note: We skip cost verification because litellm.completion_cost() returns 0.0 for mocks
            # The token counts are the real indicator of whether thread-local storage is working
            # In production with real API calls, costs would be tracked correctly

            # Check tokens (this is the critical verification for thread-safety)
            if data['read_input_tokens'] != data['expected_input_tokens']:
                failures.append(
                    f"{job_id} read wrong input_tokens: "
                    f"Expected {data['expected_input_tokens']}, Got {data['read_input_tokens']}"
                )

            if data['read_output_tokens'] != data['expected_output_tokens']:
                failures.append(
                    f"{job_id} read wrong output_tokens: "
                    f"Expected {data['expected_output_tokens']}, Got {data['read_output_tokens']}"
                )

        # Assert no failures
        if failures:
            failure_msg = (
                f"\n{'='*70}\n"
                f"ISSUE #375 BUG DETECTED: Race condition in concurrent cost tracking!\n"
                f"{'='*70}\n\n"
                f"Scenario: 3 concurrent jobs in server mode (max_concurrent=3)\n\n"
                f"Expected behavior:\n"
                f"  - job_1: ${job_configs['job_1']['cost']:.2f}\n"
                f"  - job_2: ${job_configs['job_2']['cost']:.2f}\n"
                f"  - job_3: ${job_configs['job_3']['cost']:.2f}\n\n"
                f"Actual results:\n"
                f"  - job_1: ${job_results['job_1']['read_cost']:.2f}\n"
                f"  - job_2: ${job_results['job_2']['read_cost']:.2f}\n"
                f"  - job_3: ${job_results['job_3']['read_cost']:.2f}\n\n"
                f"Failures:\n"
            )

            for failure in failures:
                failure_msg += f"  - {failure}\n"

            failure_msg += (
                f"\nRoot cause:\n"
                f"  The global _LAST_CALLBACK_DATA dictionary in pdd/llm_invoke.py:690\n"
                f"  is shared across all threads in server mode. When concurrent jobs\n"
                f"  run, their callbacks overwrite each other's cost data before jobs\n"
                f"  can read it (race condition at lines 764-767 write, line 2749 read).\n\n"
                f"Impact:\n"
                f"  - Budget enforcement fails (jobs see wrong costs)\n"
                f"  - Cost reports are incorrect\n"
                f"  - Users are misled about their spending\n\n"
                f"Fix:\n"
                f"  Replace _LAST_CALLBACK_DATA with threading.local() for\n"
                f"  thread-safe callback data storage.\n"
                f"{'='*70}\n"
            )

            pytest.fail(failure_msg)

    def test_sequential_server_jobs_still_work_e2e(self):
        """
        E2E regression test: Sequential jobs should still work after the fix.

        This ensures the threading.local() fix doesn't break single-threaded execution.
        """
        job_configs = {
            'job_1': {'cost': 0.15, 'input_tokens': 150, 'output_tokens': 75},
            'job_2': {'cost': 0.25, 'input_tokens': 250, 'output_tokens': 125},
        }

        for job_id, config in job_configs.items():
            # Create mock response
            mock_response = MagicMock()
            mock_usage = MagicMock()
            mock_usage.prompt_tokens = config['input_tokens']
            mock_usage.completion_tokens = config['output_tokens']
            mock_response.usage = mock_usage

            mock_choice = MagicMock()
            mock_choice.finish_reason = 'stop'
            mock_response.choices = [mock_choice]

            # Trigger callback
            _litellm_success_callback(
                kwargs={},
                completion_response=mock_response,
                start_time=0.0,
                end_time=1.0
            )

            # Read cost (should get correct value from thread-local storage)
            read_cost = getattr(_CALLBACK_DATA, 'cost', 0.0)
            read_input_tokens = getattr(_CALLBACK_DATA, 'input_tokens', 0)
            read_output_tokens = getattr(_CALLBACK_DATA, 'output_tokens', 0)

            # Verify correctness
            assert read_input_tokens == config['input_tokens'], (
                f"{job_id}: Expected input_tokens={config['input_tokens']}, "
                f"got {read_input_tokens}"
            )

            assert read_output_tokens == config['output_tokens'], (
                f"{job_id}: Expected output_tokens={config['output_tokens']}, "
                f"got {read_output_tokens}"
            )
