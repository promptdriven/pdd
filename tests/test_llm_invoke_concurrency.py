"""Tests for llm_invoke concurrent execution and callback thread-safety.

These tests verify that:
1. Concurrent LiteLLM callbacks work correctly with thread-local storage (verifies fix for bug #375)
2. Sequential calls still work (regression prevention)

This addresses issue #375: Race Condition in LLM Cost Tracking.
"""
import pytest
import time
import threading
from concurrent.futures import ThreadPoolExecutor
from unittest.mock import MagicMock

from pdd.llm_invoke import _litellm_success_callback, _CALLBACK_DATA


class TestConcurrentLLMCallbacks:
    """Tests for concurrent LiteLLM callback execution and thread-safety."""

    def test_concurrent_callbacks_corrupt_cost_data(self):
        """
        Test #1 from Step 6: Verify that concurrent _litellm_success_callback calls
        use thread-local storage to isolate callback data per thread.

        Before fix: This test FAILS - threads read each other's token counts (race condition).
        After fix: This test PASSES - each thread gets its own token counts (thread-local storage).

        This is the primary bug reproduction test from issue #375.

        Note: We verify token counts (not cost) because litellm.completion_cost() returns 0.0
        for mock responses. Token counts are the reliable indicator of thread-safety.
        """
        # Track results with thread-safe data structure
        results_lock = threading.Lock()
        thread_results = {}

        # Expected costs and token patterns for each thread
        test_cases = {
            'thread_0': {'cost': 0.10, 'input_tokens': 100, 'output_tokens': 50, 'finish_reason': 'stop'},
            'thread_1': {'cost': 0.30, 'input_tokens': 200, 'output_tokens': 100, 'finish_reason': 'stop'},
            'thread_2': {'cost': 0.05, 'input_tokens': 300, 'output_tokens': 150, 'finish_reason': 'stop'},
        }

        def simulate_llm_callback(thread_id):
            """Simulate an LLM call with callback that writes to/reads from thread-local _CALLBACK_DATA."""
            test_case = test_cases[thread_id]

            # Create mock completion response
            mock_response = MagicMock()
            mock_usage = MagicMock()
            mock_usage.prompt_tokens = test_case['input_tokens']
            mock_usage.completion_tokens = test_case['output_tokens']
            mock_response.usage = mock_usage

            mock_choice = MagicMock()
            mock_choice.finish_reason = test_case['finish_reason']
            mock_response.choices = [mock_choice]

            # Mock kwargs for callback
            mock_kwargs = {}

            # Stagger timing to ensure callbacks interleave (critical for race condition)
            if thread_id == 'thread_1':
                time.sleep(0.01)
            elif thread_id == 'thread_2':
                time.sleep(0.02)

            # Step 1: Callback writes to global _CALLBACK_DATA
            # This simulates LiteLLM calling our success callback
            _litellm_success_callback(
                kwargs=mock_kwargs,
                completion_response=mock_response,
                start_time=0.0,
                end_time=1.0
            )

            # Small delay to let other threads write (simulates async callback timing)
            time.sleep(0.03)

            # Step 2: Read from thread-local _CALLBACK_DATA
            # This simulates llm_invoke reading the callback data (pdd/llm_invoke.py:2751)
            with results_lock:
                thread_results[thread_id] = {
                    'read_cost': getattr(_CALLBACK_DATA, 'cost', 0.0),
                    'read_input_tokens': getattr(_CALLBACK_DATA, 'input_tokens', 0),
                    'read_output_tokens': getattr(_CALLBACK_DATA, 'output_tokens', 0),
                    'read_finish_reason': getattr(_CALLBACK_DATA, 'finish_reason', None),
                    'expected_cost': test_case['cost'],
                    'expected_input_tokens': test_case['input_tokens'],
                    'expected_output_tokens': test_case['output_tokens'],
                    'expected_finish_reason': test_case['finish_reason'],
                }

        # Run 3 threads concurrently (matching server's max_concurrent=3)
        with ThreadPoolExecutor(max_workers=3) as executor:
            futures = [
                executor.submit(simulate_llm_callback, 'thread_0'),
                executor.submit(simulate_llm_callback, 'thread_1'),
                executor.submit(simulate_llm_callback, 'thread_2'),
            ]

            # Wait for all threads to complete
            for future in futures:
                future.result()

        # Verify results: Each thread should read its own data, not another thread's data
        # Before fix: This assertion FAILS due to race condition (shared global state)
        # After fix: This assertion should PASS (thread-local storage)

        failures = []
        for thread_id, data in thread_results.items():
            # Note: We skip cost verification because litellm.completion_cost() returns 0.0 for mocks
            # The token counts are the real indicator of whether thread-local storage is working

            # Check token counts (this is the critical verification)
            if data['read_input_tokens'] != data['expected_input_tokens']:
                failures.append(
                    f"{thread_id} read wrong input_tokens: "
                    f"Expected {data['expected_input_tokens']}, Got {data['read_input_tokens']}"
                )

            if data['read_output_tokens'] != data['expected_output_tokens']:
                failures.append(
                    f"{thread_id} read wrong output_tokens: "
                    f"Expected {data['expected_output_tokens']}, Got {data['read_output_tokens']}"
                )

            # Check finish reason
            if data['read_finish_reason'] != data['expected_finish_reason']:
                failures.append(
                    f"{thread_id} read wrong finish_reason: "
                    f"Expected {data['expected_finish_reason']}, Got {data['read_finish_reason']}"
                )

        # If there are failures, thread-local storage is not working correctly
        if failures:
            failure_msg = (
                "Thread-local storage not working correctly! "
                "Threads are reading each other's callback data.\n\n"
                "Failures:\n" + "\n".join(f"  - {f}" for f in failures) +
                f"\n\nAll results:\n{thread_results}\n\n"
                "This indicates that the fix for issue #375 is not working properly. "
                "Each thread should read its own callback data from thread-local storage."
            )
            pytest.fail(failure_msg)

    def test_sequential_callbacks_work(self):
        """
        Test #4 from Step 6: Verify sequential callback calls still work (regression prevention).

        This ensures the fix doesn't break the existing single-threaded use case.
        """
        # Test cases for sequential execution
        test_cases = [
            {'cost': 0.10, 'input_tokens': 100, 'output_tokens': 50, 'finish_reason': 'stop'},
            {'cost': 0.20, 'input_tokens': 200, 'output_tokens': 100, 'finish_reason': 'stop'},
            {'cost': 0.15, 'input_tokens': 150, 'output_tokens': 75, 'finish_reason': 'length'},
        ]

        results = []

        for i, test_case in enumerate(test_cases):
            # Create mock response
            mock_response = MagicMock()
            mock_usage = MagicMock()
            mock_usage.prompt_tokens = test_case['input_tokens']
            mock_usage.completion_tokens = test_case['output_tokens']
            mock_response.usage = mock_usage

            mock_choice = MagicMock()
            mock_choice.finish_reason = test_case['finish_reason']
            mock_response.choices = [mock_choice]

            mock_kwargs = {}

            # Call callback (writes to thread-local _CALLBACK_DATA)
            _litellm_success_callback(
                kwargs=mock_kwargs,
                completion_response=mock_response,
                start_time=0.0,
                end_time=1.0
            )

            # Read from thread-local _CALLBACK_DATA (immediately after callback)
            result = {
                'cost': getattr(_CALLBACK_DATA, 'cost', 0.0),
                'input_tokens': getattr(_CALLBACK_DATA, 'input_tokens', 0),
                'output_tokens': getattr(_CALLBACK_DATA, 'output_tokens', 0),
                'finish_reason': getattr(_CALLBACK_DATA, 'finish_reason', None),
            }
            results.append(result)

        # Verify all sequential calls got correct data
        for i, (test_case, result) in enumerate(zip(test_cases, results)):
            # Note: We can't verify cost exactly since litellm.completion_cost may return 0.0
            # But we can verify token counts and finish reason
            assert result['input_tokens'] == test_case['input_tokens'], (
                f"Sequential call {i} got wrong input_tokens: "
                f"Expected {test_case['input_tokens']}, Got {result['input_tokens']}"
            )
            assert result['output_tokens'] == test_case['output_tokens'], (
                f"Sequential call {i} got wrong output_tokens: "
                f"Expected {test_case['output_tokens']}, Got {result['output_tokens']}"
            )
            assert result['finish_reason'] == test_case['finish_reason'], (
                f"Sequential call {i} got wrong finish_reason: "
                f"Expected {test_case['finish_reason']}, Got {result['finish_reason']}"
            )
