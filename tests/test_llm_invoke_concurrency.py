"""Tests for llm_invoke concurrent execution and callback thread-safety.

These tests verify that:
1. Concurrent LiteLLM callbacks corrupt cost data in _LAST_CALLBACK_DATA (reproduces bug #375)
2. Sequential calls still work (regression prevention)

This addresses issue #375: Race Condition in LLM Cost Tracking.
"""
import pytest
import time
import threading
from concurrent.futures import ThreadPoolExecutor
from unittest.mock import MagicMock

from pdd.llm_invoke import _litellm_success_callback, _LAST_CALLBACK_DATA


class TestConcurrentLLMCallbacks:
    """Tests for concurrent LiteLLM callback execution and thread-safety."""

    def test_concurrent_callbacks_corrupt_cost_data(self):
        """
        Test #1 from Step 6: Verify that concurrent _litellm_success_callback calls
        corrupt cost data due to shared global _LAST_CALLBACK_DATA.

        Before fix: This test FAILS - threads read each other's costs (race condition).
        After fix: This test should PASS - each thread gets its own cost (thread-local storage).

        This is the primary bug reproduction test from issue #375.
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
            """Simulate an LLM call with callback that writes to/reads from _LAST_CALLBACK_DATA."""
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

            # Step 1: Callback writes to global _LAST_CALLBACK_DATA
            # This simulates LiteLLM calling our success callback
            _litellm_success_callback(
                kwargs=mock_kwargs,
                completion_response=mock_response,
                start_time=0.0,
                end_time=1.0
            )

            # Small delay to let other threads write (simulates async callback timing)
            time.sleep(0.03)

            # Step 2: Read from global _LAST_CALLBACK_DATA
            # This simulates llm_invoke reading the callback data (pdd/llm_invoke.py:2749)
            with results_lock:
                thread_results[thread_id] = {
                    'read_cost': _LAST_CALLBACK_DATA.get('cost', 0.0),
                    'read_input_tokens': _LAST_CALLBACK_DATA.get('input_tokens', 0),
                    'read_output_tokens': _LAST_CALLBACK_DATA.get('output_tokens', 0),
                    'read_finish_reason': _LAST_CALLBACK_DATA.get('finish_reason', None),
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
            # Check cost
            if data['read_cost'] != data['expected_cost']:
                failures.append(
                    f"{thread_id} read wrong cost: "
                    f"Expected ${data['expected_cost']:.2f}, Got ${data['read_cost']:.2f}"
                )

            # Check token counts
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

        # If there are failures, this is the race condition bug
        if failures:
            failure_msg = (
                "Race condition detected in _LAST_CALLBACK_DATA! "
                "Threads are reading each other's callback data.\n\n"
                "Failures:\n" + "\n".join(f"  - {f}" for f in failures) +
                f"\n\nAll results:\n{thread_results}\n\n"
                "This confirms issue #375: The global _LAST_CALLBACK_DATA dictionary "
                "is shared across concurrent jobs, causing cost/token data corruption."
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

            # Call callback (writes to _LAST_CALLBACK_DATA)
            _litellm_success_callback(
                kwargs=mock_kwargs,
                completion_response=mock_response,
                start_time=0.0,
                end_time=1.0
            )

            # Read from _LAST_CALLBACK_DATA (immediately after callback)
            result = {
                'cost': _LAST_CALLBACK_DATA.get('cost', 0.0),
                'input_tokens': _LAST_CALLBACK_DATA.get('input_tokens', 0),
                'output_tokens': _LAST_CALLBACK_DATA.get('output_tokens', 0),
                'finish_reason': _LAST_CALLBACK_DATA.get('finish_reason', None),
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
