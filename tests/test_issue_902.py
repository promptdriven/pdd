
import unittest
from unittest.mock import patch, MagicMock
from pathlib import Path
import time
import random
import sys
import os

# Ensure local pdd is in path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

# Import the functions to test
from pdd.agentic_common import run_agentic_task, _is_permanent_error
from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator
from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator
from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

class TestIssue902(unittest.TestCase):
    
    # --- agentic_common Jitter Test ---
    @patch("pdd.agentic_common.get_available_agents", return_value=["anthropic"])
    @patch("pdd.agentic_common._run_with_provider")
    @patch("pdd.agentic_common.time.sleep")
    @patch("pdd.agentic_common.random.uniform")
    def test_jitter_is_additive(self, mock_uniform, mock_sleep, mock_run_with_provider, _mock_agents):
        """Requirement: Backoff jitter should be additive to the exponential base."""
        mock_run_with_provider.return_value = (False, "Error: transient", 0.0)
        mock_uniform.return_value = 2.5

        run_agentic_task(
            instruction="test",
            cwd=Path("."),
            max_retries=2,
            retry_delay=10.0,
            quiet=True
        )

        self.assertTrue(mock_sleep.called)
        first_sleep = mock_sleep.call_args_list[0][0][0]
        self.assertAlmostEqual(first_sleep, 12.5)

    # --- agentic_common False Positive Test ---
    @patch("pdd.agentic_common.get_available_agents", return_value=["anthropic"])
    @patch("pdd.agentic_common._run_with_provider")
    def test_false_positive_error_with_cost(self, mock_run_with_provider, _mock_agents):
        """Requirement: Error-like content with cost > 0 is a false positive and should be retried/fail.
        Currently buggy code has a < 500 char limit which misses long error messages.
        """
        long_error = "Error: " + "A" * 600
        mock_run_with_provider.return_value = (True, long_error, 0.05)
        
        success, output, cost, provider = run_agentic_task(
            instruction="test",
            cwd=Path("."),
            max_retries=1,
            quiet=True
        )
        
        # This will FAIL on current code because success will be True (thinks 600 chars is valid content)
        self.assertFalse(success, "Should detect long Error message as false positive")

    # --- agentic_common Aggregate Timeout Test ---
    @patch("pdd.agentic_common.get_available_agents", return_value=["anthropic", "google"])
    @patch("pdd.agentic_common._run_with_provider")
    @patch("pdd.agentic_common.time.time")
    def test_aggregate_timeout_skips_providers(self, mock_time, mock_run_with_provider, _mock_agents):
        """Requirement: Step should skip subsequent providers if aggregate deadline (2x step timeout) is reached."""
        T = 1000.0
        times = [
            T,      # task_start_time
            T,      # aggregate deadline check (start)
            T,      # now for budget check
            T + 250, # after 1st provider fails (jump > 2*timeout)
            T + 250, # log interaction
            T + 250, # next provider aggregate deadline check
        ]
        mock_time.side_effect = times

        with patch("pdd.agentic_common._DEFAULT_PROVIDER_PREFERENCE", ["anthropic", "google"]):
            mock_run_with_provider.return_value = (False, "Fail", 0.0)
            
            success, output, cost, provider = run_agentic_task(
                instruction="test",
                cwd=Path("."),
                timeout=100.0,
                max_retries=1,
                quiet=True
            )
            
            self.assertFalse(success)
            # Should only call _run_with_provider once because 2nd provider (google) is skipped
            self.assertEqual(mock_run_with_provider.call_count, 1)

    # --- agentic_common Permanent Error Classification ---
    def test_permanent_errors(self):
        """Requirement: Classification of permanent errors (auth, invalid parameter, model not found)."""
        self.assertTrue(_is_permanent_error("Authentication error: invalid key"))
        self.assertTrue(_is_permanent_error("Invalid parameter: model_name"))
        self.assertTrue(_is_permanent_error("Model not found: gpt-5"))
        self.assertTrue(_is_permanent_error("Permission denied: access denied"))
        
        # Transient errors should be False (should retry)
        self.assertFalse(_is_permanent_error("Rate limit exceeded"))
        self.assertFalse(_is_permanent_error("Timeout expired"))
        self.assertFalse(_is_permanent_error("500 Internal Server Error"))

if __name__ == "__main__":
    unittest.main()
