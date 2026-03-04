"""
E2E Test for Issue #686: Anthropic cost calculation double-counts cache_creation tokens.

This test exercises the full provider JSON parsing path that `run_agentic_task` uses:
  _parse_provider_json("anthropic", data) -> _calculate_anthropic_cost(data)

The bug: `_calculate_anthropic_cost()` computes `new_input = input_tokens - cache_read`
but does NOT subtract `cache_creation`. Since Anthropic's `input_tokens` includes both
`cache_read` and `cache_creation`, the cache_creation tokens end up charged at the regular
input rate (1.0x) AND again at the cache write rate (1.25x), totaling 2.25x instead of 1.25x.

These E2E tests use realistic Claude CLI JSON output payloads (matching what `run_agentic_task`
parses from subprocess stdout) to verify the cost flows correctly through the full parsing path.
"""

import pytest


class TestE2EAnthropicCostParsing:
    """E2E: Parse realistic Claude CLI JSON output and verify cost accuracy."""

    def _parse_anthropic_json(self, data):
        """Exercise the full provider JSON parsing path used by run_agentic_task."""
        from pdd.agentic_common import _parse_provider_json
        success, text, cost = _parse_provider_json("anthropic", data)
        return success, text, cost

    def test_e2e_claude_output_with_prompt_caching(self):
        """
        E2E: Realistic Claude CLI JSON with prompt caching.

        Simulates what run_agentic_task receives from `claude -p - --output-format json`
        when total_cost_usd is 0 (subscription auth) and prompt caching is active.

        Sonnet pricing: $3/M input, $15/M output, cache read 0.1x, cache write 1.25x

        Token breakdown (1000 input total):
          - 500 cache_read  -> 500 * $3/M * 0.1  = $0.00015
          - 300 cache_creation -> 300 * $3/M * 1.25 = $0.001125
          - 200 new input   -> 200 * $3/M * 1.0   = $0.0006
          - 200 output      -> 200 * $15/M         = $0.003

        Correct total: $0.004875
        Buggy total:   $0.005775 (cache_creation charged at 1.0x + 1.25x = 2.25x)
        """
        # Realistic Claude CLI JSON output payload
        claude_json = {
            "result": "I've analyzed the bug and here are my findings...",
            "total_cost_usd": 0,  # Zero when using subscription auth
            "usage": {
                "input_tokens": 1000,
                "output_tokens": 200,
                "cache_read_input_tokens": 500,
                "cache_creation_input_tokens": 300,
            },
            "modelUsage": {
                "claude-sonnet-4-20250514": {
                    # No costUSD — forces token-based estimation
                    "inputTokens": 1000,
                    "outputTokens": 200,
                    "cacheReadInputTokens": 500,
                    "cacheCreationInputTokens": 300,
                }
            },
        }

        success, text, cost = self._parse_anthropic_json(claude_json)

        assert success is True
        assert text == "I've analyzed the bug and here are my findings..."

        # Correct cost: $0.004875
        # Buggy cost:   $0.005775  (overcharge = 300/1M * $3.00 = $0.0009)
        expected_correct_cost = 0.004875

        assert cost == pytest.approx(expected_correct_cost, abs=1e-7), (
            f"ISSUE #686 BUG: cache_creation tokens double-counted!\n\n"
            f"  Expected cost: ${expected_correct_cost:.6f}\n"
            f"  Actual cost:   ${cost:.6f}\n"
            f"  Overcharge:    ${cost - expected_correct_cost:.6f}\n\n"
            f"  cache_creation (300) tokens are charged at regular input rate (1.0x)\n"
            f"  AND at cache write rate (1.25x), totaling 2.25x instead of 1.25x."
        )

    def test_e2e_agentic_task_cost_with_heavy_caching(self):
        """
        E2E: Heavy prompt caching scenario (typical for multi-step agentic workflows).

        In `pdd bug` / `pdd fix` workflows, most of the prompt is cached after the
        first turn. This means cache_creation is large on turn 1, and subsequent turns
        have large cache_read. The cost inflation compounds across all cached turns.

        Token breakdown (50,000 input total — typical for agentic task):
          - 40,000 cache_read       -> charged at 0.1x input
          - 8,000  cache_creation   -> charged at 1.25x input
          - 2,000  new input        -> charged at 1.0x input
          - 5,000  output           -> charged at output rate

        Sonnet pricing: $3/M input, $15/M output
        """
        claude_json = {
            "result": "Task completed successfully.",
            "total_cost_usd": 0,
            "usage": {
                "input_tokens": 50000,
                "output_tokens": 5000,
                "cache_read_input_tokens": 40000,
                "cache_creation_input_tokens": 8000,
            },
            "modelUsage": {
                "claude-sonnet-4-20250514": {
                    "inputTokens": 50000,
                    "outputTokens": 5000,
                }
            },
        }

        success, text, cost = self._parse_anthropic_json(claude_json)

        assert success is True

        # Correct calculation:
        #   new_input = 50000 - 40000 - 8000 = 2000
        #   input_cost = 2000/1M * $3 = $0.006
        #   cache_read_cost = 40000/1M * $3 * 0.1 = $0.012
        #   cache_write_cost = 8000/1M * $3 * 1.25 = $0.030
        #   output_cost = 5000/1M * $15 = $0.075
        #   total = $0.123
        #
        # Buggy calculation (cache_creation not subtracted from new_input):
        #   new_input = 50000 - 40000 = 10000 (includes 8000 cache_creation)
        #   input_cost = 10000/1M * $3 = $0.030  (should be $0.006)
        #   overcharge = 8000/1M * $3 = $0.024
        #   buggy total = $0.147

        expected_correct_cost = 0.123
        buggy_cost = 0.147

        assert cost == pytest.approx(expected_correct_cost, abs=1e-7), (
            f"ISSUE #686 BUG: Heavy caching amplifies the double-counting!\n\n"
            f"  Expected cost: ${expected_correct_cost:.6f}\n"
            f"  Actual cost:   ${cost:.6f}\n"
            f"  Overcharge:    ${cost - expected_correct_cost:.6f}\n\n"
            f"  With 8,000 cache_creation tokens, the overcharge is\n"
            f"  8000/1M * $3.00 = $0.024 per agentic call.\n"
            f"  Over a 10-step workflow, this inflates costs by ~$0.24."
        )

    def test_e2e_total_cost_usd_bypasses_token_math(self):
        """
        E2E: When total_cost_usd is present and non-zero, token math is skipped entirely.

        This verifies the bug does NOT affect users who have total_cost_usd populated
        (API key auth). The token-based fallback is only hit with subscription auth.
        """
        claude_json = {
            "result": "Done.",
            "total_cost_usd": 0.004875,  # Correct cost provided by Claude
            "usage": {
                "input_tokens": 1000,
                "output_tokens": 200,
                "cache_read_input_tokens": 500,
                "cache_creation_input_tokens": 300,
            },
            "modelUsage": {},
        }

        success, text, cost = self._parse_anthropic_json(claude_json)

        assert success is True
        assert cost == pytest.approx(0.004875), (
            f"When total_cost_usd is present, it should be used directly.\n"
            f"  Expected: $0.004875\n"
            f"  Got:      ${cost:.6f}"
        )

    def test_e2e_budget_enforcement_with_cached_agentic_steps(self):
        """
        E2E: Budget enforcement sees inflated costs due to double-counting.

        In a multi-step agentic workflow with a $1.00 budget, the inflated cost
        reporting could cause premature budget exhaustion warnings or, conversely,
        credit over-deductions in cloud mode.
        """
        budget = 1.00
        accumulated_cost = 0.0

        # Simulate 5 agentic steps, each with caching
        for step in range(5):
            step_json = {
                "result": f"Step {step} done.",
                "total_cost_usd": 0,
                "usage": {
                    "input_tokens": 50000,
                    "output_tokens": 5000,
                    "cache_read_input_tokens": 40000,
                    "cache_creation_input_tokens": 8000,
                },
                "modelUsage": {
                    "claude-sonnet-4-20250514": {
                        "inputTokens": 50000,
                        "outputTokens": 5000,
                    }
                },
            }

            _, _, step_cost = self._parse_anthropic_json(step_json)
            accumulated_cost += step_cost

        # Correct cost per step: $0.123 -> 5 steps = $0.615
        # Buggy cost per step:   $0.147 -> 5 steps = $0.735
        expected_total = 0.123 * 5  # $0.615

        assert accumulated_cost == pytest.approx(expected_total, abs=1e-6), (
            f"ISSUE #686 BUG: Accumulated cost over 5 agentic steps is inflated!\n\n"
            f"  Expected total: ${expected_total:.4f}\n"
            f"  Actual total:   ${accumulated_cost:.4f}\n"
            f"  Overcharge:     ${accumulated_cost - expected_total:.4f}\n\n"
            f"  In cloud mode, this means users are over-charged by\n"
            f"  ${accumulated_cost - expected_total:.4f} in PDD credits per workflow."
        )
