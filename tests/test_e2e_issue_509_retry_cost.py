"""
E2E Test for Issue #509: Cost under-reporting when retry calls overwrite _llm_mod._LAST_CALLBACK_DATA.

This test exercises the generate command path by invoking llm_invoke directly, simulating
a scenario where llm_invoke retries due to None content. The test verifies that the cost
accumulated in _llm_mod._LAST_CALLBACK_DATA includes BOTH the original and retry call
costs, not just the retry cost.

The bug: _llm_mod._LAST_CALLBACK_DATA["cost"] gets overwritten (not accumulated) on retry,
so the cost from the first LLM call is silently lost.
"""

import os
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

import pdd.llm_invoke as _llm_mod


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH so language detection can find language_format.csv."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


@pytest.fixture(autouse=True)
def reset_callback_data():
    """Reset _llm_mod._LAST_CALLBACK_DATA before each test."""
    _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.0
    _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = 0
    _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = 0
    _llm_mod._LAST_CALLBACK_DATA["finish_reason"] = None
    yield


def _make_response(content, prompt_tokens=100, completion_tokens=50):
    resp = MagicMock()
    choice = MagicMock()
    choice.message.content = content
    choice.finish_reason = "stop"
    resp.choices = [choice]
    usage = MagicMock()
    usage.prompt_tokens = prompt_tokens
    usage.completion_tokens = completion_tokens
    resp.usage = usage
    return resp


class TestE2ERetryCostAccumulation:
    """E2E test: llm_invoke cost accumulation through the generate command path."""

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "OPENAI_API_KEY": "test-key"})
    def test_generate_command_reports_accumulated_retry_cost(self, tmp_path, monkeypatch):
        """
        Exercise the full generate -> llm_invoke -> retry path and verify
        that the cost returned includes both the original and retry call costs.

        This simulates a user running `pdd generate` where the first LLM call
        returns None content, triggering a cache-bypass retry. The total cost
        should be $0.05 + $0.03 = $0.08, but the bug causes it to report $0.03.
        """
        monkeypatch.chdir(tmp_path)

        # Create a prompt file
        prompt_file = tmp_path / "hello_python.prompt"
        prompt_file.write_text("Write a Python function that prints hello world.\n{input}")

        # Set up mock model data
        mock_model = {
            "provider": "Anthropic",
            "model": "claude-test-model",
            "input": 3.0,
            "output": 15.0,
            "coding_arena_elo": 1500,
            "structured_output": False,
            "base_url": "",
            "api_key": "OPENAI_API_KEY",
            "max_tokens": "",
            "max_completion_tokens": "",
            "reasoning_type": "none",
            "max_reasoning_tokens": 0,
        }

        import pandas as pd

        first_call_cost = 0.05
        retry_call_cost = 0.03
        expected_total = first_call_cost + retry_call_cost  # $0.08

        first_resp = _make_response(content=None)  # Triggers retry
        retry_resp = _make_response(content='def hello():\n    print("Hello world")\n')

        call_count = [0]

        def mock_completion(**kwargs):
            call_count[0] += 1
            if call_count[0] == 1:
                _llm_mod._LAST_CALLBACK_DATA["cost"] = first_call_cost
                _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = 100
                _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = 50
                return first_resp
            else:
                _llm_mod._LAST_CALLBACK_DATA["cost"] = retry_call_cost
                _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = 100
                _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = 50
                return retry_resp

        # Patch at the llm_invoke level to control LLM behavior
        with patch("pdd.llm_invoke._load_model_data") as mock_load, \
             patch("pdd.llm_invoke._select_model_candidates") as mock_select, \
             patch("pdd.llm_invoke._ensure_api_key", return_value=True), \
             patch("pdd.llm_invoke.litellm") as mock_litellm:

            mock_load.return_value = pd.DataFrame([mock_model])
            mock_select.return_value = [mock_model]
            mock_litellm.completion = mock_completion
            mock_litellm.cache = MagicMock()  # Non-None triggers cache-bypass retry path
            mock_litellm.drop_params = True

            # Call llm_invoke directly as the generate command would
            from pdd.llm_invoke import llm_invoke
            result = llm_invoke(
                prompt="Write a Python function that prints hello world.\n{input}",
                input_json={"input": ""},
                strength=0.5,
                temperature=0.0,
                use_cloud=False,
            )

        # Verify 2 LLM calls were made (original + retry)
        assert call_count[0] == 2, (
            f"Expected 2 LLM calls (original + retry), got {call_count[0]}"
        )

        # THE BUG CHECK: cost should be accumulated ($0.05 + $0.03 = $0.08)
        reported_cost = result["cost"]
        assert reported_cost == pytest.approx(expected_total), (
            f"ISSUE #509 BUG DETECTED: Retry cost overwrites instead of accumulating!\n\n"
            f"  First call cost:  ${first_call_cost:.2f}\n"
            f"  Retry call cost:  ${retry_call_cost:.2f}\n"
            f"  Expected total:   ${expected_total:.2f}\n"
            f"  Reported total:   ${reported_cost:.2f}\n"
            f"  Lost cost:        ${expected_total - reported_cost:.2f}\n\n"
            f"The --output-cost CSV would under-report by ${expected_total - reported_cost:.2f} per retry."
        )

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "OPENAI_API_KEY": "test-key"})
    def test_budget_enforcement_sees_full_retry_cost(self, tmp_path, monkeypatch):
        """
        E2E test: When budget is tight, under-reported retry costs could allow overspend.

        Simulates a scenario where a user sets --budget and multiple retries occur.
        The budget check should see the accumulated cost, not just the last retry's cost.
        """
        monkeypatch.chdir(tmp_path)

        mock_model = {
            "provider": "Anthropic",
            "model": "claude-test-model",
            "input": 3.0,
            "output": 15.0,
            "coding_arena_elo": 1500,
            "structured_output": False,
            "base_url": "",
            "api_key": "OPENAI_API_KEY",
            "max_tokens": "",
            "max_completion_tokens": "",
            "reasoning_type": "none",
            "max_reasoning_tokens": 0,
        }

        import pandas as pd

        # One retry (two calls total): costs should accumulate to $0.10
        costs = [0.05, 0.05]

        # First call returns None, second succeeds
        responses = [
            _make_response(content=None),
            _make_response(content='print("hello")'),
        ]

        call_count = [0]

        def mock_completion(**kwargs):
            idx = call_count[0]
            call_count[0] += 1
            # Only first call can trigger cache-bypass retry; subsequent are direct
            if idx < len(costs):
                _llm_mod._LAST_CALLBACK_DATA["cost"] = costs[idx]
                _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = 100
                _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = 50
                return responses[idx]
            # Fallback
            _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.05
            _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = 100
            _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = 50
            return responses[-1]

        with patch("pdd.llm_invoke._load_model_data") as mock_load, \
             patch("pdd.llm_invoke._select_model_candidates") as mock_select, \
             patch("pdd.llm_invoke._ensure_api_key", return_value=True), \
             patch("pdd.llm_invoke.litellm") as mock_litellm:

            mock_load.return_value = pd.DataFrame([mock_model])
            mock_select.return_value = [mock_model]
            mock_litellm.completion = mock_completion
            mock_litellm.cache = MagicMock()
            mock_litellm.drop_params = True

            from pdd.llm_invoke import llm_invoke
            result = llm_invoke(
                prompt="Test {input}",
                input_json={"input": "hello"},
                strength=0.5,
                temperature=0.0,
                use_cloud=False,
            )

        reported_cost = result["cost"]

        # The None-content retry path does one retry, so 2 calls made.
        # Expected accumulated cost: $0.05 + $0.05 = $0.10
        # Bug reports only the retry cost: $0.05
        assert reported_cost == pytest.approx(costs[0] + costs[1]), (
            f"ISSUE #509 BUG: Budget enforcement sees only ${reported_cost:.2f}, "
            f"but actual spend was ${costs[0] + costs[1]:.2f} (2 calls). "
            f"This allows overspend when --budget is set."
        )
