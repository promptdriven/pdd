"""Tests for issue #509: Cost under-reporting when retry calls overwrite _llm_mod._LAST_CALLBACK_DATA.

When llm_invoke() retries due to None content, malformed JSON, or invalid Python syntax,
the success callback overwrites _llm_mod._LAST_CALLBACK_DATA["cost"] with only the retry's cost,
silently losing the original call's cost.
"""

import pytest
import os
import pandas as pd
from unittest.mock import patch, MagicMock
import pdd.llm_invoke as _llm_mod


def _make_mock_model():
    return {
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


def _make_completion_side_effect(responses_and_costs):
    """Create a side_effect function that sets _llm_mod._LAST_CALLBACK_DATA on each call.

    responses_and_costs: list of (response, cost) tuples
    """
    call_count = [0]

    def side_effect(**kwargs):
        idx = call_count[0]
        call_count[0] += 1
        resp, cost = responses_and_costs[idx]
        # Simulate the callback overwriting _llm_mod._LAST_CALLBACK_DATA
        _llm_mod._LAST_CALLBACK_DATA["cost"] = cost
        _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = resp.usage.prompt_tokens
        _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = resp.usage.completion_tokens
        return resp

    return side_effect


@pytest.fixture(autouse=True)
def reset_callback_data():
    """Reset _llm_mod._LAST_CALLBACK_DATA before each test."""
    _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.0
    _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = 0
    _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = 0
    _llm_mod._LAST_CALLBACK_DATA["finish_reason"] = None
    yield


class TestRetryCostAccumulation:
    """Tests that retry costs are accumulated, not overwritten."""

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "OPENAI_API_KEY": "test-key"})
    @patch("pdd.llm_invoke._ensure_api_key", return_value=True)
    @patch("pdd.llm_invoke._select_model_candidates")
    @patch("pdd.llm_invoke._load_model_data")
    @patch("pdd.llm_invoke.litellm")
    def test_none_content_retry_accumulates_cost(
        self, mock_litellm, mock_load, mock_select, mock_ensure
    ):
        """When first call returns None content and retry succeeds,
        the reported cost should include BOTH calls' costs."""
        model = _make_mock_model()
        mock_load.return_value = pd.DataFrame([model])
        mock_select.return_value = [model]
        mock_litellm.cache = MagicMock()  # Non-None so retry path triggers
        mock_litellm.drop_params = True

        first_call_cost = 0.05
        retry_call_cost = 0.03
        expected_total = first_call_cost + retry_call_cost

        first_resp = _make_response(content=None)  # Triggers None-content retry
        retry_resp = _make_response(content="Hello world")

        mock_litellm.completion = _make_completion_side_effect([
            (first_resp, first_call_cost),
            (retry_resp, retry_call_cost),
        ])

        from pdd.llm_invoke import llm_invoke
        result = llm_invoke(
            prompt="Test {input}",
            input_json={"input": "hello"},
            strength=0.5,
            temperature=0.0,
            use_cloud=False,
        )

        reported_cost = result["cost"]
        assert reported_cost == pytest.approx(expected_total), (
            f"Cost should be {expected_total} (first {first_call_cost} + retry {retry_call_cost}), "
            f"but got {reported_cost}. Retry cost overwrote instead of accumulating."
        )

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "OPENAI_API_KEY": "test-key"})
    @patch("pdd.llm_invoke._ensure_api_key", return_value=True)
    @patch("pdd.llm_invoke._select_model_candidates")
    @patch("pdd.llm_invoke._load_model_data")
    @patch("pdd.llm_invoke.litellm")
    def test_malformed_json_retry_accumulates_cost(
        self, mock_litellm, mock_load, mock_select, mock_ensure
    ):
        """When first call returns malformed JSON and retry succeeds,
        the reported cost should include BOTH calls' costs."""
        model = _make_mock_model()
        mock_load.return_value = pd.DataFrame([model])
        mock_select.return_value = [model]
        mock_litellm.cache = MagicMock()
        mock_litellm.drop_params = True

        first_call_cost = 0.04
        retry_call_cost = 0.04
        expected_total = first_call_cost + retry_call_cost

        # Malformed JSON: excessive trailing newlines
        malformed = '{"key": "value' + '\n' * 500
        first_resp = _make_response(content=malformed)
        retry_resp = _make_response(content='{"key": "value"}')

        mock_litellm.completion = _make_completion_side_effect([
            (first_resp, first_call_cost),
            (retry_resp, retry_call_cost),
        ])

        from pdd.llm_invoke import llm_invoke
        result = llm_invoke(
            prompt="Test {input}",
            input_json={"input": "hello"},
            strength=0.5,
            temperature=0.0,
            use_cloud=False,
        )

        reported_cost = result["cost"]
        assert reported_cost == pytest.approx(expected_total), (
            f"Cost should be {expected_total} (first {first_call_cost} + retry {retry_call_cost}), "
            f"but got {reported_cost}. Retry cost overwrote instead of accumulating."
        )

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "OPENAI_API_KEY": "test-key"})
    @patch("pdd.llm_invoke._ensure_api_key", return_value=True)
    @patch("pdd.llm_invoke._select_model_candidates")
    @patch("pdd.llm_invoke._load_model_data")
    @patch("pdd.llm_invoke.litellm")
    def test_no_retry_cost_unchanged(
        self, mock_litellm, mock_load, mock_select, mock_ensure
    ):
        """When no retry occurs, cost should be reported normally (regression guard)."""
        model = _make_mock_model()
        mock_load.return_value = pd.DataFrame([model])
        mock_select.return_value = [model]
        mock_litellm.cache = None
        mock_litellm.drop_params = True

        single_cost = 0.05
        resp = _make_response(content="Hello world")

        mock_litellm.completion = _make_completion_side_effect([
            (resp, single_cost),
        ])

        from pdd.llm_invoke import llm_invoke
        result = llm_invoke(
            prompt="Test {input}",
            input_json={"input": "hello"},
            strength=0.5,
            temperature=0.0,
            use_cloud=False,
        )

        assert result["cost"] == pytest.approx(single_cost)

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "OPENAI_API_KEY": "test-key"})
    @patch("pdd.llm_invoke._ensure_api_key", return_value=True)
    @patch("pdd.llm_invoke._select_model_candidates")
    @patch("pdd.llm_invoke._load_model_data")
    @patch("pdd.llm_invoke.litellm")
    def test_none_content_retry_accumulates_tokens(
        self, mock_litellm, mock_load, mock_select, mock_ensure
    ):
        """Token counts should also accumulate across retries."""
        model = _make_mock_model()
        mock_load.return_value = pd.DataFrame([model])
        mock_select.return_value = [model]
        mock_litellm.cache = MagicMock()
        mock_litellm.drop_params = True

        first_resp = _make_response(content=None, prompt_tokens=1000, completion_tokens=500)
        retry_resp = _make_response(content="Hello", prompt_tokens=1000, completion_tokens=500)

        mock_litellm.completion = _make_completion_side_effect([
            (first_resp, 0.05),
            (retry_resp, 0.03),
        ])

        from pdd.llm_invoke import llm_invoke
        result = llm_invoke(
            prompt="Test {input}",
            input_json={"input": "hello"},
            strength=0.5,
            temperature=0.0,
            use_cloud=False,
        )

        # After fix, tokens should be accumulated (2000 input, 1000 output)
        # Currently they get overwritten to just the retry's tokens
        reported_cost = result["cost"]
        assert reported_cost == pytest.approx(0.08), (
            f"Expected accumulated cost of 0.08, got {reported_cost}"
        )

        # Verify that input/output token counts are also accumulated across retries.
        assert _llm_mod._LAST_CALLBACK_DATA["input_tokens"] == 2000, (
            f"Expected accumulated input tokens of 2000, "
            f"got {_llm_mod._LAST_CALLBACK_DATA['input_tokens']}"
        )
        assert _llm_mod._LAST_CALLBACK_DATA["output_tokens"] == 1000, (
            f"Expected accumulated output tokens of 1000, "
            f"got {_llm_mod._LAST_CALLBACK_DATA['output_tokens']}"
        )
