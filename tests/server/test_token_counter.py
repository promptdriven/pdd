import csv
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from z3 import Solver, Int, Real, unsat

from pdd.server import token_counter
from pdd.server.token_counter import (
    count_tokens,
    get_context_limit,
    estimate_cost,
    get_token_metrics,
    CostEstimate,
    TokenMetrics,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_pricing_csv(tmp_path):
    """Creates a temporary CSV file with pricing data."""
    csv_content = [
        "model,input,output",
        "gpt-4,30.00,60.00",
        "claude-3-opus,15.00,75.00",
        "claude-sonnet-4-20250514,3.00,15.00",
        "gemini-1.5-pro,3.50,10.50",
    ]
    p = tmp_path / "llm_model.csv"
    p.write_text("\n".join(csv_content))
    return p


# ---------------------------------------------------------------------------
# count_tokens
# ---------------------------------------------------------------------------

def test_count_tokens_empty():
    """Empty or None text should return 0 without touching litellm."""
    assert count_tokens("") == 0
    assert count_tokens(None) == 0


def test_count_tokens_uses_litellm():
    """count_tokens delegates to litellm.token_counter for non-empty text."""
    with patch("pdd.server.token_counter.litellm.token_counter", return_value=7) as mock_tc:
        result = count_tokens("hello world", model="gpt-4o")
    assert result == 7
    mock_tc.assert_called_once_with(
        model="gpt-4o",
        messages=[{"role": "user", "content": "hello world"}],
    )


def test_count_tokens_default_model():
    """count_tokens uses gpt-4o as the default model."""
    with patch("pdd.server.token_counter.litellm.token_counter", return_value=3) as mock_tc:
        count_tokens("test")
    args, kwargs = mock_tc.call_args
    assert kwargs.get("model") == "gpt-4o" or (args and args[0] == "gpt-4o")


def test_count_tokens_falls_back_to_tiktoken_on_litellm_error():
    """When litellm raises, count_tokens falls back to tiktoken cl100k_base."""
    with patch("pdd.server.token_counter.litellm.token_counter", side_effect=Exception("unknown model")):
        result = count_tokens("hello world", model="totally-unknown-xyz")
    # tiktoken cl100k_base tokenises "hello world" to 2 tokens
    assert result == 2


# ---------------------------------------------------------------------------
# get_context_limit
# ---------------------------------------------------------------------------

def test_get_context_limit_known_model():
    """Returns max_input_tokens from litellm.get_model_info for known models."""
    with patch(
        "pdd.server.token_counter.litellm.get_model_info",
        return_value={"max_input_tokens": 128000, "max_tokens": 16384},
    ):
        assert get_context_limit("gpt-4o") == 128000


def test_get_context_limit_claude():
    """Returns correct input context for Claude models."""
    with patch(
        "pdd.server.token_counter.litellm.get_model_info",
        return_value={"max_input_tokens": 200000, "max_tokens": 64000},
    ):
        assert get_context_limit("claude-sonnet-4-6") == 200000


def test_get_context_limit_gemini():
    """Returns correct input context for Gemini models."""
    with patch(
        "pdd.server.token_counter.litellm.get_model_info",
        return_value={"max_input_tokens": 1048576, "max_tokens": 8192},
    ):
        assert get_context_limit("gemini/gemini-2.0-flash") == 1048576


def test_get_context_limit_bedrock_model():
    """Bedrock-prefixed models are resolved correctly via litellm."""
    with patch(
        "pdd.server.token_counter.litellm.get_model_info",
        return_value={"max_input_tokens": 1000000, "max_tokens": 128000},
    ):
        assert get_context_limit("bedrock/anthropic.claude-3-5-sonnet-20241022-v2:0") == 1000000


def test_get_context_limit_unknown_model_returns_none():
    """Unknown models cause litellm to raise — get_context_limit returns None."""
    with patch(
        "pdd.server.token_counter.litellm.get_model_info",
        side_effect=Exception("model not mapped"),
    ):
        assert get_context_limit("totally-unknown-model-xyz") is None


def test_get_context_limit_missing_key_returns_none():
    """If litellm returns info without max_input_tokens, return None."""
    with patch(
        "pdd.server.token_counter.litellm.get_model_info",
        return_value={"max_tokens": 4096},  # no max_input_tokens key
    ):
        assert get_context_limit("some-model") is None


# ---------------------------------------------------------------------------
# estimate_cost
# ---------------------------------------------------------------------------

def test_estimate_cost_no_csv_path():
    """Should return None if CSV path is not provided."""
    assert estimate_cost(1000, "gpt-4", None) is None


def test_estimate_cost_file_not_found():
    """Should return None if CSV file does not exist."""
    assert estimate_cost(1000, "gpt-4", Path("/non/existent/path.csv")) is None


def test_estimate_cost_exact_match(mock_pricing_csv):
    """Cost estimation with an exact model name match in CSV."""
    # gpt-4 is $30.00/M — 1000 tokens → $0.03
    token_counter._load_model_pricing.cache_clear()
    estimate = estimate_cost(1000, "gpt-4", mock_pricing_csv)
    assert estimate is not None
    assert estimate.input_cost == pytest.approx(0.03)
    assert estimate.model == "gpt-4"
    assert estimate.cost_per_million == 30.00


def test_estimate_cost_partial_match(mock_pricing_csv):
    """Cost estimation with a partial model name match."""
    token_counter._load_model_pricing.cache_clear()
    # "claude-3-opus-20240229" should match "claude-3-opus" ($15.00/M)
    estimate = estimate_cost(1_000_000, "claude-3-opus-20240229", mock_pricing_csv)
    assert estimate is not None
    assert estimate.input_cost == pytest.approx(15.00)
    assert estimate.cost_per_million == 15.00


def test_estimate_cost_fallback_defaults(mock_pricing_csv):
    """Falls back to known defaults when model not found in CSV."""
    token_counter._load_model_pricing.cache_clear()
    # "unknown-model" not in CSV → falls back to claude-sonnet-4-20250514 ($3.00/M)
    estimate = estimate_cost(1000, "unknown-super-model", mock_pricing_csv)
    assert estimate is not None
    assert estimate.model == "claude-sonnet-4-20250514"
    assert estimate.cost_per_million == 3.00


def test_estimate_cost_serialization(mock_pricing_csv):
    """CostEstimate.to_dict() serializes all fields correctly."""
    token_counter._load_model_pricing.cache_clear()
    estimate = estimate_cost(1000, "gpt-4", mock_pricing_csv)
    data = estimate.to_dict()
    assert data["input_cost"] == pytest.approx(0.03)
    assert data["currency"] == "USD"
    assert data["tokens"] == 1000
    assert "model" in data
    assert "cost_per_million" in data


# ---------------------------------------------------------------------------
# get_token_metrics
# ---------------------------------------------------------------------------

def test_get_token_metrics_known_model(mock_pricing_csv):
    """Full integration: known model returns all fields populated."""
    token_counter._load_model_pricing.cache_clear()

    with patch("pdd.server.token_counter.litellm.token_counter", return_value=200), \
         patch(
             "pdd.server.token_counter.litellm.get_model_info",
             return_value={"max_input_tokens": 128000},
         ):
        metrics = get_token_metrics("hello " * 100, model="gpt-4", pricing_csv=mock_pricing_csv)

    assert isinstance(metrics, TokenMetrics)
    assert metrics.token_count == 200
    assert metrics.context_limit == 128000
    assert metrics.context_usage_percent == pytest.approx((200 / 128000) * 100)
    assert metrics.cost_estimate is not None
    assert metrics.cost_estimate.model == "gpt-4"


def test_get_token_metrics_unknown_model():
    """Unknown model: context_limit and context_usage_percent are None."""
    with patch("pdd.server.token_counter.litellm.token_counter", return_value=50), \
         patch(
             "pdd.server.token_counter.litellm.get_model_info",
             side_effect=Exception("not mapped"),
         ):
        metrics = get_token_metrics("test", model="unknown-model-xyz", pricing_csv=None)

    assert metrics.token_count == 50
    assert metrics.context_limit is None
    assert metrics.context_usage_percent is None
    assert metrics.cost_estimate is None


def test_get_token_metrics_no_pricing():
    """No pricing CSV: cost_estimate is None but other fields are set."""
    with patch("pdd.server.token_counter.litellm.token_counter", return_value=10), \
         patch(
             "pdd.server.token_counter.litellm.get_model_info",
             return_value={"max_input_tokens": 128000},
         ):
        metrics = get_token_metrics("test", model="gpt-4o", pricing_csv=None)

    assert metrics.token_count == 10
    assert metrics.context_limit == 128000
    assert metrics.context_usage_percent is not None
    assert metrics.cost_estimate is None


def test_get_token_metrics_to_dict_unknown_model():
    """TokenMetrics.to_dict() handles None context fields without errors."""
    with patch("pdd.server.token_counter.litellm.token_counter", return_value=5), \
         patch(
             "pdd.server.token_counter.litellm.get_model_info",
             side_effect=Exception("not mapped"),
         ):
        metrics = get_token_metrics("hi", model="unknown", pricing_csv=None)

    data = metrics.to_dict()
    assert data["token_count"] == 5
    assert data["context_limit"] is None
    assert data["context_usage_percent"] is None
    assert data["cost_estimate"] is None


# ---------------------------------------------------------------------------
# Z3 Formal Verification Tests
# ---------------------------------------------------------------------------

def test_z3_cost_calculation_properties():
    """
    Verify mathematical properties of cost calculation:
    - Cost is non-negative for non-negative tokens and positive price.
    - Cost scales linearly with token count.
    """
    s = Solver()

    tokens = Int("tokens")
    price_per_million = Real("price_per_million")
    cost = Real("cost")

    # cost = (tokens / 1_000_000) * price_per_million
    calc_cost = (ToReal(tokens) / 1_000_000.0) * price_per_million
    s.add(cost == calc_cost)
    s.add(tokens >= 0)
    s.add(price_per_million > 0)

    # Negate the property: cost < 0 must be unsatisfiable
    s.add(cost < 0)
    assert s.check() == unsat, "Found a case where cost is negative despite positive inputs"


def test_z3_context_usage_percentage():
    """
    Verify context usage percentage logic (when context_limit is not None):
    - tokens == limit  →  usage == 100%
    - tokens > limit   →  usage > 100%
    - tokens == 0      →  usage == 0%
    """
    s = Solver()

    tokens = Int("tokens")
    limit = Int("limit")
    usage = Real("usage")

    # usage = (tokens / limit) * 100
    calc_usage = (ToReal(tokens) / ToReal(limit)) * 100.0
    s.add(usage == calc_usage)
    s.add(tokens >= 0)
    s.add(limit > 0)  # Only tested when context_limit is known (non-None)

    # Case 1: tokens == limit → usage == 100
    s.push()
    s.add(tokens == limit)
    s.add(usage != 100.0)
    assert s.check() == unsat, "Usage should be 100% when tokens equal the limit"
    s.pop()

    # Case 2: tokens > limit → usage > 100
    s.push()
    s.add(tokens > limit)
    s.add(usage <= 100.0)
    assert s.check() == unsat, "Usage should be > 100% when tokens exceed the limit"
    s.pop()

    # Case 3: tokens == 0 → usage == 0
    s.push()
    s.add(tokens == 0)
    s.add(usage != 0.0)
    assert s.check() == unsat, "Usage should be 0% when token count is zero"
    s.pop()


def ToReal(x):
    """Helper to cast Z3 Int to Real."""
    return x + 0.0
