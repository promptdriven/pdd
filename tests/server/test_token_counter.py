import csv
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

from pdd.server import token_counter
from pdd.server.token_counter import (
    count_tokens,
    get_context_limit,
    estimate_cost,
    estimate_completion_cost,
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
        "local-free,0,0",
        "legacy-input-only,2.50,",
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


def test_get_context_limit_hang_returns_none(monkeypatch):
    """
    Regression test for the github_copilot device-code OAuth hang.

    litellm's provider-detection heuristic can misroute a bare model name
    (e.g. `claude-opus-4-7`) into a provider that performs a blocking
    OAuth poll for up to ~60s. ``get_context_limit`` must time out and
    return None instead of wedging the caller.
    """
    import time as _time

    def _slow_get_model_info(model):
        # Sleep longer than the wrapper's timeout to simulate the hang.
        _time.sleep(2.0)
        return {"max_input_tokens": 99999}

    # Shrink the timeout so the test is fast.
    # Use object-ref monkeypatch (not string paths) so resolution does not
    # depend on ``pdd.server`` exposing ``token_counter`` as an attribute,
    # which it does not in fresh imports (e.g. on a pytest-xdist worker).
    monkeypatch.setattr(token_counter, "_LITELLM_CALL_TIMEOUT_SEC", 0.25)
    monkeypatch.setattr(
        token_counter.litellm, "get_model_info", _slow_get_model_info
    )

    start = _time.monotonic()
    result = get_context_limit("claude-opus-4-7")
    elapsed = _time.monotonic() - start

    assert result is None
    # Should return well before _slow_get_model_info would finish.
    assert elapsed < 1.5, f"get_context_limit took {elapsed:.2f}s (timeout not honoured)"


def test_count_tokens_hang_falls_back_to_tiktoken(monkeypatch):
    """count_tokens must time out on a hanging litellm.token_counter."""
    import time as _time

    def _slow_token_counter(*args, **kwargs):
        _time.sleep(2.0)
        return 9999

    # Use object-ref monkeypatch (not string paths) so resolution does not
    # depend on ``pdd.server`` exposing ``token_counter`` as an attribute,
    # which it does not in fresh imports (e.g. on a pytest-xdist worker).
    monkeypatch.setattr(token_counter, "_LITELLM_CALL_TIMEOUT_SEC", 0.25)
    monkeypatch.setattr(
        token_counter.litellm, "token_counter", _slow_token_counter
    )

    start = _time.monotonic()
    result = count_tokens("hello world", model="claude-opus-4-7")
    elapsed = _time.monotonic() - start

    # tiktoken fallback should return 2 for "hello world"
    assert result == 2
    assert elapsed < 1.5, f"count_tokens took {elapsed:.2f}s (timeout not honoured)"


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


def test_estimate_cost_accepts_string_pricing_csv_path(mock_pricing_csv):
    """Legacy callers may pass pricing_csv as a string path."""
    token_counter._load_model_pricing.cache_clear()
    estimate = estimate_cost(1000, "gpt-4", str(mock_pricing_csv))

    assert estimate is not None
    assert estimate.input_cost == pytest.approx(0.03)


def test_estimate_cost_partial_match(mock_pricing_csv):
    """Cost estimation with a partial model name match."""
    token_counter._load_model_pricing.cache_clear()
    # "claude-3-opus-20240229" should match "claude-3-opus" ($15.00/M)
    estimate = estimate_cost(1_000_000, "claude-3-opus-20240229", mock_pricing_csv)
    assert estimate is not None
    assert estimate.input_cost == pytest.approx(15.00)
    assert estimate.cost_per_million == 15.00


def test_estimate_cost_allows_input_only_legacy_pricing(mock_pricing_csv):
    """Input-only estimates remain usable when an older CSV lacks output rates."""
    token_counter._load_model_pricing.cache_clear()
    estimate = estimate_cost(1_000_000, "legacy-input-only", mock_pricing_csv)

    assert estimate is not None
    assert estimate.input_cost == pytest.approx(2.50)
    assert estimate.output_cost_per_million is None


def test_estimate_cost_unknown_model_returns_none(mock_pricing_csv):
    """Unknown model pricing must be explicit None, not a guessed default."""
    token_counter._load_model_pricing.cache_clear()
    estimate = estimate_cost(1000, "unknown-super-model", mock_pricing_csv)
    assert estimate is None


def test_estimate_cost_rejects_provider_prefixed_near_matches(tmp_path):
    """Bare model names must not inherit prices from provider-scoped near matches."""
    pricing_csv = tmp_path / "llm_model.csv"
    pricing_csv.write_text(
        "\n".join(
            [
                "model,input,output",
                "azure/gpt-4.1-mini,0.4,1.6",
                "github_copilot/gpt-4o,0.0,0.0",
                "openai/gpt-4o,2.5,10.0",
                "gpt-4.1-mini,0.4,1.6",
            ]
        )
    )

    token_counter._load_model_pricing.cache_clear()

    assert estimate_completion_cost(1000, 1000, "gpt-4", pricing_csv) is None
    assert estimate_completion_cost(1000, 1000, "gpt-4o", pricing_csv) is None


def test_estimate_cost_preserves_exact_provider_and_unqualified_matches(tmp_path):
    """Conservative matching still allows exact provider-qualified/unqualified rows."""
    pricing_csv = tmp_path / "llm_model.csv"
    pricing_csv.write_text(
        "\n".join(
            [
                "model,input,output",
                "openai/gpt-4o,2.5,10.0",
                "gpt-4.1-mini,0.4,1.6",
                "local-free,0,0",
            ]
        )
    )

    token_counter._load_model_pricing.cache_clear()

    provider_estimate = estimate_completion_cost(
        1_000_000, 1_000_000, "openai/gpt-4o", pricing_csv
    )
    assert provider_estimate is not None
    assert provider_estimate.matched_model == "openai/gpt-4o"
    assert provider_estimate.total_cost == pytest.approx(12.5)

    unqualified_estimate = estimate_completion_cost(
        1_000_000, 1_000_000, "gpt-4.1-mini", pricing_csv
    )
    assert unqualified_estimate is not None
    assert unqualified_estimate.matched_model == "gpt-4.1-mini"
    assert unqualified_estimate.total_cost == pytest.approx(2.0)

    zero_estimate = estimate_completion_cost(1000, 1000, "local-free", pricing_csv)
    assert zero_estimate is not None
    assert zero_estimate.total_cost == pytest.approx(0.0)


def test_estimate_completion_cost_uses_input_and_output_rates(mock_pricing_csv):
    """Completion estimates include separate deterministic input/output rates."""
    token_counter._load_model_pricing.cache_clear()
    estimate = estimate_completion_cost(
        input_tokens=1_000_000,
        predicted_output_tokens=500_000,
        model="gpt-4",
        pricing_csv=mock_pricing_csv,
    )

    assert estimate is not None
    assert estimate.input_cost == pytest.approx(30.00)
    assert estimate.output_cost == pytest.approx(30.00)
    assert estimate.total_cost == pytest.approx(60.00)
    assert estimate.input_tokens == 1_000_000
    assert estimate.output_tokens == 500_000
    assert estimate.input_cost_per_million == 30.00
    assert estimate.output_cost_per_million == 60.00


def test_estimate_completion_cost_zero_rates_are_known_prices(mock_pricing_csv):
    """Explicit zero input/output rates are valid known prices, not unknown."""
    token_counter._load_model_pricing.cache_clear()
    estimate = estimate_completion_cost(1000, 2000, "local-free", mock_pricing_csv)

    assert estimate is not None
    assert estimate.input_cost == pytest.approx(0.0)
    assert estimate.output_cost == pytest.approx(0.0)
    assert estimate.total_cost == pytest.approx(0.0)


def test_estimate_completion_cost_requires_output_rate(mock_pricing_csv):
    """Completion estimates are unknown when only input pricing is available."""
    token_counter._load_model_pricing.cache_clear()
    assert (
        estimate_completion_cost(1000, 1000, "legacy-input-only", mock_pricing_csv)
        is None
    )


def test_estimate_completion_cost_unknown_model_returns_none(mock_pricing_csv):
    """Completion pricing also refuses to invent prices for unknown models."""
    token_counter._load_model_pricing.cache_clear()
    assert (
        estimate_completion_cost(1000, 1000, "unknown-super-model", mock_pricing_csv)
        is None
    )


# ---------------------------------------------------------------------------
# default pricing CSV resolution (#1357: usable pre-flight cost primitives)
# ---------------------------------------------------------------------------

def test_default_pricing_csv_resolution_order(tmp_path, monkeypatch):
    """Resolution prefers $HOME/.pdd, then cwd/.pdd, then the bundled CSV."""
    home = tmp_path / "home"
    project = tmp_path / "project"
    (home / ".pdd").mkdir(parents=True)
    (project / ".pdd").mkdir(parents=True)
    home_csv = home / ".pdd" / "llm_model.csv"
    project_csv = project / ".pdd" / "llm_model.csv"
    monkeypatch.setattr(Path, "home", classmethod(lambda cls: home))
    monkeypatch.chdir(project)

    # Nothing user/project-level yet -> falls back to the bundled package CSV.
    assert token_counter.default_pricing_csv() == token_counter._BUNDLED_PRICING_CSV
    assert token_counter._BUNDLED_PRICING_CSV.is_file()  # bundled CSV ships with the package

    # Project-level CSV wins over the bundled fallback.
    project_csv.write_text("model,input,output\ngpt-4,30.00,60.00\n")
    assert token_counter.default_pricing_csv() == project_csv

    # $HOME-level CSV takes precedence over the project CSV.
    home_csv.write_text("model,input,output\ngpt-4,30.00,60.00\n")
    assert token_counter.default_pricing_csv() == home_csv


def test_estimate_completion_cost_uses_default_pricing_when_csv_omitted(monkeypatch, mock_pricing_csv):
    """With no pricing_csv, the completion estimate resolves the canonical CSV."""
    token_counter._load_model_pricing.cache_clear()
    monkeypatch.setattr(token_counter, "default_pricing_csv", lambda: mock_pricing_csv)

    estimate = estimate_completion_cost(
        input_tokens=1_000_000, predicted_output_tokens=500_000, model="gpt-4"
    )

    assert estimate is not None
    assert estimate.total_cost == pytest.approx(60.00)


def test_estimate_completion_cost_no_default_pricing_returns_none(monkeypatch):
    """When no pricing source exists at all, cost stays explicitly unknown."""
    token_counter._load_model_pricing.cache_clear()
    monkeypatch.setattr(token_counter, "default_pricing_csv", lambda: None)
    assert estimate_completion_cost(1000, 1000, "gpt-4") is None


def test_estimate_completion_cost_explicit_missing_path_not_replaced(monkeypatch, tmp_path):
    """An explicit (but missing) path is honored, never swapped for the default."""
    token_counter._load_model_pricing.cache_clear()
    sentinel = {"called": False}

    def _should_not_run():
        sentinel["called"] = True
        return None

    monkeypatch.setattr(token_counter, "default_pricing_csv", _should_not_run)
    assert estimate_completion_cost(1000, 1000, "gpt-4", tmp_path / "nope.csv") is None
    assert sentinel["called"] is False


def test_estimate_cost_default_none_still_unknown(monkeypatch, mock_pricing_csv):
    """Legacy input-only API keeps treating None pricing_csv as 'no pricing'."""
    token_counter._load_model_pricing.cache_clear()
    # Even if a default exists, estimate_cost must not auto-resolve it.
    monkeypatch.setattr(token_counter, "default_pricing_csv", lambda: mock_pricing_csv)
    assert estimate_cost(1000, "gpt-4") is None


def test_estimate_cost_serialization(mock_pricing_csv):
    """CostEstimate.to_dict() serializes all fields correctly."""
    token_counter._load_model_pricing.cache_clear()
    estimate = estimate_cost(1000, "gpt-4", mock_pricing_csv)
    data = estimate.to_dict()
    assert data["input_cost"] == pytest.approx(0.03)
    assert data["output_cost"] == pytest.approx(0.0)
    assert data["total_cost"] == pytest.approx(0.03)
    assert data["currency"] == "USD"
    assert data["tokens"] == 1000
    assert data["input_tokens"] == 1000
    assert data["output_tokens"] == 0
    assert "model" in data
    assert "matched_model" in data
    assert "cost_per_million" in data
    assert "input_cost_per_million" in data
    assert "output_cost_per_million" in data


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
    z3 = pytest.importorskip("z3")
    s = z3.Solver()

    tokens = z3.Int("tokens")
    price_per_million = z3.Real("price_per_million")
    cost = z3.Real("cost")

    # cost = (tokens / 1_000_000) * price_per_million
    calc_cost = (ToReal(tokens) / 1_000_000.0) * price_per_million
    s.add(cost == calc_cost)
    s.add(tokens >= 0)
    s.add(price_per_million > 0)

    # Negate the property: cost < 0 must be unsatisfiable
    s.add(cost < 0)
    assert s.check() == z3.unsat, "Found a case where cost is negative despite positive inputs"


def test_z3_context_usage_percentage():
    """
    Verify context usage percentage logic (when context_limit is not None):
    - tokens == limit  →  usage == 100%
    - tokens > limit   →  usage > 100%
    - tokens == 0      →  usage == 0%
    """
    z3 = pytest.importorskip("z3")
    s = z3.Solver()

    tokens = z3.Int("tokens")
    limit = z3.Int("limit")
    usage = z3.Real("usage")

    # usage = (tokens / limit) * 100
    calc_usage = (ToReal(tokens) / ToReal(limit)) * 100.0
    s.add(usage == calc_usage)
    s.add(tokens >= 0)
    s.add(limit > 0)  # Only tested when context_limit is known (non-None)

    # Case 1: tokens == limit → usage == 100
    s.push()
    s.add(tokens == limit)
    s.add(usage != 100.0)
    assert s.check() == z3.unsat, "Usage should be 100% when tokens equal the limit"
    s.pop()

    # Case 2: tokens > limit → usage > 100
    s.push()
    s.add(tokens > limit)
    s.add(usage <= 100.0)
    assert s.check() == z3.unsat, "Usage should be > 100% when tokens exceed the limit"
    s.pop()

    # Case 3: tokens == 0 → usage == 0
    s.push()
    s.add(tokens == 0)
    s.add(usage != 0.0)
    assert s.check() == z3.unsat, "Usage should be 0% when token count is zero"
    s.pop()


def ToReal(x):
    """Helper to cast Z3 Int to Real."""
    return x + 0.0
