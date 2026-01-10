import sys
import csv
import pytest
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock
from z3 import Solver, Int, Real, Implies, And, Or, unsat

# Add the source directory to sys.path to allow importing the module
# Assuming the test file is located at tests/server/test_token_counter.py
# and the code is at pdd/server/token_counter.py
ROOT_DIR = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT_DIR))

from pdd.server import token_counter
from pdd.server.token_counter import (
    count_tokens,
    get_context_limit,
    estimate_cost,
    get_token_metrics,
    CostEstimate,
    TokenMetrics,
    MODEL_CONTEXT_LIMITS
)

# --- Fixtures ---

@pytest.fixture
def mock_pricing_csv(tmp_path):
    """Creates a temporary CSV file with pricing data."""
    csv_content = [
        "model,input,output",
        "gpt-4,30.00,60.00",
        "claude-3-opus,15.00,75.00",
        "claude-sonnet-4-20250514,3.00,15.00", # Default fallback in code
        "gemini-1.5-pro,3.50,10.50"
    ]
    p = tmp_path / "llm_model.csv"
    p.write_text("\n".join(csv_content))
    return p

# --- Unit Tests: count_tokens ---

def test_count_tokens_empty():
    """Empty text should return 0 tokens."""
    assert count_tokens("") == 0
    assert count_tokens(None) == 0

def test_count_tokens_basic():
    """Test token counting with a simple string."""
    # We rely on the actual tiktoken library here as it's a dependency.
    # "hello world" is typically 2 tokens in cl100k_base.
    text = "hello world"
    count = count_tokens(text)
    assert count > 0
    assert isinstance(count, int)

# --- Unit Tests: get_context_limit ---

@pytest.mark.parametrize("model_name, expected_limit", [
    ("gpt-4", 128000),
    ("gpt-4-turbo", 128000),  # Partial match
    ("claude-3-opus", 200000),
    ("claude-sonnet-4", 200000),
    ("gemini-2-pro", 1000000),
    ("unknown-model-xyz", 128000), # Default fallback
])
def test_get_context_limit_resolution(model_name, expected_limit):
    """Verify context limits are resolved correctly based on model name."""
    assert get_context_limit(model_name) == expected_limit

def test_get_context_limit_case_insensitive():
    """Verify model matching is case insensitive."""
    assert get_context_limit("CLAUDE-3-OPUS") == 200000

# --- Unit Tests: estimate_cost ---

def test_estimate_cost_no_csv_path():
    """Should return None if CSV path is not provided or None."""
    assert estimate_cost(1000, "gpt-4", None) is None

def test_estimate_cost_file_not_found():
    """Should return None if CSV file does not exist."""
    assert estimate_cost(1000, "gpt-4", Path("/non/existent/path.csv")) is None

def test_estimate_cost_exact_match(mock_pricing_csv):
    """Test cost estimation with an exact model name match in CSV."""
    # gpt-4 is 30.00 per million
    # 1000 tokens -> (1000 / 1,000,000) * 30.00 = 0.03
    estimate = estimate_cost(1000, "gpt-4", mock_pricing_csv)
    assert estimate is not None
    assert estimate.input_cost == 0.03
    assert estimate.model == "gpt-4"
    assert estimate.cost_per_million == 30.00

def test_estimate_cost_partial_match(mock_pricing_csv):
    """Test cost estimation with a partial model name match."""
    # "claude-3-opus-20240229" should match "claude-3-opus" (15.00)
    estimate = estimate_cost(1000000, "claude-3-opus-20240229", mock_pricing_csv)
    assert estimate is not None
    assert estimate.input_cost == 15.00
    assert estimate.cost_per_million == 15.00

def test_estimate_cost_fallback_defaults(mock_pricing_csv):
    """Test fallback to known default models if specific model not found."""
    # "unknown-model" is not in CSV.
    # Code checks for defaults like 'claude-sonnet-4-20250514'.
    # Our mock CSV includes 'claude-sonnet-4-20250514' at 3.00.
    estimate = estimate_cost(1000, "unknown-super-model", mock_pricing_csv)
    assert estimate is not None
    assert estimate.model == "claude-sonnet-4-20250514"
    assert estimate.cost_per_million == 3.00

def test_estimate_cost_serialization(mock_pricing_csv):
    """Test to_dict method of CostEstimate."""
    estimate = estimate_cost(1000, "gpt-4", mock_pricing_csv)
    data = estimate.to_dict()
    assert data["input_cost"] == 0.03
    assert data["currency"] == "USD"
    assert data["tokens"] == 1000

# --- Unit Tests: get_token_metrics ---

def test_get_token_metrics_integration(mock_pricing_csv):
    """Test full integration of metrics gathering."""
    text = "hello " * 100 # Simple text
    model = "gpt-4"
    
    # We need to clear the lru_cache for _load_model_pricing to ensure it picks up the new temp file
    token_counter._load_model_pricing.cache_clear()
    
    metrics = get_token_metrics(text, model, mock_pricing_csv)
    
    assert isinstance(metrics, TokenMetrics)
    assert metrics.token_count > 0
    assert metrics.context_limit == 128000
    assert metrics.context_usage_percent > 0
    assert metrics.cost_estimate is not None
    assert metrics.cost_estimate.model == "gpt-4"

def test_get_token_metrics_no_pricing():
    """Test metrics generation without pricing file."""
    metrics = get_token_metrics("test", "gpt-4", None)
    assert metrics.token_count > 0
    assert metrics.cost_estimate is None
    
    data = metrics.to_dict()
    assert data["cost_estimate"] is None

# --- Z3 Formal Verification Tests ---

def test_z3_cost_calculation_properties():
    """
    Verify mathematical properties of cost calculation:
    1. Cost is non-negative for non-negative tokens and positive price.
    2. Cost scales linearly.
    """
    s = Solver()
    
    tokens = Int('tokens')
    price_per_million = Real('price_per_million')
    cost = Real('cost')
    
    # Definition of cost calculation from code: (token_count / 1_000_000) * cost_per_million
    # Note: Z3 Real division is exact.
    calc_cost = (ToReal(tokens) / 1000000.0) * price_per_million
    
    s.add(cost == calc_cost)
    
    # Constraint: Tokens are non-negative, Price is positive
    s.add(tokens >= 0)
    s.add(price_per_million > 0)
    
    # Property to verify: Cost must be >= 0
    # We negate the property and check for unsat
    s.add(cost < 0)
    
    assert s.check() == unsat, "Found a case where cost is negative despite positive inputs"

def test_z3_context_usage_percentage():
    """
    Verify context usage percentage logic:
    1. If tokens == limit, usage is 100%.
    2. If tokens > limit, usage > 100%.
    3. If tokens == 0, usage is 0%.
    """
    s = Solver()
    
    tokens = Int('tokens')
    limit = Int('limit')
    usage = Real('usage')
    
    # Logic from code: (token_count / context_limit) * 100
    # Guard against division by zero in code (limit > 0)
    calc_usage = (ToReal(tokens) / ToReal(limit)) * 100.0
    
    s.add(usage == calc_usage)
    s.add(tokens >= 0)
    s.add(limit > 0) # Context limit is always positive in the map
    
    # Case 1: tokens == limit => usage == 100
    s.push()
    s.add(tokens == limit)
    s.add(usage != 100.0)
    assert s.check() == unsat, "Usage should be 100% when tokens equals limit"
    s.pop()
    
    # Case 2: tokens > limit => usage > 100
    s.push()
    s.add(tokens > limit)
    s.add(usage <= 100.0)
    assert s.check() == unsat, "Usage should be > 100% when tokens exceed limit"
    s.pop()

    # Case 3: tokens == 0 => usage == 0
    s.push()
    s.add(tokens == 0)
    s.add(usage != 0.0)
    assert s.check() == unsat, "Usage should be 0% when tokens are 0"
    s.pop()

def ToReal(x):
    """Helper to cast Z3 Int to Real."""
    return x + 0.0