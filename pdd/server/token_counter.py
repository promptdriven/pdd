"""
Token counting and cost estimation utilities.

Uses tiktoken for local token estimation without API calls.
Loads model pricing from .pdd/llm_model.csv.
"""

from __future__ import annotations

import csv
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Optional, Dict

import tiktoken

# Default context limits by model family (tokens)
MODEL_CONTEXT_LIMITS = {
    "gpt-4": 128000,
    "gpt-5": 200000,
    "claude-3": 200000,
    "claude-sonnet-4": 200000,
    "claude-opus-4": 200000,
    "claude-haiku-4": 200000,
    "gemini-2": 1000000,
    "gemini-3": 1000000,
    "default": 128000,
}

# Tiktoken encodings - use cl100k_base for most modern models
ENCODING_NAME = "cl100k_base"


@dataclass
class CostEstimate:
    """Cost estimation result."""
    input_cost: float
    model: str
    tokens: int
    cost_per_million: float
    currency: str = "USD"

    def to_dict(self) -> Dict:
        return {
            "input_cost": round(self.input_cost, 6),
            "model": self.model,
            "tokens": self.tokens,
            "cost_per_million": self.cost_per_million,
            "currency": self.currency,
        }


@dataclass
class TokenMetrics:
    """Combined token metrics result."""
    token_count: int
    context_limit: int
    context_usage_percent: float
    cost_estimate: Optional[CostEstimate]

    def to_dict(self) -> Dict:
        return {
            "token_count": self.token_count,
            "context_limit": self.context_limit,
            "context_usage_percent": round(self.context_usage_percent, 2),
            "cost_estimate": self.cost_estimate.to_dict() if self.cost_estimate else None,
        }


@lru_cache(maxsize=1)
def _get_encoding() -> tiktoken.Encoding:
    """Get tiktoken encoding (cached)."""
    return tiktoken.get_encoding(ENCODING_NAME)


def count_tokens(text: str) -> int:
    """
    Count tokens in text using tiktoken.

    Args:
        text: The text to count tokens for

    Returns:
        Token count
    """
    if not text:
        return 0

    encoding = _get_encoding()
    return len(encoding.encode(text))


def get_context_limit(model: str) -> int:
    """
    Get the context limit for a model.

    Args:
        model: Model name

    Returns:
        Context limit in tokens
    """
    model_lower = model.lower()

    for prefix, limit in MODEL_CONTEXT_LIMITS.items():
        if prefix in model_lower:
            return limit

    return MODEL_CONTEXT_LIMITS["default"]


@lru_cache(maxsize=1)
def _load_model_pricing(csv_path: str) -> Dict[str, float]:
    """Load model pricing from CSV (cached)."""
    pricing = {}

    try:
        with open(csv_path, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                model = row.get('model', '')
                input_cost = row.get('input', '0')
                try:
                    pricing[model] = float(input_cost)
                except ValueError:
                    continue
    except (FileNotFoundError, PermissionError):
        pass

    return pricing


def estimate_cost(
    token_count: int,
    model: str,
    pricing_csv: Optional[Path] = None
) -> Optional[CostEstimate]:
    """
    Estimate the input cost for a given token count.

    Args:
        token_count: Number of input tokens
        model: Model name
        pricing_csv: Path to llm_model.csv (optional)

    Returns:
        CostEstimate or None if pricing not found
    """
    if pricing_csv is None or not pricing_csv.exists():
        return None

    pricing = _load_model_pricing(str(pricing_csv))

    if not pricing:
        return None

    # Find matching model
    cost_per_million = None
    matched_model = model

    # Try exact match first
    if model in pricing:
        cost_per_million = pricing[model]
    else:
        # Try partial match
        model_lower = model.lower()
        for csv_model, cost in pricing.items():
            if model_lower in csv_model.lower() or csv_model.lower() in model_lower:
                cost_per_million = cost
                matched_model = csv_model
                break

    if cost_per_million is None:
        # Use a default model for estimation
        for default_model in ['claude-sonnet-4-20250514', 'gpt-4o', 'claude-3-5-sonnet-latest']:
            if default_model in pricing:
                cost_per_million = pricing[default_model]
                matched_model = default_model
                break

    if cost_per_million is None:
        return None

    # Calculate cost (pricing is per million tokens)
    input_cost = (token_count / 1_000_000) * cost_per_million

    return CostEstimate(
        input_cost=input_cost,
        model=matched_model,
        tokens=token_count,
        cost_per_million=cost_per_million,
    )


def get_token_metrics(
    text: str,
    model: str = "claude-sonnet-4-20250514",
    pricing_csv: Optional[Path] = None
) -> TokenMetrics:
    """
    Get comprehensive token metrics for text.

    Args:
        text: The text to analyze
        model: Model name
        pricing_csv: Path to pricing CSV

    Returns:
        TokenMetrics with count, context usage, and cost
    """
    token_count = count_tokens(text)
    context_limit = get_context_limit(model)
    context_usage = (token_count / context_limit) * 100 if context_limit > 0 else 0
    cost = estimate_cost(token_count, model, pricing_csv)

    return TokenMetrics(
        token_count=token_count,
        context_limit=context_limit,
        context_usage_percent=context_usage,
        cost_estimate=cost,
    )
