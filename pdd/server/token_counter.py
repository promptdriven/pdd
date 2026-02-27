"""
Token counting and cost estimation utilities.

Uses litellm for model-aware token counting and context window lookup.
Falls back to tiktoken for unknown models.
Loads model pricing from .pdd/llm_model.csv.
"""

from __future__ import annotations

import csv
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Optional, Dict

import litellm
import tiktoken

# Tiktoken fallback encoding for models litellm cannot identify
_FALLBACK_ENCODING = "cl100k_base"


@dataclass
class CostEstimate:
    """Cost estimation result."""

    input_cost: float
    model: str
    tokens: int
    cost_per_million: float
    currency: str = "USD"

    def to_dict(self) -> Dict:
        """Serialize to dict."""
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
    context_limit: Optional[int]
    context_usage_percent: Optional[float]
    cost_estimate: Optional[CostEstimate]

    def to_dict(self) -> Dict:
        """Serialize to dict."""
        return {
            "token_count": self.token_count,
            "context_limit": self.context_limit,
            "context_usage_percent": (
                round(self.context_usage_percent, 2)
                if self.context_usage_percent is not None
                else None
            ),
            "cost_estimate": self.cost_estimate.to_dict() if self.cost_estimate else None,
        }


@lru_cache(maxsize=1)
def _get_fallback_encoding() -> tiktoken.Encoding:
    """Get tiktoken fallback encoding (cached)."""
    return tiktoken.get_encoding(_FALLBACK_ENCODING)


def count_tokens(text: str, model: str = "gpt-4o") -> int:
    """
    Count tokens in text using litellm's model-aware tokenizer.

    Falls back to tiktoken cl100k_base encoding if litellm raises an exception
    (e.g. for unknown or locally-served models).

    Args:
        text: The text to count tokens for.
        model: Model name used to select the correct tokenizer.

    Returns:
        Token count.
    """
    if not text:
        return 0

    messages = [{"role": "user", "content": text}]
    try:
        return litellm.token_counter(model=model, messages=messages)
    except Exception:
        encoding = _get_fallback_encoding()
        return len(encoding.encode(text))


def get_context_limit(model: str) -> Optional[int]:
    """
    Get the input context window size for a model via litellm.

    Returns None for unknown models. Callers should skip context-window
    validation when None is returned rather than raising an error.

    Args:
        model: Model name.

    Returns:
        Context window size in input tokens, or None if the model is unknown
        to litellm.
    """
    try:
        info = litellm.get_model_info(model)
        return info.get("max_input_tokens")
    except Exception:
        return None


@lru_cache(maxsize=1)
def _load_model_pricing(csv_path: str) -> Dict[str, float]:
    """Load model pricing from CSV (cached)."""
    pricing: Dict[str, float] = {}

    try:
        with open(csv_path, "r") as f:
            reader = csv.DictReader(f)
            for row in reader:
                model = row.get("model", "")
                input_cost = row.get("input", "0")
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
    pricing_csv: Optional[Path] = None,
) -> Optional[CostEstimate]:
    """
    Estimate the input cost for a given token count.

    Args:
        token_count: Number of input tokens.
        model: Model name.
        pricing_csv: Path to llm_model.csv (optional).

    Returns:
        CostEstimate or None if pricing not found.
    """
    if pricing_csv is None or not pricing_csv.exists():
        return None

    pricing = _load_model_pricing(str(pricing_csv))

    if not pricing:
        return None

    cost_per_million = None
    matched_model = model

    # Exact match first
    if model in pricing:
        cost_per_million = pricing[model]
    else:
        # Partial/substring match
        model_lower = model.lower()
        for csv_model, cost in pricing.items():
            if model_lower in csv_model.lower() or csv_model.lower() in model_lower:
                cost_per_million = cost
                matched_model = csv_model
                break

    if cost_per_million is None:
        # Fall back to well-known defaults present in most pricing CSVs
        for default_model in ["claude-sonnet-4-20250514", "gpt-4o", "claude-3-5-sonnet-latest"]:
            if default_model in pricing:
                cost_per_million = pricing[default_model]
                matched_model = default_model
                break

    if cost_per_million is None:
        return None

    # Pricing is expressed per million tokens
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
    pricing_csv: Optional[Path] = None,
) -> TokenMetrics:
    """
    Get comprehensive token metrics for text.

    Args:
        text: The text to analyze.
        model: Model name.
        pricing_csv: Path to pricing CSV.

    Returns:
        TokenMetrics with count, context usage (if model is known), and cost.
    """
    token_count = count_tokens(text, model)
    context_limit = get_context_limit(model)
    context_usage = (token_count / context_limit) * 100 if context_limit else None
    cost = estimate_cost(token_count, model, pricing_csv)

    return TokenMetrics(
        token_count=token_count,
        context_limit=context_limit,
        context_usage_percent=context_usage,
        cost_estimate=cost,
    )
