"""
Cost tracker utility for calculating API costs from token usage.

This module provides functions to calculate the USD cost of Anthropic API calls
based on token usage including caching tokens.
"""

from typing import Optional

__all__ = ["calculate_cost"]


# Pricing per million tokens (as of January 2025)
# Source: https://www.anthropic.com/pricing
PRICING = {
    "claude-3-7-sonnet-20250219": {
        "input": 3.00,   # $3 per million input tokens
        "output": 15.00,  # $15 per million output tokens
        "cache_write": 3.75,  # $3.75 per million cache write tokens
        "cache_read": 0.30,   # $0.30 per million cache read tokens
    },
    "claude-3-5-sonnet-20241022": {
        "input": 3.00,
        "output": 15.00,
        "cache_write": 3.75,
        "cache_read": 0.30,
    },
    "claude-3-opus-20240229": {
        "input": 15.00,
        "output": 75.00,
        "cache_write": 18.75,
        "cache_read": 1.50,
    },
    "claude-3-sonnet-20240229": {
        "input": 3.00,
        "output": 15.00,
        "cache_write": 3.75,
        "cache_read": 0.30,
    },
    "claude-3-haiku-20240307": {
        "input": 0.25,
        "output": 1.25,
        "cache_write": 0.30,
        "cache_read": 0.03,
    },
}

# Default pricing for unknown models (use sonnet rates)
DEFAULT_PRICING = {
    "input": 3.00,
    "output": 15.00,
    "cache_write": 3.75,
    "cache_read": 0.30,
}


def calculate_cost(
    model: str,
    input_tokens: int,
    output_tokens: int,
    cache_write_tokens: int = 0,
    cache_read_tokens: int = 0,
) -> float:
    """
    Calculate the USD cost of an API call based on token usage.

    Args:
        model: The Claude model identifier
        input_tokens: Number of regular input tokens
        output_tokens: Number of output tokens
        cache_write_tokens: Number of tokens written to cache (optional)
        cache_read_tokens: Number of tokens read from cache (optional)

    Returns:
        Total cost in USD as a float

    Note:
        - Pricing is per million tokens
        - Cache write tokens are typically charged at 1.25x regular input rate
        - Cache read tokens are typically charged at 0.1x regular input rate
        - Returns 0.0 for invalid/negative token counts
    """
    # Ensure non-negative token counts
    input_tokens = max(0, input_tokens)
    output_tokens = max(0, output_tokens)
    cache_write_tokens = max(0, cache_write_tokens)
    cache_read_tokens = max(0, cache_read_tokens)

    # Get pricing for the model, fallback to default
    pricing = PRICING.get(model, DEFAULT_PRICING)

    # Calculate cost (prices are per million tokens)
    cost = 0.0
    cost += (input_tokens / 1_000_000) * pricing["input"]
    cost += (output_tokens / 1_000_000) * pricing["output"]
    cost += (cache_write_tokens / 1_000_000) * pricing["cache_write"]
    cost += (cache_read_tokens / 1_000_000) * pricing["cache_read"]

    return cost
