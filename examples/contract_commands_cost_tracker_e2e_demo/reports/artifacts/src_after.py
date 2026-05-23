"""
Stateless utility for calculating Anthropic Claude API costs for the Edit File Tool.

This module exposes `calculate_cost` as the primary interface for computing input, output,
cache write, and cache read charges based on model-specific pricing tables. Pricing entries
are expressed in USD per 1,000,000 tokens and are resolved via robust model family matching.

Pricing rules implemented:
- Standard input tokens: charged at the model family's input rate.
- Standard output tokens: charged at the model family's output rate.
- Cache writes: 25% premium over input rate (1.25 x input_rate).
- Cache reads: 90% discount vs. input rate (0.10 x input_rate).

Callers are expected to supply token counts already extracted from Anthropic API responses;
this module performs no I/O and reads no environment variables.
"""

from __future__ import annotations

import logging
from typing import Dict, Mapping

LOGGER = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Pricing Table
# ---------------------------------------------------------------------------
# USD per 1,000,000 tokens. Update centrally when Anthropic pricing changes.
# Values reflect commonly published Anthropic Claude pricing for these families.
MODEL_PRICING: Mapping[str, Mapping[str, float]] = {
    "claude-3-7-sonnet": {"input_per_mtok": 3.00, "output_per_mtok": 15.00},
    "claude-3-5-sonnet": {"input_per_mtok": 3.00, "output_per_mtok": 15.00},
    "claude-3-5-haiku":  {"input_per_mtok": 0.80, "output_per_mtok": 4.00},
    "claude-3-opus":     {"input_per_mtok": 15.00, "output_per_mtok": 75.00},
    "claude-3-sonnet":   {"input_per_mtok": 3.00, "output_per_mtok": 15.00},
    "claude-3-haiku":    {"input_per_mtok": 0.25, "output_per_mtok": 1.25},
}

# Pricing multipliers for cache token categories.
_CACHE_WRITE_MULTIPLIER: float = 1.25  # 25% premium over input rate
_CACHE_READ_MULTIPLIER: float = 0.10   # 90% discount vs. input rate


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
def calculate_cost(
    model: str,
    input_tokens: int,
    output_tokens: int,
    cache_write_tokens: int = 0,
    cache_read_tokens: int = 0,
) -> float:
    """
    Calculate the total USD cost of Anthropic Claude API usage.

    Args:
        model: Anthropic Claude model identifier (e.g. "claude-3-7-sonnet-20250219").
            Version suffixes are resolved via prefix/family matching.
        input_tokens: Standard input tokens sent to the model. Must be int >= 0.
        output_tokens: Standard output tokens received from the model. Must be int >= 0.
        cache_write_tokens: Tokens written to Anthropic's prompt cache. Must be int >= 0.
            Charged at 1.25 x the input rate.
        cache_read_tokens: Tokens read from Anthropic's prompt cache. Must be int >= 0.
            Charged at 0.10 x the input rate.

    Returns:
        Total cost in USD as a float. No rounding is performed; callers format as needed.

    Raises:
        ValueError: If `model` is not a non-empty string, if any token count is not a
            non-negative integer (bools are rejected), or if the model cannot be
            resolved to a supported pricing family.
    """
    canonical = _resolve_model_family(model)

    vi = _validate_tokens("input_tokens", input_tokens)
    vo = _validate_tokens("output_tokens", output_tokens)
    vcw = _validate_tokens("cache_write_tokens", cache_write_tokens)
    vcr = _validate_tokens("cache_read_tokens", cache_read_tokens)

    rates = MODEL_PRICING[canonical]
    input_rate = rates["input_per_mtok"] / 1_000_000.0
    output_rate = rates["output_per_mtok"] / 1_000_000.0

    input_cost = vi * input_rate
    output_cost = vo * output_rate
    cache_write_cost = vcw * input_rate * _CACHE_WRITE_MULTIPLIER
    cache_read_cost = vcr * input_rate * _CACHE_READ_MULTIPLIER

    total = input_cost + output_cost + cache_write_cost + cache_read_cost

    LOGGER.debug(
        "calculate_cost(model=%s -> family=%s) input=%.10f output=%.10f "
        "cache_write=%.10f cache_read=%.10f total=%.10f",
        model, canonical, input_cost, output_cost,
        cache_write_cost, cache_read_cost, total,
    )

    return total


def calculate_cost_breakdown(
    model: str,
    input_tokens: int,
    output_tokens: int,
    cache_write_tokens: int = 0,
    cache_read_tokens: int = 0,
) -> Dict[str, float]:
    """
    Return a per-category cost breakdown in USD.

    Parameters mirror `calculate_cost`. The returned dictionary contains:
    "input_cost", "output_cost", "cache_write_cost", "cache_read_cost", "total_cost".

    Raises:
        ValueError: Same validation rules as `calculate_cost`.
    """
    canonical = _resolve_model_family(model)

    vi = _validate_tokens("input_tokens", input_tokens)
    vo = _validate_tokens("output_tokens", output_tokens)
    vcw = _validate_tokens("cache_write_tokens", cache_write_tokens)
    vcr = _validate_tokens("cache_read_tokens", cache_read_tokens)

    rates = MODEL_PRICING[canonical]
    input_rate = rates["input_per_mtok"] / 1_000_000.0
    output_rate = rates["output_per_mtok"] / 1_000_000.0

    input_cost = vi * input_rate
    output_cost = vo * output_rate
    cache_write_cost = vcw * input_rate * _CACHE_WRITE_MULTIPLIER
    cache_read_cost = vcr * input_rate * _CACHE_READ_MULTIPLIER
    total_cost = input_cost + output_cost + cache_write_cost + cache_read_cost

    return {
        "input_cost": input_cost,
        "output_cost": output_cost,
        "cache_write_cost": cache_write_cost,
        "cache_read_cost": cache_read_cost,
        "total_cost": total_cost,
    }


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------
def _resolve_model_family(model: str) -> str:
    """
    Resolve a (possibly versioned) model string to a canonical family key.

    Resolution strategy:
      1. Validate `model` is a non-empty string after strip().
      2. Normalize by stripping whitespace and lowercasing.
      3. Strip optional vendor prefixes like "anthropic/" or "anthropic:".
      4. Among MODEL_PRICING keys k, choose the longest key such that
         normalized.startswith(k) or k in normalized. Longest-match avoids
         ambiguity between, e.g., 'claude-3-sonnet' and 'claude-3-5-sonnet'.

    Raises:
        ValueError: If `model` is not a non-empty string, or if no family matches.
    """
    if not isinstance(model, str) or not model.strip():
        raise ValueError("model must be a non-empty string")

    normalized = model.strip().lower()
    # Strip common vendor prefixes.
    for vendor_prefix in ("anthropic/", "anthropic:"):
        if normalized.startswith(vendor_prefix):
            normalized = normalized[len(vendor_prefix):]
            break

    # Also handle dot-style versioning (e.g. claude-3.5-sonnet -> claude-3-5-sonnet)
    dot_normalized = normalized.replace(".", "-")

    best_key: str = ""
    for key in MODEL_PRICING.keys():
        for candidate in (normalized, dot_normalized):
            if candidate.startswith(key) or key in candidate:
                if len(key) > len(best_key):
                    best_key = key
                break

    if not best_key:
        supported = sorted(MODEL_PRICING.keys())
        raise ValueError(
            f"Unsupported Anthropic model '{model}'. "
            f"Supported families: {supported}."
        )

    LOGGER.debug("Resolved model %r to family %r", model, best_key)
    return best_key


def _validate_tokens(name: str, value: int) -> int:
    """
    Validate that `value` is a non-negative integer (rejecting bools).

    Returns:
        The validated integer value (returned so callers can chain).

    Raises:
        ValueError: If `value` is a bool, not an int, or negative.
    """
    if isinstance(value, bool):
        raise ValueError(
            f"{name} must be a non-negative int; received bool ({value!r})"
        )
    if not isinstance(value, int):
        raise ValueError(
            f"{name} must be a non-negative int; received {type(value).__name__} "
            f"({value!r})"
        )
    if value < 0:
        raise ValueError(
            f"{name} must be a non-negative int; received {value}"
        )
    return value


# ---------------------------------------------------------------------------
# Sanity checks (not run on import)
# ---------------------------------------------------------------------------
def _run_sanity_checks() -> None:
    """
    Internal sanity tests demonstrating module correctness.

    Not invoked on import; safe to call from unit tests or `__main__`.
    """
    import math

    # 1) Known model, simple counts.
    haiku_rates = MODEL_PRICING["claude-3-5-haiku"]
    expected = 1_000_000 * (haiku_rates["input_per_mtok"] / 1_000_000.0)
    actual = calculate_cost("claude-3-5-haiku-20241022",
                            input_tokens=1_000_000, output_tokens=0)
    assert math.isclose(actual, expected, rel_tol=1e-12, abs_tol=1e-15), (
        f"expected {expected}, got {actual}"
    )

    # 2) Versioned model resolves to its family.
    v1 = calculate_cost("claude-3-7-sonnet-20250219", 100, 50, 10, 5)
    v2 = calculate_cost("claude-3-7-sonnet", 100, 50, 10, 5)
    assert v1 == v2, "Versioned model must match family pricing exactly"

    # 3) Zero tokens -> zero cost.
    assert calculate_cost("claude-3-opus", 0, 0, 0, 0) == 0.0

    # 4) Negative tokens raise ValueError.
    for bad in (-1, -100):
        try:
            calculate_cost("claude-3-opus", bad, 0)
        except ValueError:
            pass
        else:
            raise AssertionError(f"Expected ValueError for input_tokens={bad}")

    # 5) Bool tokens raise ValueError.
    try:
        calculate_cost("claude-3-haiku", True, 0)  # type: ignore[arg-type]
    except ValueError:
        pass
    else:
        raise AssertionError("Expected ValueError for bool input_tokens")

    # 6) Non-int tokens raise ValueError.
    try:
        calculate_cost("claude-3-haiku", 1.5, 0)  # type: ignore[arg-type]
    except ValueError:
        pass
    else:
        raise AssertionError("Expected ValueError for float input_tokens")

    # 7) Unknown model raises ValueError with supported families in message.
    try:
        calculate_cost("gpt-4o", 1, 1)
    except ValueError as e:
        msg = str(e)
        assert "gpt-4o" in msg, "Error message must include unknown model"
        for fam in MODEL_PRICING.keys():
            assert fam in msg, f"Error message must list supported family {fam}"
    else:
        raise AssertionError("Expected ValueError for unknown model 'gpt-4o'")

    # 8) Empty / non-string model raises ValueError.
    for bad_model in ("", "   ", None, 123):
        try:
            calculate_cost(bad_model, 1, 1)  # type: ignore[arg-type]
        except ValueError:
            pass
        else:
            raise AssertionError(f"Expected ValueError for model={bad_model!r}")

    # 9) Breakdown total matches calculate_cost result.
    bd = calculate_cost_breakdown("claude-3-5-sonnet",
                                  input_tokens=3000, output_tokens=1500,
                                  cache_write_tokens=200)
    total = calculate_cost("claude-3-5-sonnet",
                           input_tokens=3000, output_tokens=1500,
                           cache_write_tokens=200)
    assert math.isclose(bd["total_cost"], total, rel_tol=1e-12, abs_tol=1e-15)
    assert bd["cache_read_cost"] == 0.0

    # 10) Determinism: identical args -> bitwise equal results.
    a = calculate_cost("claude-3-opus", 1234, 567, 89, 12)
    b = calculate_cost("claude-3-opus", 1234, 567, 89, 12)
    assert a == b, "calculate_cost must be deterministic for identical args"


if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG, format="%(levelname)s: %(message)s")
    _run_sanity_checks()
    print("cost_tracker_utility: all sanity checks passed.")