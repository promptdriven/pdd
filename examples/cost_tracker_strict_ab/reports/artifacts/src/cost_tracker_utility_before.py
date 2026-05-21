"""Cost tracker utility for Anthropic Claude API usage.

This stateless module computes the total USD cost of Claude API requests,
including support for Anthropic native prompt caching (cache writes at a
25% premium and cache reads at a 90% discount relative to standard input
token pricing).

The module is dependency-free (standard library only) and safe to import
from both synchronous and asynchronous code paths. It exposes a single
required function, :func:`calculate_cost`, plus an additive
:func:`calculate_cost_breakdown` helper for verbose callers.

Pricing constants are expressed in USD per 1,000,000 tokens (per-MTok)
and are centralized in :data:`MODEL_PRICING` so they can be updated in a
single place as Anthropic pricing evolves.
"""

from __future__ import annotations

import logging
from typing import Dict

logger = logging.getLogger(__name__)

__all__ = [
    "calculate_cost",
    "calculate_cost_breakdown",
    "MODEL_PRICING",
]


# ---------------------------------------------------------------------------
# Pricing constants
# ---------------------------------------------------------------------------
# Values are USD per 1,000,000 tokens (per-MTok). Update here if Anthropic
# pricing changes. Keys are canonical "family" identifiers; the resolver
# maps versioned model strings (e.g. "claude-3-7-sonnet-20250219") onto
# these canonical keys.
MODEL_PRICING: Dict[str, Dict[str, float]] = {
    "claude-3-7-sonnet": {"input_per_mtok": 3.00, "output_per_mtok": 15.00},
    "claude-3-5-sonnet": {"input_per_mtok": 3.00, "output_per_mtok": 15.00},
    "claude-3-5-haiku": {"input_per_mtok": 0.80, "output_per_mtok": 4.00},
    "claude-3-opus": {"input_per_mtok": 15.00, "output_per_mtok": 75.00},
    "claude-3-sonnet": {"input_per_mtok": 3.00, "output_per_mtok": 15.00},
    "claude-3-haiku": {"input_per_mtok": 0.25, "output_per_mtok": 1.25},
}

# Cache pricing multipliers relative to the standard input rate.
CACHE_WRITE_MULTIPLIER = 1.25  # 25% premium over input tokens
CACHE_READ_MULTIPLIER = 0.10  # 90% discount vs. input tokens

# Ordering matters for resolution: more specific families (e.g. "claude-3-5-haiku")
# must be checked before broader ones (e.g. "claude-3-haiku") to avoid
# ambiguity.
_FAMILY_RESOLUTION_ORDER = (
    "claude-3-7-sonnet",
    "claude-3-5-sonnet",
    "claude-3-5-haiku",
    "claude-3-opus",
    "claude-3-sonnet",
    "claude-3-haiku",
)

# Alternate naming aliases (e.g. "claude-3.5-sonnet", "claude-3-7") that map
# onto canonical families. Keys must be lowercase and pre-normalized.
_FAMILY_ALIASES = {
    "claude-3.7-sonnet": "claude-3-7-sonnet",
    "claude-3.5-sonnet": "claude-3-5-sonnet",
    "claude-3.5-haiku": "claude-3-5-haiku",
}


# ---------------------------------------------------------------------------
# Validation helpers
# ---------------------------------------------------------------------------
def _validate_tokens(name: str, value: int) -> int:
    """Validate a token-count argument.

    Args:
        name: Human-readable name of the parameter being validated.
        value: The value supplied by the caller.

    Returns:
        The validated integer value (unchanged) so callers can use this
        helper inline.

    Raises:
        ValueError: If ``value`` is not a non-negative ``int`` (note that
            ``bool`` is rejected even though it is an ``int`` subclass).
    """
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(
            f"{name} must be a non-negative integer; got {type(value).__name__}={value!r}"
        )
    if value < 0:
        raise ValueError(f"{name} must be >= 0; got {value}")
    return value


def _validate_model(model: str) -> str:
    """Validate the model string and return it unchanged.

    Args:
        model: Model identifier passed by the caller.

    Returns:
        The original model string.

    Raises:
        ValueError: If the model is not a non-empty string.
    """
    if not isinstance(model, str) or not model.strip():
        raise ValueError("model must be a non-empty string")
    return model


# ---------------------------------------------------------------------------
# Model resolution
# ---------------------------------------------------------------------------
def _resolve_model_family(model: str) -> str:
    """Resolve a (possibly versioned) model string to a canonical family key.

    The function normalizes ``model`` to lowercase and then tries (1) alias
    lookup, (2) prefix matching against known families in
    :data:`_FAMILY_RESOLUTION_ORDER`, and (3) substring containment as a
    last resort.

    Args:
        model: Anthropic model identifier (e.g. ``"claude-3-7-sonnet-20250219"``).

    Returns:
        The canonical family key used as a lookup in :data:`MODEL_PRICING`.

    Raises:
        ValueError: If no family matches.
    """
    normalized = model.strip().lower()

    # 1) Direct alias mapping.
    for alias, canonical in _FAMILY_ALIASES.items():
        if normalized.startswith(alias):
            return canonical

    # 2) Prefix matching against known families (specific-first order).
    for family in _FAMILY_RESOLUTION_ORDER:
        if normalized.startswith(family):
            return family

    # 3) Substring containment as a last resort.
    for family in _FAMILY_RESOLUTION_ORDER:
        if family in normalized:
            return family

    supported = ", ".join(_FAMILY_RESOLUTION_ORDER)
    raise ValueError(
        f"Unknown model '{model}'. Supported families: {supported}."
    )


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
    """Compute the total USD cost for a single Anthropic API call.

    Pricing rules:
      * Standard input tokens are charged at the model's input rate.
      * Standard output tokens are charged at the model's output rate.
      * Cache write tokens are charged at 1.25x the input rate.
      * Cache read tokens are charged at 0.10x the input rate.

    Args:
        model: Anthropic model identifier (versioned strings are accepted).
        input_tokens: Number of standard input tokens (>= 0).
        output_tokens: Number of standard output tokens (>= 0).
        cache_write_tokens: Number of tokens written to the prompt cache (>= 0).
        cache_read_tokens: Number of tokens read from the prompt cache (>= 0).

    Returns:
        Total cost in USD as a float. No rounding is applied; callers are
        responsible for any display formatting.

    Raises:
        ValueError: If ``model`` is invalid, the model family cannot be
            resolved, or any token count is not a non-negative integer.
    """
    _validate_model(model)
    input_tokens = _validate_tokens("input_tokens", input_tokens)
    output_tokens = _validate_tokens("output_tokens", output_tokens)
    cache_write_tokens = _validate_tokens("cache_write_tokens", cache_write_tokens)
    cache_read_tokens = _validate_tokens("cache_read_tokens", cache_read_tokens)

    family = _resolve_model_family(model)
    pricing = MODEL_PRICING[family]

    input_rate = pricing["input_per_mtok"] / 1_000_000.0
    output_rate = pricing["output_per_mtok"] / 1_000_000.0

    input_cost = input_tokens * input_rate
    output_cost = output_tokens * output_rate
    cache_write_cost = cache_write_tokens * input_rate * CACHE_WRITE_MULTIPLIER
    cache_read_cost = cache_read_tokens * input_rate * CACHE_READ_MULTIPLIER

    total = input_cost + output_cost + cache_write_cost + cache_read_cost

    logger.debug(
        "cost calc model=%s family=%s in=%d out=%d cw=%d cr=%d total=%.10f",
        model,
        family,
        input_tokens,
        output_tokens,
        cache_write_tokens,
        cache_read_tokens,
        total,
    )

    return total


def calculate_cost_breakdown(
    model: str,
    input_tokens: int,
    output_tokens: int,
    cache_write_tokens: int = 0,
    cache_read_tokens: int = 0,
) -> Dict[str, float]:
    """Return a detailed cost breakdown for verbose/diagnostic callers.

    The returned dictionary contains per-component USD costs as well as
    the total. This is purely additive; :func:`calculate_cost` remains
    the canonical interface.

    Args:
        model: Anthropic model identifier.
        input_tokens: Standard input token count.
        output_tokens: Standard output token count.
        cache_write_tokens: Tokens written to the prompt cache.
        cache_read_tokens: Tokens read from the prompt cache.

    Returns:
        A dict with keys: ``input_cost``, ``output_cost``,
        ``cache_write_cost``, ``cache_read_cost``, ``total_cost``,
        and ``family``.
    """
    _validate_model(model)
    input_tokens = _validate_tokens("input_tokens", input_tokens)
    output_tokens = _validate_tokens("output_tokens", output_tokens)
    cache_write_tokens = _validate_tokens("cache_write_tokens", cache_write_tokens)
    cache_read_tokens = _validate_tokens("cache_read_tokens", cache_read_tokens)

    family = _resolve_model_family(model)
    pricing = MODEL_PRICING[family]
    input_rate = pricing["input_per_mtok"] / 1_000_000.0
    output_rate = pricing["output_per_mtok"] / 1_000_000.0

    input_cost = input_tokens * input_rate
    output_cost = output_tokens * output_rate
    cache_write_cost = cache_write_tokens * input_rate * CACHE_WRITE_MULTIPLIER
    cache_read_cost = cache_read_tokens * input_rate * CACHE_READ_MULTIPLIER
    total_cost = input_cost + output_cost + cache_write_cost + cache_read_cost

    return {
        "family": family,  # type: ignore[dict-item]
        "input_cost": input_cost,
        "output_cost": output_cost,
        "cache_write_cost": cache_write_cost,
        "cache_read_cost": cache_read_cost,
        "total_cost": total_cost,
    }


# ---------------------------------------------------------------------------
# Sanity checks (only invoked under __main__ or by explicit caller)
# ---------------------------------------------------------------------------
def _run_sanity_checks() -> None:
    """Internal sanity checks; not executed on import.

    Verifies validation errors and a precise expected cost for a known
    model. Designed to be cheap and dependency-free.
    """
    # Negative tokens raise.
    try:
        calculate_cost("claude-3-7-sonnet", -1, 0)
    except ValueError:
        pass
    else:
        raise AssertionError("Expected ValueError for negative input_tokens")

    # bool rejected (bool is an int subclass).
    try:
        calculate_cost("claude-3-7-sonnet", True, 0)  # type: ignore[arg-type]
    except ValueError:
        pass
    else:
        raise AssertionError("Expected ValueError for bool input_tokens")

    # Unknown model raises.
    try:
        calculate_cost("gpt-4o", 10, 10)
    except ValueError:
        pass
    else:
        raise AssertionError("Expected ValueError for unknown model")

    # Empty model raises.
    try:
        calculate_cost("   ", 10, 10)
    except ValueError:
        pass
    else:
        raise AssertionError("Expected ValueError for empty model")

    # Zero tokens => zero cost.
    assert calculate_cost("claude-3-7-sonnet", 0, 0) == 0.0

    # Precise expected value for claude-3-7-sonnet ($3 in / $15 out per MTok).
    # 1,000,000 input + 1,000,000 output => 3 + 15 = 18 USD.
    cost = calculate_cost("claude-3-7-sonnet", 1_000_000, 1_000_000)
    assert abs(cost - 18.0) < 1e-9, f"unexpected cost {cost}"

    # Cache write premium (1.25x input) and cache read discount (0.10x input).
    # 1,000,000 cache_write => 3 * 1.25 = 3.75
    # 1,000,000 cache_read  => 3 * 0.10 = 0.30
    cost = calculate_cost(
        "claude-3-7-sonnet",
        input_tokens=0,
        output_tokens=0,
        cache_write_tokens=1_000_000,
        cache_read_tokens=1_000_000,
    )
    assert abs(cost - (3.75 + 0.30)) < 1e-9, f"unexpected cache cost {cost}"

    # Versioned model string resolves via prefix.
    cost_versioned = calculate_cost(
        "claude-3-7-sonnet-20250219", 1_000_000, 1_000_000
    )
    assert abs(cost_versioned - 18.0) < 1e-9

    # Haiku family resolves and uses cheaper rates.
    cost_haiku = calculate_cost("claude-3-haiku-20240307", 1_000_000, 1_000_000)
    # 0.25 + 1.25 = 1.50
    assert abs(cost_haiku - 1.50) < 1e-9, f"unexpected haiku cost {cost_haiku}"

    # Breakdown helper returns expected components.
    breakdown = calculate_cost_breakdown(
        "claude-3-7-sonnet", 1_000_000, 0, 0, 0
    )
    assert abs(breakdown["input_cost"] - 3.0) < 1e-9
    assert abs(breakdown["total_cost"] - 3.0) < 1e-9

    print("cost_tracker_utility sanity checks passed.")


if __name__ == "__main__":
    _run_sanity_checks()