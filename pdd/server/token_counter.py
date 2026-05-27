"""
Token counting and cost estimation utilities.

Uses litellm for model-aware token counting and context window lookup.
Falls back to tiktoken for unknown models.
Loads model pricing from .pdd/llm_model.csv.
"""

from __future__ import annotations

import csv
import logging
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeoutError
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, Optional, Dict

import litellm
import tiktoken

logger = logging.getLogger(__name__)

# Tiktoken fallback encoding for models litellm cannot identify
_FALLBACK_ENCODING = "cl100k_base"

# Hard cap (seconds) on any individual litellm provider-detection call.
# litellm's get_llm_provider() can misroute bare-name models into providers
# that perform a blocking device-code OAuth poll (e.g. github_copilot),
# wedging the CLI for ~60s per retry. A small timeout converts that hang
# into a fast "unknown model" fallback.
_LITELLM_CALL_TIMEOUT_SEC = 5.0

def _call_litellm_with_timeout(
    fn: Callable[..., Any],
    *args: Any,
    timeout: Optional[float] = None,
    **kwargs: Any,
) -> Any:
    """
    Run a litellm call in a worker thread with a hard timeout.

    Raises TimeoutError if the call doesn't finish in time, so callers can
    treat hangs the same way they treat exceptions. The orphaned worker
    thread is left to clean up on its own (it'll exit when litellm's
    internal poll loop ends or when the interpreter shuts down).
    """
    # Resolve the timeout dynamically so tests (and operators) can tune
    # ``_LITELLM_CALL_TIMEOUT_SEC`` at runtime.
    effective_timeout = timeout if timeout is not None else _LITELLM_CALL_TIMEOUT_SEC
    # Don't use ``with ThreadPoolExecutor``: its __exit__ calls
    # ``shutdown(wait=True)`` which would block on the orphaned worker
    # thread, defeating the timeout. Instead shutdown(wait=False) and let
    # the worker exit on its own when litellm's poll loop completes.
    executor = ThreadPoolExecutor(max_workers=1, thread_name_prefix="litellm-probe")
    try:
        future = executor.submit(fn, *args, **kwargs)
        try:
            return future.result(timeout=effective_timeout)
        except FuturesTimeoutError as exc:
            future.cancel()
            raise TimeoutError(
                f"litellm call {getattr(fn, '__qualname__', repr(fn))} timed out"
                f" after {effective_timeout:.1f}s (likely provider-detection hang)"
            ) from exc
    finally:
        executor.shutdown(wait=False)


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


def _tiktoken_fallback(text: str) -> int:
    """Fallback token count via tiktoken cl100k_base."""
    encoding = _get_fallback_encoding()
    return len(encoding.encode(text))


def _messages_to_text(messages: Any) -> str:
    """Best-effort flattening of a chat messages list to a single string."""
    if not messages:
        return ""
    if isinstance(messages, str):
        return messages
    parts = []
    try:
        for msg in messages:
            content = msg.get("content") if isinstance(msg, dict) else None
            if isinstance(content, str):
                parts.append(content)
            elif isinstance(content, list):
                for chunk in content:
                    if isinstance(chunk, dict):
                        text = chunk.get("text")
                        if isinstance(text, str):
                            parts.append(text)
                    elif isinstance(chunk, str):
                        parts.append(chunk)
    except Exception:
        return ""
    return "\n".join(parts)


def count_tokens_for_messages(messages: Any, model: str = "gpt-4o") -> int:
    """
    Count tokens for a chat messages list, hang-safe against litellm provider
    detection issues. Falls back to tiktoken cl100k_base on error/timeout.
    """
    if not messages:
        return 0

    try:
        return _call_litellm_with_timeout(
            litellm.token_counter, model=model, messages=messages
        )
    except Exception as exc:
        logger.warning(
            "count_tokens_for_messages: tiktoken fallback for model=%s (%s)",
            model,
            exc,
        )
        return _tiktoken_fallback(_messages_to_text(messages))


def count_tokens(text: str, model: str = "gpt-4o") -> int:
    """
    Count tokens in text using litellm's model-aware tokenizer.

    Falls back to tiktoken cl100k_base encoding if litellm raises an exception
    or hangs (e.g. for unknown or locally-served models, or when litellm's
    provider detection misroutes the model into a blocking OAuth flow).

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
        return _call_litellm_with_timeout(
            litellm.token_counter, model=model, messages=messages
        )
    except Exception as exc:  # includes TimeoutError from our wrapper
        logger.warning(
            "count_tokens: falling back to tiktoken for model=%s (%s)",
            model,
            exc,
        )
        return _tiktoken_fallback(text)


def get_context_limit(model: str) -> Optional[int]:
    """
    Get the input context window size for a model via litellm.

    Returns None for unknown models. Callers should skip context-window
    validation when None is returned rather than raising an error.

    This function is defensive against two failure modes in litellm:

    1. Exceptions raised by ``litellm.get_model_info`` for unknown models —
       caught and treated as "unknown" (returns None).
    2. Hangs caused by litellm's provider-detection heuristic misrouting
       bare model names into providers that perform a blocking device-code
       OAuth flow (notably github_copilot). The call is wrapped in a
       thread-based timeout so a stuck provider-detection path returns
       None instead of wedging the entire CLI for ~60s per retry.

    Args:
        model: Model name.

    Returns:
        Context window size in input tokens, or None if the model is unknown
        to litellm, the lookup times out, or the call raises.
    """
    try:
        info = _call_litellm_with_timeout(litellm.get_model_info, model)
        return info.get("max_input_tokens") if info else None
    except Exception as exc:  # includes TimeoutError from our wrapper
        logger.warning(
            "get_context_limit: litellm.get_model_info failed for %s (%s); "
            "skipping context-window validation",
            model,
            exc,
        )
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
