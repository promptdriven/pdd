"""
Token counting and cost estimation utilities.

Uses litellm for model-aware token counting and context window lookup.
Falls back to tiktoken for unknown models.
Loads model pricing from .pdd/llm_model.csv.
"""

from __future__ import annotations

import csv
import logging
import threading
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, Optional, Dict, NamedTuple

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
    Run a litellm call in a daemon worker thread with a hard timeout.

    Raises TimeoutError if the call doesn't finish in time, so callers can
    treat hangs the same way they treat exceptions.

    The worker is a *daemon* thread on purpose. litellm's provider-detection
    can misroute a model into a provider that performs a blocking device-code
    OAuth poll (e.g. ``chatgpt``/``github_copilot``) which never returns
    without human interaction. A non-daemon worker — such as the ones spawned
    by ``ThreadPoolExecutor`` — would keep the interpreter alive at exit
    (Python's atexit handler joins all pool workers), wedging the whole
    process. This was observed hanging an otherwise-passing pytest run in CI
    for ~10 min until a chunk timeout killed it. A daemon thread is abandoned
    cleanly and dies with the process instead.
    """
    # Resolve the timeout dynamically so tests (and operators) can tune
    # ``_LITELLM_CALL_TIMEOUT_SEC`` at runtime.
    effective_timeout = timeout if timeout is not None else _LITELLM_CALL_TIMEOUT_SEC
    result_holder: list[Any] = [None]
    error_holder: list[Any] = [None]

    def _run() -> None:
        try:
            result_holder[0] = fn(*args, **kwargs)
        except Exception as exc:  # noqa: BLE001 - re-raised on the calling thread
            error_holder[0] = exc

    worker = threading.Thread(target=_run, name="litellm-probe", daemon=True)
    worker.start()
    worker.join(timeout=effective_timeout)

    if worker.is_alive():
        raise TimeoutError(
            f"litellm call {getattr(fn, '__qualname__', repr(fn))} timed out"
            f" after {effective_timeout:.1f}s (likely provider-detection hang)"
        )
    if error_holder[0] is not None:
        raise error_holder[0]
    return result_holder[0]


@dataclass
class CostEstimate:
    """Cost estimation result."""

    input_cost: float
    model: str
    tokens: int
    cost_per_million: float
    currency: str = "USD"
    output_cost: float = 0.0
    total_cost: Optional[float] = None
    matched_model: Optional[str] = None
    input_tokens: Optional[int] = None
    output_tokens: Optional[int] = None
    input_cost_per_million: Optional[float] = None
    output_cost_per_million: Optional[float] = None

    def __post_init__(self) -> None:
        """Populate compatibility/default fields."""
        if self.total_cost is None:
            self.total_cost = self.input_cost + self.output_cost
        if self.matched_model is None:
            self.matched_model = self.model
        if self.input_tokens is None:
            self.input_tokens = self.tokens
        if self.output_tokens is None:
            self.output_tokens = 0
        if self.input_cost_per_million is None:
            self.input_cost_per_million = self.cost_per_million

    def to_dict(self) -> Dict:
        """Serialize to dict."""
        return {
            "input_cost": round(self.input_cost, 6),
            "model": self.model,
            "tokens": self.tokens,
            "cost_per_million": self.cost_per_million,
            "currency": self.currency,
            "output_cost": round(self.output_cost, 6),
            "total_cost": round(self.total_cost, 6) if self.total_cost is not None else None,
            "matched_model": self.matched_model,
            "input_tokens": self.input_tokens,
            "output_tokens": self.output_tokens,
            "input_cost_per_million": self.input_cost_per_million,
            "output_cost_per_million": self.output_cost_per_million,
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


class ModelPricing(NamedTuple):
    """Per-million-token input and output pricing for a model."""

    input_cost_per_million: float
    output_cost_per_million: float


@lru_cache(maxsize=1)
def _load_model_pricing(csv_path: str) -> Dict[str, ModelPricing]:
    """Load model pricing from CSV (cached)."""
    pricing: Dict[str, ModelPricing] = {}

    try:
        with open(csv_path, "r") as f:
            reader = csv.DictReader(f)
            for row in reader:
                model = row.get("model", "")
                input_cost = row.get("input")
                output_cost = row.get("output")
                if not model or input_cost in (None, "") or output_cost in (None, ""):
                    continue
                try:
                    pricing[model] = ModelPricing(
                        float(input_cost),
                        float(output_cost),
                    )
                except (TypeError, ValueError):
                    continue
    except (FileNotFoundError, PermissionError):
        pass

    return pricing


def _find_model_pricing(
    model: str,
    pricing: Dict[str, ModelPricing],
) -> Optional[tuple[str, ModelPricing]]:
    """Find valid pricing for model using exact, then conservative partial match."""
    if model in pricing:
        return model, pricing[model]

    model_lower = model.lower()
    for csv_model, rates in pricing.items():
        csv_model_lower = csv_model.lower()
        if model_lower in csv_model_lower or csv_model_lower in model_lower:
            return csv_model, rates

    return None


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

    match = _find_model_pricing(model, pricing)
    if match is None:
        return None
    matched_model, rates = match

    # Pricing is expressed per million tokens
    input_cost = (token_count / 1_000_000) * rates.input_cost_per_million

    return CostEstimate(
        input_cost=input_cost,
        model=matched_model,
        matched_model=matched_model,
        tokens=token_count,
        input_tokens=token_count,
        output_tokens=0,
        cost_per_million=rates.input_cost_per_million,
        input_cost_per_million=rates.input_cost_per_million,
        output_cost_per_million=rates.output_cost_per_million,
    )


def estimate_completion_cost(
    input_tokens: int,
    predicted_output_tokens: int,
    model: str,
    pricing_csv: Optional[Path] = None,
) -> Optional[CostEstimate]:
    """
    Estimate combined input and predicted output cost for a completion.

    Returns None when pricing is unavailable or the model has no valid pricing
    row. Unknown models must not borrow another model's price.
    """
    if pricing_csv is None or not pricing_csv.exists():
        return None

    pricing = _load_model_pricing(str(pricing_csv))
    if not pricing:
        return None

    match = _find_model_pricing(model, pricing)
    if match is None:
        return None
    matched_model, rates = match

    input_cost = (input_tokens / 1_000_000) * rates.input_cost_per_million
    output_cost = (
        predicted_output_tokens / 1_000_000
    ) * rates.output_cost_per_million
    total_cost = input_cost + output_cost

    return CostEstimate(
        input_cost=input_cost,
        output_cost=output_cost,
        total_cost=total_cost,
        model=matched_model,
        matched_model=matched_model,
        tokens=input_tokens,
        input_tokens=input_tokens,
        output_tokens=predicted_output_tokens,
        cost_per_million=rates.input_cost_per_million,
        input_cost_per_million=rates.input_cost_per_million,
        output_cost_per_million=rates.output_cost_per_million,
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
