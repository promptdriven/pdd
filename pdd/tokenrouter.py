"""Deterministic TokenRouter model and protocol routing metadata.

TokenRouter's live catalog changes independently of PDD releases.  PDD therefore
ships the reviewed intersection below and uses the live catalog only when a
maintainer deliberately refreshes this snapshot, never during inference.
"""

from __future__ import annotations

from typing import Final


TOKENROUTER_PROVIDER: Final = "TokenRouter"
TOKENROUTER_API_KEY_ENV: Final = "TOKENROUTER_API_KEY"
TOKENROUTER_BASE_URL: Final = "https://api.tokenrouter.com/v1"
TOKENROUTER_ANTHROPIC_MESSAGES_URL: Final = (
    f"{TOKENROUTER_BASE_URL}/messages"
)
TOKENROUTER_CATALOG_SNAPSHOT_DATE: Final = "2026-07-24"

# Exact TokenRouter model id -> reviewed endpoint type.  This is the intersection
# of TokenRouter's public text-model pricing catalog and PDD's supported model
# catalog on TOKENROUTER_CATALOG_SNAPSHOT_DATE.  Image/video/audio-only models
# and models that PDD does not otherwise support are intentionally absent.
TOKENROUTER_MODEL_ENDPOINTS: Final[dict[str, str]] = {
    "anthropic/claude-haiku-4.5": "anthropic-compatible",
    "anthropic/claude-opus-4.5": "anthropic-compatible",
    "anthropic/claude-opus-4.6": "anthropic-compatible",
    "anthropic/claude-opus-4.7": "anthropic",
    "anthropic/claude-opus-4.8": "anthropic",
    "anthropic/claude-sonnet-4": "anthropic-compatible",
    "anthropic/claude-sonnet-4.5": "anthropic-compatible",
    "anthropic/claude-sonnet-4.6": "anthropic-compatible",
    "deepseek/deepseek-v3.2": "openai",
    "google/gemini-3-flash-preview": "gemini",
    "google/gemini-3.1-pro-preview": "gemini",
    "google/gemini-3.5-flash": "gemini",
    "google/gemini-3.5-flash-lite": "gemini",
    "google/gemini-3.6-flash": "gemini",
    "minimax/minimax-m2.1": "openai",
    "minimax/minimax-m2.5": "openai",
    "moonshotai/kimi-k2.5": "openai",
    "moonshotai/kimi-k2.6": "openai",
    "openai/gpt-5.2": "openai",
    "openai/gpt-5.3-codex": "openai-response",
    "openai/gpt-5.4": "openai-response",
    "openai/gpt-5.4-mini": "openai",
    "openai/gpt-5.5": "openai-response",
    "openai/gpt-5-mini": "openai",
    "openai/gpt-5.6-sol": "openai-response",
    "qwen/qwen3-coder-next": "openai",
    "x-ai/grok-4.1-fast": "openai",
    "xiaomi/mimo-v2.5-pro": "openai",
    "z-ai/glm-4.6": "openai",
    "z-ai/glm-4.7": "openai",
    "z-ai/glm-5": "openai",
    "z-ai/glm-5-turbo": "openai",
    "z-ai/glm-5.1": "openai",
    "z-ai/glm-5.2": "openai",
}


def tokenrouter_litellm_model(model_id: str, endpoint_type: str) -> str:
    """Return the LiteLLM model string for an explicit TokenRouter protocol."""
    if endpoint_type == "openai":
        return f"openai/{model_id}"
    if endpoint_type == "openai-response":
        return f"openai/responses/{model_id}"
    if endpoint_type in {"anthropic", "anthropic-compatible"}:
        return f"anthropic/{model_id}"
    if endpoint_type == "gemini":
        return f"gemini/{model_id}"
    raise ValueError(
        f"Unsupported TokenRouter endpoint type {endpoint_type!r} for {model_id!r}"
    )


def tokenrouter_catalog_models() -> set[str]:
    """Return the exact LiteLLM model strings expected in the packaged CSV."""
    return {
        tokenrouter_litellm_model(model_id, endpoint_type)
        for model_id, endpoint_type in TOKENROUTER_MODEL_ENDPOINTS.items()
    }


def tokenrouter_litellm_base_url(provider: str, model: str, base_url: str) -> str:
    """Return the protocol-correct URL for a catalog row.

    LiteLLM appends ``/v1/messages`` to Anthropic base URLs.  TokenRouter's
    canonical base already ends in ``/v1``, so passing it through unchanged
    would incorrectly produce ``/v1/v1/messages``.  Supplying the complete
    messages URL prevents that suffix duplication.
    """
    if (
        str(provider).strip().casefold() == TOKENROUTER_PROVIDER.casefold()
        and str(model).startswith("anthropic/")
        and str(base_url).rstrip("/") == TOKENROUTER_BASE_URL
    ):
        return TOKENROUTER_ANTHROPIC_MESSAGES_URL
    return base_url
