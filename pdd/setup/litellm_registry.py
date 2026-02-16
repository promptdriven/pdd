"""
pdd/setup/litellm_registry.py

Wraps litellm's bundled model registry to provide provider search, model
browsing, and API key env var lookup.  Uses only local data — no network calls.
"""
from __future__ import annotations

import logging
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------


@dataclass
class ProviderInfo:
    """Summary information about an LLM provider."""

    name: str  # litellm provider ID, e.g. "anthropic"
    display_name: str  # human-friendly, e.g. "Anthropic"
    api_key_env_var: Optional[str]  # e.g. "ANTHROPIC_API_KEY"
    model_count: int  # number of chat models available
    sample_models: List[str] = field(default_factory=list)  # up to 3 names


@dataclass
class ModelInfo:
    """Metadata for a single LLM model from litellm's registry."""

    name: str  # short display name, e.g. "claude-opus-4-5"
    litellm_id: str  # full ID for litellm.completion()
    input_cost_per_million: float  # USD per 1M input tokens
    output_cost_per_million: float  # USD per 1M output tokens
    max_input_tokens: Optional[int] = None
    max_output_tokens: Optional[int] = None
    supports_vision: bool = False
    supports_function_calling: bool = False


# ---------------------------------------------------------------------------
# Static mappings
# ---------------------------------------------------------------------------

PROVIDER_API_KEY_MAP: Dict[str, str] = {
    "openai": "OPENAI_API_KEY",
    "anthropic": "ANTHROPIC_API_KEY",
    "gemini": "GEMINI_API_KEY",
    "vertex_ai": "VERTEX_CREDENTIALS",
    "groq": "GROQ_API_KEY",
    "mistral": "MISTRAL_API_KEY",
    "deepseek": "DEEPSEEK_API_KEY",
    "fireworks_ai": "FIREWORKS_API_KEY",
    "together_ai": "TOGETHERAI_API_KEY",
    "perplexity": "PERPLEXITYAI_API_KEY",
    "cohere": "COHERE_API_KEY",
    "cohere_chat": "COHERE_API_KEY",
    "replicate": "REPLICATE_API_KEY",
    "xai": "XAI_API_KEY",
    "deepinfra": "DEEPINFRA_API_KEY",
    "cerebras": "CEREBRAS_API_KEY",
    "ai21": "AI21_API_KEY",
    "bedrock": "AWS_ACCESS_KEY_ID",
    "azure": "AZURE_API_KEY",
    "azure_ai": "AZURE_AI_API_KEY",
    "openrouter": "OPENROUTER_API_KEY",
    "huggingface": "HUGGINGFACE_API_KEY",
    "databricks": "DATABRICKS_API_KEY",
    "cloudflare": "CLOUDFLARE_API_KEY",
    "novita": "NOVITA_API_KEY",
    "sambanova": "SAMBANOVA_API_KEY",
    "watsonx": "WATSONX_API_KEY",
}

PROVIDER_DISPLAY_NAMES: Dict[str, str] = {
    "openai": "OpenAI",
    "anthropic": "Anthropic",
    "gemini": "Google Gemini",
    "vertex_ai": "Google Vertex AI",
    "groq": "Groq",
    "mistral": "Mistral AI",
    "deepseek": "DeepSeek",
    "fireworks_ai": "Fireworks AI",
    "together_ai": "Together AI",
    "perplexity": "Perplexity",
    "cohere": "Cohere",
    "cohere_chat": "Cohere Chat",
    "replicate": "Replicate",
    "xai": "xAI",
    "deepinfra": "DeepInfra",
    "cerebras": "Cerebras",
    "ai21": "AI21",
    "bedrock": "AWS Bedrock",
    "azure": "Azure OpenAI",
    "azure_ai": "Azure AI",
    "openrouter": "OpenRouter",
    "huggingface": "Hugging Face",
    "databricks": "Databricks",
    "cloudflare": "Cloudflare Workers AI",
    "novita": "Novita AI",
    "sambanova": "SambaNova",
    "watsonx": "IBM watsonx",
}

# Curated list of major cloud providers shown by default.
_TOP_PROVIDER_IDS = [
    "openai",
    "anthropic",
    "gemini",
    "fireworks_ai",
    "mistral",
    "xai",
    "groq",
    "deepseek",
    "together_ai",
    "openrouter",
]


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------


def _get_display_name(provider: str) -> str:
    """Return the human-friendly name for *provider*, with a title-case fallback."""
    return PROVIDER_DISPLAY_NAMES.get(provider, provider.replace("_", " ").title())


def _collect_chat_models_for_provider(provider: str) -> Dict[str, dict]:
    """Return ``{model_id: cost_entry}`` for all chat models belonging to *provider*.

    Handles the ``vertex_ai`` sub-provider convention by matching any
    ``litellm_provider`` that starts with *provider*.

    Falls back to scanning ``litellm.model_cost`` directly when
    ``models_by_provider`` entries are missing from ``model_cost``.
    """
    import litellm  # local import — guarded by is_litellm_available()

    result: Dict[str, dict] = {}

    # Strategy 1: use models_by_provider set, then look up cost data.
    model_names: Set[str] = set()
    if provider in litellm.models_by_provider:
        model_names = set(litellm.models_by_provider[provider])

    for name in model_names:
        entry = litellm.model_cost.get(name)
        if entry and entry.get("mode") == "chat":
            result[name] = entry

    # Strategy 2 (fallback): scan model_cost for provider match.
    # Needed for together_ai and vertex_ai sub-providers.
    for model_id, entry in litellm.model_cost.items():
        if model_id in result:
            continue
        lp = entry.get("litellm_provider", "")
        if lp == provider or lp.startswith(f"{provider}-"):
            if entry.get("mode") == "chat":
                result[model_id] = entry

    return result


def _entry_to_model_info(model_id: str, entry: dict) -> ModelInfo:
    """Convert a ``litellm.model_cost`` entry into a :class:`ModelInfo`."""
    input_per_token = entry.get("input_cost_per_token") or 0
    output_per_token = entry.get("output_cost_per_token") or 0
    return ModelInfo(
        name=model_id.split("/")[-1] if "/" in model_id else model_id,
        litellm_id=model_id,
        input_cost_per_million=round(input_per_token * 1_000_000, 4),
        output_cost_per_million=round(output_per_token * 1_000_000, 4),
        max_input_tokens=entry.get("max_input_tokens"),
        max_output_tokens=entry.get("max_output_tokens"),
        supports_vision=bool(entry.get("supports_vision")),
        supports_function_calling=bool(entry.get("supports_function_calling")),
    )


def _build_provider_info(provider: str) -> Optional[ProviderInfo]:
    """Build a :class:`ProviderInfo` for *provider*, or ``None`` if it has no chat models."""
    chat_models = _collect_chat_models_for_provider(provider)
    if not chat_models:
        return None
    sample = sorted(chat_models.keys())[:3]
    return ProviderInfo(
        name=provider,
        display_name=_get_display_name(provider),
        api_key_env_var=PROVIDER_API_KEY_MAP.get(provider),
        model_count=len(chat_models),
        sample_models=sample,
    )


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def is_litellm_available() -> bool:
    """Return ``True`` if litellm is importable and has model data."""
    try:
        import litellm

        return bool(litellm.model_cost)
    except Exception:
        return False


def get_api_key_env_var(provider: str) -> Optional[str]:
    """Return the API key environment variable name for *provider*.

    Returns ``None`` if the provider is not in the known mapping.
    """
    return PROVIDER_API_KEY_MAP.get(provider)


def get_top_providers() -> List[ProviderInfo]:
    """Return a curated list of major cloud providers, sorted by the curated order.

    Falls back to all providers sorted by model count if the curated list
    yields fewer than 3 results (e.g. litellm data changed).
    """
    if not is_litellm_available():
        return []

    result: List[ProviderInfo] = []
    for pid in _TOP_PROVIDER_IDS:
        info = _build_provider_info(pid)
        if info:
            result.append(info)

    if len(result) < 3:
        return get_all_providers()[:10]
    return result


def get_all_providers() -> List[ProviderInfo]:
    """Return all providers that have at least one chat model.

    Sorted by model count descending.
    """
    if not is_litellm_available():
        return []

    import litellm

    seen: Set[str] = set()
    infos: List[ProviderInfo] = []

    # Collect from models_by_provider keys
    for provider in litellm.models_by_provider:
        if provider in seen:
            continue
        seen.add(provider)
        info = _build_provider_info(provider)
        if info:
            infos.append(info)

    # Also scan model_cost for providers not in models_by_provider
    for entry in litellm.model_cost.values():
        lp = entry.get("litellm_provider", "")
        # Normalise vertex_ai sub-providers
        base = lp.split("-")[0] if "-" in lp else lp
        if base and base not in seen:
            seen.add(base)
            info = _build_provider_info(base)
            if info:
                infos.append(info)

    infos.sort(key=lambda i: i.model_count, reverse=True)
    return infos


def search_providers(query: str) -> List[ProviderInfo]:
    """Return providers whose name or display name contains *query* (case-insensitive).

    Sorted by model count descending.
    """
    if not query:
        return get_all_providers()

    all_providers = get_all_providers()
    q = query.lower()
    return [
        p
        for p in all_providers
        if q in p.name.lower() or q in p.display_name.lower()
    ]


def get_models_for_provider(provider: str) -> List[ModelInfo]:
    """Return chat-mode models for *provider*, sorted by name.

    Converts per-token costs to per-million-token costs.
    """
    if not is_litellm_available():
        return []

    chat_models = _collect_chat_models_for_provider(provider)
    result = [
        _entry_to_model_info(model_id, entry)
        for model_id, entry in chat_models.items()
    ]
    result.sort(key=lambda m: m.name)
    return result
