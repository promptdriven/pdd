#!/usr/bin/env python3
"""
scripts/generate_model_catalog.py

Regenerates pdd/data/llm_model.csv from LiteLLM's bundled model registry.

Usage:
    python scripts/generate_model_catalog.py [--output PATH]

The script pulls from litellm.model_cost (local data, no network calls) and:
  - Filters to chat-mode models only
  - Skips deprecated models
  - Skips placeholder/tier entries (e.g. together-ai-4.1b-8b)
  - Converts per-token costs to per-million-token costs
  - Looks up display provider names and API key env var names
  - Applies curated ELO scores for known models; skips models below ELO_CUTOFF
  - Infers structured_output, reasoning_type, max_reasoning_tokens
  - Sorts by ELO descending, then model name ascending

Re-run this script whenever you update the litellm package to pick up new models.
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from collections import defaultdict
from datetime import date
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# ELO cutoff — models below this score are excluded from the catalog.
# ---------------------------------------------------------------------------
ELO_CUTOFF = 1300
MAX_COST_PER_MTOK = 100.0  # Sanity cap — drop rows with absurd pricing (LiteLLM bugs)

# ---------------------------------------------------------------------------
# ELO scores — canonical base model names mapped to coding arena ELO.
# All known models are listed here; ELO_CUTOFF controls which make the CSV.
# Keys are normalized base names (as produced by _extract_base_model).

#   Scores sourced from LM Arena *coding* leaderboard (Feb 2026):
#   https://openlm.ai/chatbot-arena/  (Coding column)
#   You should update these values every so often. 
# ---------------------------------------------------------------------------
ELO_SCORES: Dict[str, int] = {
    # -----------------------------------------------------------------------
    # Source: LMArena CODE Arena leaderboard, scraped Feb 22, 2026.
    #   - Scores marked [CODE] are directly from the Code Arena.
    #   - Scores marked [EST]  are estimated from Text Arena scores,
    #     discounted by ~40-60 pts based on observed Text→Code deltas
    #     for similar-tier models.
    # -----------------------------------------------------------------------

    # -----------------------------------------------------------------------
    # Anthropic Claude
    # -----------------------------------------------------------------------
    "claude-opus-4-6": 1561,            # [CODE] #1
    "claude-opus-4-5": 1469,            # [CODE] #6
    "claude-opus-4-1": 1389,            # [CODE] #20
    "claude-opus-4": 1370,              # [EST]
    "claude-sonnet-4-6": 1524,          # [CODE] #3
    "claude-sonnet-4-5": 1390,          # [CODE] #19
    "claude-sonnet-4": 1350,            # [EST]
    "claude-3-7-sonnet": 1310,          # [EST]
    "claude-3-5-sonnet-20241022": 1310, # [EST]
    "claude-3-5-sonnet": 1310,          # [EST]
    "claude-haiku-4-5": 1303,           # [CODE]
    # Dot-separated aliases
    "claude-opus-4.6": 1561,
    "claude-opus-4.5": 1469,
    "claude-opus-4.1": 1389,
    "claude-sonnet-4.6": 1524,
    "claude-sonnet-4.5": 1390,
    "claude-haiku-4.5": 1303,
    "claude-3.5-sonnet": 1310,
    "claude-3.7-sonnet": 1310,
    # Alternate naming
    "claude-4-opus": 1370,
    "claude-4-sonnet": 1350,
    "claude-opus-41": 1389,            # GitHub Copilot naming for claude-opus-4-1
    "claude-opus-4.6-fast": 1561,      # GitHub Copilot fast variant

    # -----------------------------------------------------------------------
    # OpenAI — GPT-5 family
    # -----------------------------------------------------------------------
    "gpt-5.2": 1395,                   # [CODE] #17 (default reasoning)
    "gpt-5.2-codex": 1336,             # [CODE] #22
    "gpt-5.1": 1348,                   # [CODE] (default)
    "gpt-5.1-codex": 1348,             # Codex variant
    "gpt-5.1-codex-mini": 1243,        # [CODE] #31
    "gpt-5.1-codex-max": 1389,         # [EST] same as gpt-5.1-medium
    "gpt-5.3-codex": 1336,             # [EST] assume similar to gpt-5.2-codex
    "gpt-5": 1393,                     # [CODE] #18 as gpt-5-medium
    "gpt-5-mini": 1310,                # [EST]
    "gpt-5-nano": 1300,                # [EST] smallest GPT-5 variant
    # OpenAI — GPT-4.x
    "gpt-4.5": 1380,                   # [EST]
    "gpt-4.1": 1355,                   # [EST]
    "gpt-4.1-mini": 1310,              # [EST]
    "gpt-4o": 1300,                    # [EST]
    # OpenAI — o-series
    "o3": 1370,                        # [EST]
    "o4-mini": 1330,                   # [EST]
    "o3-mini": 1310,                   # [EST]
    "o1": 1340,                        # [EST]
    "o1-mini": 1315,                   # [EST]

    # -----------------------------------------------------------------------
    # Google Gemini
    # -----------------------------------------------------------------------
    "gemini-3.1-pro": 1461,             # [CODE] #7
    "gemini-3.1-pro-preview": 1461,
    "gemini-3-pro": 1444,              # [CODE] #9
    "gemini-3-pro-preview": 1444,
    "gemini-3-flash": 1440,            # [CODE] #12
    "gemini-3-flash-preview": 1440,
    "gemini-2.5-pro": 1206,            # [CODE] huge Text→Code drop
    "gemini-2.5-flash": 1300,          # [EST]

    # -----------------------------------------------------------------------
    # DeepSeek
    # -----------------------------------------------------------------------
    "deepseek-v3.2": 1310,             # [CODE]
    "deepseek-v3.1": 1300,             # [EST]
    "deepseek-r1-0528": 1370,          # [EST]
    "deepseek-r1": 1340,               # [EST]
    "deepseek-reasoner": 1340,         # alias for deepseek-r1
    "deepseek-v3-0324": 1300,          # [EST]
    "deepseek-v3": 1300,               # [EST]
    "deepseek-chat": 1300,             # alias

    # -----------------------------------------------------------------------
    # xAI / Grok
    # -----------------------------------------------------------------------
    "grok-4-0709": 1467,               # Strong latest Grok model (Jul 2026 release)
    "grok-4.1-thinking": 1402,         # [EST]
    "grok-4.1": 1380,                  # [EST]
    "grok-4-1-fast-reasoning": 1402,   # Fast reasoning variant
    "grok-4-1-fast": 1380,             # Fast non-reasoning variant
    "grok-4-1-fast-non-reasoning": 1350,
    "grok-4": 1350,                    # [EST]
    "grok-4-fast": 1300,               # [EST]
    "grok-4-fast-reasoning": 1350,     # [EST]
    "grok-4-fast-non-reasoning": 1300, # [EST]
    "grok-3": 1200,                    # [EST]

    # -----------------------------------------------------------------------
    # Mistral
    # -----------------------------------------------------------------------
    "mistral-large": 1223,             # [CODE]
    "mistral-large-3": 1223,           # [CODE]

    # -----------------------------------------------------------------------
    # Moonshot / Kimi
    # -----------------------------------------------------------------------
    "kimi-k2.5": 1439,                 # [CODE] #13
    "kimi-k2p5": 1439,                 # Fireworks alias for kimi-k2.5
    "kimi-k2.5-instant": 1424,         # [CODE] #14
    "kimi-k2-thinking": 1333,          # [CODE]
    "kimi-k2-instruct": 1310,          # [EST]
    "kimi-k2-0905": 1310,              # [EST]
    "kimi-k2-0711": 1310,              # [EST]

    # -----------------------------------------------------------------------
    # Qwen / Alibaba
    # -----------------------------------------------------------------------
    "qwen3-coder-next": 1310,           # [EST] next-gen coder variant
    "qwen3-coder-480b-a35b": 1280,     # [CODE]
    "qwen3-235b-a22b-instruct-2507": 1280,  # [EST]
    "qwen3-235b-a22b-thinking-2507": 1300,  # [EST]
    "qwen3-max": 1310,                 # [EST]
    "qwen3-235b-a22b": 1280,           # [EST]
    "qwen3-32b": 1260,                 # [EST]

    # -----------------------------------------------------------------------
    # GLM (Zhipu AI / ZAI)
    # -----------------------------------------------------------------------
    "glm-5": 1456,                     # [CODE] #8
    "glm-4.7": 1440,                   # [CODE] #11
    "glm-4.6": 1357,                   # [CODE]

    # -----------------------------------------------------------------------
    # Minimax
    # -----------------------------------------------------------------------
    "minimax-m2.5": 1443,              # [CODE] #10
    "minimax-m2.1": 1402,              # [CODE] #15
    "minimax-m2": 1313,                # [CODE]

    # -----------------------------------------------------------------------
    # MiMo (Xiaomi)
    # -----------------------------------------------------------------------
    "mimo-v2-flash": 1340,             # [CODE]
}

# ---------------------------------------------------------------------------
# Price overrides — (input_per_mtok, output_per_mtok).
# Use this to correct known LiteLLM pricing bugs or supply missing prices.
# ---------------------------------------------------------------------------
PRICE_OVERRIDES: Dict[str, Tuple[float, float]] = {
    # Hyperbolic uses unified pricing; LiteLLM has V3 price for R1-0528
    "hyperbolic/deepseek-ai/DeepSeek-R1-0528": (3.0, 3.0),
    # W&B prices are off by ~100,000x in LiteLLM (github.com/BerriAI/litellm/issues/17417)
    "wandb/Qwen/Qwen3-235B-A22B-Instruct-2507": (0.10, 0.10),
    "wandb/Qwen/Qwen3-235B-A22B-Thinking-2507": (0.10, 0.10),
    "wandb/deepseek-ai/DeepSeek-R1-0528": (1.35, 5.40),
    "wandb/deepseek-ai/DeepSeek-V3.1": (0.55, 1.65),
    "wandb/Qwen/Qwen3-Coder-480B-A35B-Instruct": (1.0, 1.5),
    # Vercel has long-context rate ($2.50) instead of standard ($1.25) for Gemini 2.5 Pro
    "vercel_ai_gateway/google/gemini-2.5-pro": (1.25, 10.0),
    # Hyperbolic unified pricing — LiteLLM has wrong values for R1 and V3
    "hyperbolic/deepseek-ai/DeepSeek-R1": (2.0, 2.0),
    "hyperbolic/deepseek-ai/DeepSeek-V3": (0.25, 0.25),
    # Heroku reports $0 in LiteLLM but actually charges per-token
    "heroku/claude-4-sonnet": (3.0, 15.0),
    "heroku/claude-3-5-sonnet-latest": (3.0, 15.0),
    "heroku/claude-3-7-sonnet": (3.0, 15.0),
}

# ---------------------------------------------------------------------------
# Provider table — maps litellm provider ID to (display name, API key env var).
# ---------------------------------------------------------------------------
PROVIDERS: Dict[str, Tuple[str, str]] = {
    "openai":             ("OpenAI",                    "OPENAI_API_KEY"),
    "anthropic":          ("Anthropic",                 "ANTHROPIC_API_KEY"),
    "gemini":             ("Google Gemini",             "GEMINI_API_KEY"),
    "vertex_ai":          ("Google Vertex AI",          "GOOGLE_APPLICATION_CREDENTIALS|VERTEXAI_PROJECT|VERTEXAI_LOCATION"),
    "xai":                ("xAI",                       "XAI_API_KEY"),
    "deepseek":           ("DeepSeek",                  "DEEPSEEK_API_KEY"),
    "mistral":            ("Mistral AI",                "MISTRAL_API_KEY"),
    "cohere":             ("Cohere",                    "COHERE_API_KEY"),
    "cohere_chat":        ("Cohere",                    "COHERE_API_KEY"),
    "moonshot":           ("Moonshot AI",               "MOONSHOT_API_KEY"),
    "groq":               ("Groq",                      "GROQ_API_KEY"),
    "fireworks_ai":       ("Fireworks AI",              "FIREWORKS_AI_API_KEY"),
    "together_ai":        ("Together AI",               "TOGETHERAI_API_KEY"),
    "perplexity":         ("Perplexity",                "PERPLEXITYAI_API_KEY"),
    "openrouter":         ("OpenRouter",                "OPENROUTER_API_KEY"),
    "deepinfra":          ("DeepInfra",                 "DEEPINFRA_API_KEY"),
    "cerebras":           ("Cerebras",                  "CEREBRAS_API_KEY"),
    "replicate":          ("Replicate",                 "REPLICATE_API_KEY"),
    "anyscale":           ("Anyscale",                  "ANYSCALE_API_KEY"),
    "novita":             ("Novita AI",                 "NOVITA_API_KEY"),
    "sambanova":          ("SambaNova",                 "SAMBANOVA_API_KEY"),
    "nvidia_nim":         ("NVIDIA NIM",                "NVIDIA_NIM_API_KEY"),
    "bedrock":            ("AWS Bedrock",               "AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME"),
    "bedrock_converse":   ("AWS Bedrock",               "AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME"),
    "sagemaker":          ("AWS SageMaker",             "AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME"),
    "azure":              ("Azure OpenAI",              "AZURE_API_KEY|AZURE_API_BASE|AZURE_API_VERSION"),
    "azure_ai":           ("Azure AI",                  "AZURE_AI_API_KEY"),
    "databricks":         ("Databricks",                "DATABRICKS_API_KEY"),
    "watsonx":            ("IBM watsonx",               "WATSONX_APIKEY"),
    "cloudflare":         ("Cloudflare Workers AI",     "CLOUDFLARE_API_KEY"),
    "huggingface":        ("Hugging Face",              "HF_TOKEN"),
    "ai21":               ("AI21",                      "AI21_API_KEY"),
    "nlp_cloud":          ("NLP Cloud",                 "NLP_CLOUD_API_KEY"),
    "aleph_alpha":        ("Aleph Alpha",               "ALEPHALPHA_API_KEY"),
    "predibase":          ("Predibase",                 "PREDIBASE_API_KEY"),
    "friendliai":         ("FriendliAI",                "FRIENDLI_TOKEN"),
    "github":             ("GitHub Models",             "GITHUB_API_KEY"),
    "github_copilot":     ("Github Copilot",            ""),
    "clarifai":           ("Clarifai",                  "CLARIFAI_PAT"),
    "voyage":             ("Voyage",                    "VOYAGE_API_KEY"),
    "codestral":          ("Codestral",                 "CODESTRAL_API_KEY"),
    "infinity":           ("Infinity",                  "INFINITY_API_KEY"),
    "nscale":             ("Nscale",                    "NSCALE_API_KEY"),
    "hyperbolic":         ("Hyperbolic",                "HYPERBOLIC_API_KEY"),
    "lambda_ai":          ("Lambda AI",                 "LAMBDA_API_KEY"),
    "featherless_ai":     ("Featherless AI",            "FEATHERLESS_API_KEY"),
    "gmi":                ("GMI Cloud",                 "GMI_API_KEY"),
    "wandb":              ("W&B Inference",             "WANDB_API_KEY"),
    "vercel_ai_gateway":  ("Vercel AI Gateway",         "VERCEL_AI_GATEWAY_API_KEY"),
    "minimax":            ("MiniMax",                    "MINIMAX_API_KEY"),
    "ollama":             ("Ollama",                    ""),
    "ollama_chat":        ("Ollama",                    ""),
    "lm_studio":          ("LM Studio",                 ""),
}

# Anthropic provider IDs — these use "budget" reasoning
_ANTHROPIC_PROVIDERS = {"anthropic", "azure_ai"}  # azure_ai hosts Claude models too

# Model name patterns that signal reasoning (for providers not in the sets above)
_EFFORT_PATTERNS = re.compile(
    r"o1|o3|o4|gemini.*thinking|deepseek.r1|deepseek.reasoner|"
    r"qwen.*thinking|kimi.*thinking|magistral|"
    r"gemini.*flash.*thinking",
    re.IGNORECASE,
)

# Placeholder tier entries in together_ai (not real model IDs)
_TIER_PATTERN = re.compile(r"^together-ai-[\d.]+b", re.IGNORECASE)

# Models we never want in the catalog (sample spec, image-only, etc.)
_SKIP_KEYS = {"sample_spec"}

# Regex matching dated preview model names (after provider prefix is stripped).
# Examples: gemini-2.5-flash-preview-04-17, gemini-2.5-pro-preview-06-05
_DATED_PREVIEW = re.compile(
    r"^(?P<base>gemini-[\d.]+-\w+)-preview-\d{2}-\d{2,4}$",
    re.IGNORECASE,
)

CSV_FIELDNAMES = [
    "provider", "model", "input", "output", "coding_arena_elo",
    "base_url", "api_key", "max_reasoning_tokens", "structured_output",
    "reasoning_type", "location",
]

# ---------------------------------------------------------------------------
# Regex patterns for _extract_base_model() — stripping provider/region/version
# ---------------------------------------------------------------------------

# Known provider prefixes (simple provider/rest format)
_SIMPLE_PREFIX_PROVIDERS = {
    "vertex_ai", "azure_ai", "openrouter", "deepinfra", "together_ai",
    "fireworks_ai", "vercel_ai_gateway", "github_copilot", "groq",
    "cerebras", "hyperbolic", "novita", "sambanova", "replicate",
    "lambda_ai", "nscale", "oci", "gmi", "wandb", "ovhcloud",
    "llamagate", "gradient_ai", "moonshot", "snowflake", "heroku",
    "publicai", "deepseek", "xai", "mistral", "gemini", "perplexity",
    "cohere", "cohere_chat", "meta_llama", "dashscope", "minimax",
}

# Bedrock region paths: us-east-1/, ap-northeast-1/, us-gov-west-1/, etc.
# Also handles commitment and invoke prefixes.
_BEDROCK_REGION_PATH = re.compile(
    r"^(?:[a-z]{2}-[a-z]+-\d+/)+"  # one or more region segments
    r"|^(?:\d+-month-commitment/)"
    r"|^(?:invoke/)",
    re.IGNORECASE,
)

# Azure sub-region paths: eu/, global/, global-standard/
_AZURE_REGION_PREFIX = re.compile(
    r"^(?:eu|global-standard|global|us)/",
    re.IGNORECASE,
)

# Bedrock cross-region inference prefixes on bare IDs: us., eu., apac., au., jp., global.
_BEDROCK_GEO_PREFIX = re.compile(
    r"^(?:us|eu|apac|ap|au|jp|global)\.",
    re.IGNORECASE,
)

# Vendor dot-namespace: anthropic., meta., moonshotai., deepseek., xai., etc.
# Used by Bedrock (anthropic.claude-*) and OCI (xai.grok-3, meta.llama-*)
_VENDOR_DOT_PREFIX = re.compile(
    r"^(?:anthropic|meta|amazon|cohere|ai21|mistral|moonshotai|deepseek|"
    r"qwen|minimax|nvidia|openai|google|writer|twelvelabs|zai|xai)\.",
    re.IGNORECASE,
)

# HuggingFace-style org namespaces used by deepinfra, together_ai, openrouter, etc.
_ORG_NAMESPACE = re.compile(
    r"^(?:deepseek-ai|deepseek|meta-llama|meta|anthropic|google|openai|"
    r"moonshotai|mistralai|qwen|Qwen|x-ai|xai|cohere|microsoft|"
    r"allenai|NousResearch|nvidia|MiniMaxAI|zai-org)/",
    re.IGNORECASE,
)

# Fireworks account path: accounts/fireworks/models/ (or any account)
_FIREWORKS_ACCOUNT = re.compile(
    r"^accounts/[^/]+/models/",
    re.IGNORECASE,
)

# Anthropic fast/us routing prefixes on bare IDs
_FAST_PREFIX = re.compile(r"^(?:fast/us/|fast/|us/)", re.IGNORECASE)

# Dated Anthropic model IDs: claude-opus-4-6-20260205, claude-sonnet-4-5-20250929, etc.
_DATED_ANTHROPIC = re.compile(
    r"^(?P<base>claude-[\w-]+)-\d{8}$",
    re.IGNORECASE,
)

# Bedrock region-specific model IDs (bare geo-prefix form: us., eu., apac., au., jp., ap.)
_BEDROCK_GEO_MODEL = re.compile(
    r"^(?:us|eu|apac|ap|au|jp)\.",
    re.IGNORECASE,
)

# Vertex AI @version suffix: @20241022, @default, @001, @latest
_VERTEX_VERSION = re.compile(r"@[\w.-]+$")

# Bedrock version suffix: -v1:0, -v2:0, :0
_BEDROCK_VERSION = re.compile(r"(?:-v\d+:\d+|:\d+)$")

# Special mapping for Bedrock deepseek after vendor prefix is stripped
# e.g. deepseek.v3.2 -> strips to "v3.2" or "v3-v1:0" -> "v3"
_BEDROCK_DEEPSEEK_REMAP: Dict[str, str] = {
    "v3": "deepseek-v3",
    "v3.2": "deepseek-v3",
    "r1": "deepseek-r1",
}

# Safe remainder patterns after a canonical prefix match.
# Only accept: empty, date suffixes (-20241022), version tags (-v1, -v2),
# preview/latest tags, or @version.
# This REJECTS things like -distill-*, -turbo, -mini, -fast.
_SAFE_REMAINDER = re.compile(
    r"^(?:"
    r"-\d{8}"           # -20241022 (8-digit date)
    r"|-v\d+"           # -v1, -v2
    r"|-preview"        # -preview
    r"|-latest"         # -latest
    r"|-instruct"       # -instruct (same weights, just instruction-tuned name)
    r"|-versatile"      # -versatile (Groq naming for same model)
    r"|-\d{4}(?:0[1-9]|1[0-2])\d{2}"  # -YYYYMMDD compact
    r")(?:$|[-@])",     # must be end-of-string or followed by another suffix
    re.IGNORECASE,
)


def _extract_base_model(model_id: str) -> Optional[str]:
    """
    Extract a canonical base model name from a litellm model ID by stripping
    provider prefixes, regions, vendor namespaces, and version suffixes.

    Returns a key matching ELO_SCORES if confident, or None if the model
    cannot be safely identified (conservative — prefers returning None over
    a wrong match).
    """
    s = model_id.strip()

    # Step 1: Strip known provider prefix
    slash_pos = s.find("/")
    if slash_pos > 0:
        prefix = s[:slash_pos]
        if prefix in _SIMPLE_PREFIX_PROVIDERS:
            s = s[slash_pos + 1:]
            # Azure AI and some providers also have region sub-paths (global/, etc.)
            s = _AZURE_REGION_PREFIX.sub("", s)
        elif prefix == "bedrock" or prefix == "bedrock_converse":
            s = s[slash_pos + 1:]
            # Strip region paths (may be multiple segments)
            while _BEDROCK_REGION_PATH.match(s):
                s = _BEDROCK_REGION_PATH.sub("", s, count=1)
        elif prefix == "azure":
            s = s[slash_pos + 1:]
            s = _AZURE_REGION_PREFIX.sub("", s)
        elif prefix == "openai":
            s = s[slash_pos + 1:]

    # Step 2: Strip fast/us routing prefixes (bare Anthropic IDs)
    s = _FAST_PREFIX.sub("", s)

    # Step 3: Strip Bedrock cross-region geo prefixes (us., eu., apac., etc.)
    s = _BEDROCK_GEO_PREFIX.sub("", s)

    # Step 4: Strip vendor dot-namespace (anthropic., meta., moonshotai., xai., etc.)
    # Only when there's no slash left (to avoid mangling org/model paths)
    if "/" not in s and "." in s:
        m = _VENDOR_DOT_PREFIX.match(s)
        if m:
            s = s[m.end():]

    # Step 5: Strip HuggingFace-style org namespace (deepseek-ai/, meta-llama/, etc.)
    s = _ORG_NAMESPACE.sub("", s)

    # Step 6: Strip Fireworks account path
    s = _FIREWORKS_ACCOUNT.sub("", s)

    # Step 7: Strip Vertex AI @version suffix
    s = _VERTEX_VERSION.sub("", s)

    # Step 8: Strip Bedrock version suffix (-v1:0, :0)
    s = _BEDROCK_VERSION.sub("", s)

    # Step 9: Lowercase for matching
    s = s.lower()

    # Step 10: Handle Bedrock deepseek special naming (vendor-stripped leftovers)
    if s in _BEDROCK_DEEPSEEK_REMAP:
        s = _BEDROCK_DEEPSEEK_REMAP[s]

    # Step 11: Strip trailing -maas suffix (Vertex AI model-as-a-service)
    if s.endswith("-maas"):
        s = s[:-5]

    # Step 12: Exact match
    if s in ELO_SCORES:
        return s

    # Step 13: Longest-prefix match against ELO_SCORES keys.
    # Sorted longest-first to prefer more specific matches
    # (e.g. "claude-opus-4-1" over "claude-opus-4").
    for key in sorted(ELO_SCORES, key=len, reverse=True):
        if s.startswith(key):
            remainder = s[len(key):]
            if not remainder:
                return key
            if _SAFE_REMAINDER.match(remainder):
                return key

    return None


def _get_provider_root(litellm_provider: str) -> str:
    """Return the root provider for compound provider strings like vertex_ai-anthropic_models."""
    return litellm_provider.split("-")[0].split("_models")[0]


# Regex matching region-specific Bedrock model IDs, e.g.:
#   bedrock/us-east-1/...   bedrock/eu-north-1/...
#   us.anthropic....        eu.anthropic....
_REGION_RE = re.compile(
    r"^(bedrock/[a-z]{2}-[a-z]+-\d+/|[a-z]{2}\.)"
)


def _has_region(model_id: str) -> bool:
    """Return True if model_id is pinned to a specific cloud region."""
    return bool(_REGION_RE.match(model_id))


def _infer_reasoning_type(model_id: str, litellm_provider: str, entry: dict) -> str:
    supports_reasoning = entry.get("supports_reasoning", False)
    if not supports_reasoning:
        return "none"
    root = _get_provider_root(litellm_provider)
    # Anthropic (and Azure AI hosting Claude) use "budget" reasoning tokens
    if root in _ANTHROPIC_PROVIDERS:
        return "budget"
    # All other providers use "effort" (low/medium/high string)
    return "effort"


def _infer_max_reasoning_tokens(model_id: str, litellm_provider: str, entry: dict) -> int:
    root = _get_provider_root(litellm_provider)
    if not entry.get("supports_reasoning", False):
        return 0
    if root in _ANTHROPIC_PROVIDERS:
        return 128000
    return 0


def _is_deprecated(entry: dict) -> bool:
    dep = entry.get("deprecation_date")
    if not dep or not isinstance(dep, str):
        return False
    try:
        dep_date = date.fromisoformat(dep)
        return dep_date <= date.today()
    except ValueError:
        return False


def _is_placeholder(model_id: str) -> bool:
    """Filter out non-usable placeholder entries."""
    if model_id in _SKIP_KEYS:
        return True
    if _TIER_PATTERN.match(model_id):
        return True
    return False


def _is_superseded_preview(model_id: str, all_model_ids: set) -> bool:
    """Return True if this is a dated Gemini preview whose stable GA version exists.

    Google routinely sunsets dated preview models (e.g. gemini-2.5-flash-preview-04-17)
    once the stable GA version (gemini-2.5-flash) is available, but litellm's registry
    often retains them without a deprecation_date.  We skip these to avoid catalog
    entries that fail at call time with a 404.

    The check is applied to both bare IDs (gemini-2.5-flash-preview-04-17) and
    provider-prefixed IDs (gemini/gemini-2.5-flash-preview-04-17) — we strip the
    provider prefix before matching.
    """
    # Strip simple provider prefix (e.g. "gemini/", "vertex_ai/")
    bare = model_id
    slash = bare.find("/")
    if slash > 0:
        bare = bare[slash + 1:]

    m = _DATED_PREVIEW.match(bare)
    if not m:
        return False

    ga_name = m.group("base")  # e.g. "gemini-2.5-flash"

    # Check whether the stable GA version exists in litellm's registry
    # (either bare or under common provider prefixes)
    if ga_name in all_model_ids:
        return True
    if f"gemini/{ga_name}" in all_model_ids:
        return True

    return False


def _get_elo(model_id: str) -> int:
    """Look up ELO for a model.

    Lookup order (stops at first hit):
    1. Exact match in ELO_SCORES
    2. _extract_base_model() -> ELO_SCORES lookup
    3. Return 0
    """
    if model_id in ELO_SCORES:
        return ELO_SCORES[model_id]
    canonical = _extract_base_model(model_id)
    if canonical is not None:
        return ELO_SCORES[canonical]
    return 0


def build_rows() -> List[dict]:
    try:
        import litellm
    except ImportError:
        print("ERROR: litellm is not installed. Run: pip install litellm", file=sys.stderr)
        sys.exit(1)

    all_model_ids = set(litellm.model_cost.keys())
    rows = []
    skipped_previews = 0

    for model_id, entry in litellm.model_cost.items():
        # Only chat and responses modes (responses = OpenAI's newer API format)
        if entry.get("mode") not in ("chat", "responses"):
            continue
        # Skip deprecated
        if _is_deprecated(entry):
            continue
        # Skip placeholder/tier entries
        if _is_placeholder(model_id):
            continue
        # Fix B: Skip fast/ and us/ routing prefix variants entirely.
        # These are LiteLLM routing hints, not separate models. fast/ has 6x
        # inflated pricing; us/ has 10% regional surcharge. Both resolve to
        # the same underlying model at the same endpoint.
        if _FAST_PREFIX.match(model_id):
            continue
        # Skip dated preview models superseded by a stable GA release
        if _is_superseded_preview(model_id, all_model_ids):
            skipped_previews += 1
            continue
        # Skip models that cannot produce text output (e.g. TTS / audio-only)
        output_modalities = entry.get("supported_output_modalities", [])
        if output_modalities and "text" not in output_modalities:
            continue

        litellm_provider: str = entry.get("litellm_provider", "")
        root_provider = _get_provider_root(litellm_provider)

        # ELO — skip models below cutoff or with no known score
        elo = _get_elo(model_id)
        if elo < ELO_CUTOFF:
            continue

        # Convert per-token costs to per-million
        in_cost_token = entry.get("input_cost_per_token") or 0.0
        out_cost_token = entry.get("output_cost_per_token") or 0.0
        input_cost = round(in_cost_token * 1_000_000, 6)
        output_cost = round(out_cost_token * 1_000_000, 6)

        # Apply manual price overrides for known LiteLLM pricing bugs
        if model_id in PRICE_OVERRIDES:
            input_cost, output_cost = PRICE_OVERRIDES[model_id]

        # Provider display name and API key env var
        display_name, api_key = PROVIDERS.get(
            litellm_provider,
            PROVIDERS.get(
                root_provider,
                (litellm_provider.replace("_", " ").title(), f"{root_provider.upper()}_API_KEY"),
            ),
        )

        # Structured output
        structured = bool(
            entry.get("supports_function_calling") or
            entry.get("supports_response_schema")
        )

        # Reasoning
        reasoning_type = _infer_reasoning_type(model_id, litellm_provider, entry)
        max_reasoning_tokens = _infer_max_reasoning_tokens(model_id, litellm_provider, entry)

        # Location (Vertex AI models default to global)
        location = "global" if litellm_provider.startswith("vertex_ai") else ""

        rows.append({
            "provider": display_name,
            "model": model_id,
            "input": input_cost,
            "output": output_cost,
            "coding_arena_elo": elo,
            "base_url": "",
            "api_key": api_key,
            "max_reasoning_tokens": max_reasoning_tokens,
            "structured_output": structured,
            "reasoning_type": reasoning_type,
            "location": location,
        })

    if skipped_previews:
        print(f"  Skipped {skipped_previews} dated preview model(s) superseded by stable GA releases.")

    initial_count = len(rows)

    # ------------------------------------------------------------------
    # Fix C: Skip dated variants when the undated version exists.
    # e.g. drop "claude-opus-4-6-20260205" if "claude-opus-4-6" is present,
    # and drop "vertex_ai/claude-opus-4-5@20250929" if the unversioned
    # "vertex_ai/claude-opus-4-5" is present.
    # ------------------------------------------------------------------
    model_ids_present = {r["model"] for r in rows}
    kept_after_c: List[dict] = []
    skipped_dated = 0
    for row in rows:
        mid = row["model"]
        # Check bare Anthropic dated IDs: claude-*-YYYYMMDD
        m = _DATED_ANTHROPIC.match(mid)
        if m and m.group("base") in model_ids_present:
            skipped_dated += 1
            continue
        # Check Vertex AI @version suffixed IDs
        if "@" in mid:
            base_no_version = _VERTEX_VERSION.sub("", mid)
            if base_no_version != mid and base_no_version in model_ids_present:
                skipped_dated += 1
                continue
        # Check Bedrock versioned IDs (e.g. anthropic.claude-opus-4-5-20251101-v1:0)
        stripped = _BEDROCK_VERSION.sub("", mid)
        if stripped != mid and stripped in model_ids_present:
            skipped_dated += 1
            continue
        kept_after_c.append(row)
    rows = kept_after_c
    if skipped_dated:
        print(f"  Fix C: Removed {skipped_dated} dated/versioned variant(s).")

    # ------------------------------------------------------------------
    # Fix A: Deduplicate per (provider_display, canonical_base_model).
    # For each provider × base model, keep only the cheapest non-regional
    # variant. This collapses e.g. 14 Anthropic claude-opus-4-6 rows into 1.
    # ------------------------------------------------------------------
    # Also handles Bedrock region dedup: for Bedrock, multiple region-specific
    # model IDs (bedrock/us-east-1/..., bedrock/eu-north-1/..., us.anthropic...,
    # eu.anthropic...) resolve to the same model. We keep only the cheapest
    # (typically the regionless/global variant).
    dedup_buckets: Dict[Tuple[str, str], List[dict]] = defaultdict(list)
    no_canonical = 0
    for row in rows:
        canonical = _extract_base_model(row["model"])
        if canonical is None:
            # Can't canonicalize — keep it as-is (use model ID as its own key)
            canonical = row["model"]
            no_canonical += 1
        dedup_buckets[(row["provider"], canonical)].append(row)

    rows_deduped: List[dict] = []
    dedup_removed = 0
    for (_provider, _base), bucket in dedup_buckets.items():
        if len(bucket) == 1:
            rows_deduped.append(bucket[0])
        else:
            # Keep the cheapest variant (by avg cost = (input + output) / 2).
            # Tiebreaker: prefer regionless model IDs so Bedrock users aren't
            # locked to a specific region (e.g. "bedrock/moonshotai.kimi-k2.5"
            # over "bedrock/us-east-1/moonshotai.kimi-k2.5").
            bucket.sort(key=lambda r: (
                (r["input"] + r["output"]) / 2,
                _has_region(r["model"]),
            ))
            rows_deduped.append(bucket[0])
            dedup_removed += len(bucket) - 1
    rows = rows_deduped
    if dedup_removed:
        print(f"  Fix A: Deduplicated {dedup_removed} provider×model variant(s).")

    # ------------------------------------------------------------------
    # Sanity filter — drop rows where input or output cost exceeds the cap.
    # Catches LiteLLM pricing bugs (e.g. values off by 100,000×).
    # ------------------------------------------------------------------
    pre_sanity = len(rows)
    rows = [
        r for r in rows
        if r["input"] <= MAX_COST_PER_MTOK and r["output"] <= MAX_COST_PER_MTOK
    ]
    sanity_removed = pre_sanity - len(rows)
    if sanity_removed:
        print(f"  Sanity filter: Removed {sanity_removed} row(s) with cost > ${MAX_COST_PER_MTOK}/Mtok.")

    # ------------------------------------------------------------------
    # Fix D: Pareto filter — remove models that are strictly dominated
    # (higher cost AND lower ELO) by another model *from the same provider*.
    #
    # A model X is dominated if there exists model Y (same provider) where:
    #   Y.elo >= X.elo  AND  Y.avg_cost <= X.avg_cost  AND  (strictly better on >= 1)
    #
    # Scoped per-provider so that free-tier providers (GitHub Copilot) don't
    # wipe out paid providers that users with different API keys still need.
    # This prunes e.g. Opus 4/4.1 ($15/$75, ELO 1405/1475) within Anthropic
    # since Opus 4.5/4.6 ($5/$25, ELO 1496/1530) strictly dominate them.
    # ------------------------------------------------------------------
    provider_groups: Dict[str, List[dict]] = defaultdict(list)
    for row in rows:
        provider_groups[row["provider"]].append(row)

    pareto_removed = 0
    pareto_kept: List[dict] = []
    for provider, group in provider_groups.items():
        # Skip Pareto filtering for zero-cost providers (e.g. GitHub Copilot,
        # Snowflake, Dashscope). All their models report $0, so cost isn't a
        # meaningful differentiator and only the highest-ELO model would survive.
        all_zero = all((r["input"] + r["output"]) == 0 for r in group)
        if all_zero:
            pareto_kept.extend(group)
            continue
        for candidate in group:
            c_elo = candidate["coding_arena_elo"]
            c_avg = (candidate["input"] + candidate["output"]) / 2
            dominated = False
            for other in group:
                if other is candidate:
                    continue
                o_elo = other["coding_arena_elo"]
                o_avg = (other["input"] + other["output"]) / 2
                if o_elo >= c_elo and o_avg <= c_avg:
                    if o_elo > c_elo or o_avg < c_avg:
                        dominated = True
                        break
            if dominated:
                pareto_removed += 1
            else:
                pareto_kept.append(candidate)
    rows = pareto_kept
    if pareto_removed:
        print(f"  Fix D: Removed {pareto_removed} Pareto-dominated model(s).")

    print(f"  Post-processing: {initial_count} -> {len(rows)} rows.")

    # Sort: provider ascending, then ELO descending within each provider
    rows.sort(key=lambda r: (r["provider"], -r["coding_arena_elo"], r["model"]))
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    default_output = Path(__file__).parent.parent / "pdd" / "data" / "llm_model.csv"
    parser.add_argument(
        "--output", "-o",
        type=Path,
        default=default_output,
        help=f"Output CSV path (default: {default_output})",
    )
    args = parser.parse_args()

    output_path: Path = args.output
    output_path.parent.mkdir(parents=True, exist_ok=True)

    print("Building model catalog from litellm.model_cost...")
    rows = build_rows()
    print(f"  Found {len(rows)} chat models across all providers.")

    with open(output_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=CSV_FIELDNAMES)
        writer.writeheader()
        writer.writerows(rows)

    print(f"  Written to: {output_path}")

    # Print a quick summary by provider
    from collections import Counter
    providers = Counter(r["provider"] for r in rows)
    print("\nProviders by model count:")
    for provider, count in providers.most_common():
        print(f"  {provider}: {count}")


if __name__ == "__main__":
    main()
