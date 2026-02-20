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
from datetime import date
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# ELO cutoff — models below this score are excluded from the catalog.
# ---------------------------------------------------------------------------
ELO_CUTOFF = 1400

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
    # Anthropic Claude — dash-separated canonical form
    # -----------------------------------------------------------------------
    "claude-opus-4-6": 1530,
    "claude-opus-4-5": 1496,
    "claude-opus-4": 1405,
    "claude-opus-4-1": 1475,
    "claude-sonnet-4-6": 1485,
    "claude-sonnet-4-5": 1464,
    "claude-sonnet-4": 1384,
    "claude-3-7-sonnet": 1341,
    "claude-3-5-sonnet-20241022": 1340,
    "claude-3-5-sonnet-20240620": 1309,
    "claude-3-5-sonnet": 1340,
    "claude-haiku-4-5": 1436,
    "claude-3-5-haiku": 1287,
    "claude-3-opus": 1269,
    "claude-3-haiku": 1208,
    "claude-3-sonnet": 1232,
    # Dot-separated variants (OpenRouter, GitHub Copilot, Vercel, GMI)
    "claude-opus-4.6": 1530,
    "claude-opus-4.5": 1496,
    "claude-opus-4.1": 1475,
    "claude-sonnet-4.6": 1485,
    "claude-sonnet-4.5": 1464,
    "claude-haiku-4.5": 1436,
    "claude-3.5-sonnet": 1340,
    "claude-3.5-haiku": 1287,
    "claude-3.7-sonnet": 1341,
    # Alternate naming: "claude-4-opus" / "claude-4-sonnet"
    "claude-4-opus": 1405,
    "claude-4-sonnet": 1384,
    # -----------------------------------------------------------------------
    # OpenAI — GPT-5 family
    # -----------------------------------------------------------------------
    "gpt-5": 1460,
    "gpt-5.1": 1450,
    "gpt-5.2": 1465,
    "gpt-5-mini": 1419,
    "gpt-5-nano": 1363,
    # OpenAI — GPT-4.x
    "gpt-4.5": 1419,
    "gpt-4.1": 1396,
    "gpt-4.1-mini": 1370,
    "gpt-4.1-nano": 1312,
    "gpt-4o": 1307,
    "gpt-4o-2024-08-06": 1307,
    "gpt-4o-2024-11-20": 1307,
    "gpt-4o-mini": 1300,
    "gpt-4-turbo": 1280,
    "gpt-4-0125-preview": 1261,
    "gpt-4-1106-preview": 1269,
    # OpenAI — o-series
    "o3": 1441,
    "o4-mini": 1385,
    "o3-mini": 1361,
    "o1": 1378,
    "o1-mini": 1366,
    "o1-preview": 1378,
    # OpenAI — gpt-oss
    "gpt-oss-120b": 1398,
    "gpt-oss-20b": 1371,
    # -----------------------------------------------------------------------
    # Google Gemini
    # -----------------------------------------------------------------------
    "gemini-3-pro": 1501,
    "gemini-3-pro-preview": 1501,
    "gemini-3-flash": 1469,
    "gemini-3-flash-preview": 1469,
    "gemini-2.5-pro": 1465,
    "gemini-2.5-flash": 1420,
    "gemini-2.0-flash": 1371,
    "gemini-2.0-flash-thinking": 1383,
    "gemini-1.5-pro": 1311,
    "gemini-1.5-flash": 1273,
    # -----------------------------------------------------------------------
    # DeepSeek
    # -----------------------------------------------------------------------
    "deepseek-r1": 1382,
    "deepseek-r1-0528": 1436,
    "deepseek-reasoner": 1382,
    "deepseek-chat": 1337,
    "deepseek-v3": 1337,
    "deepseek-v3-0324": 1391,
    "deepseek-v3.1": 1430,
    "deepseek-v3.2": 1431,
    # -----------------------------------------------------------------------
    # xAI / Grok
    # -----------------------------------------------------------------------
    "grok-4.1": 1483,
    "grok-4": 1453,
    "grok-4-fast": 1441,
    "grok-3": 1439,
    "grok-3-mini": 1380,
    "grok-2": 1298,
    # -----------------------------------------------------------------------
    # Mistral
    # -----------------------------------------------------------------------
    "mistral-large": 1450,
    "mistral-large-3": 1450,
    "mistral-medium-3": 1387,
    "mistral-medium-3.1": 1412,
    "magistral-medium": 1307,
    "magistral-small": 1330,
    "codestral": 1300,
    "mistral-small-3.1": 1295,
    "mistral-small-3.2": 1361,
    "mistral-small-3": 1251,
    # -----------------------------------------------------------------------
    # Moonshot / Kimi
    # -----------------------------------------------------------------------
    "kimi-k2.5": 1480,
    "kimi-k2-instruct": 1402,
    "kimi-k2-thinking": 1450,
    "kimi-k2-0905": 1403,
    "kimi-k2-0711": 1402,
    # -----------------------------------------------------------------------
    # Meta Llama
    # -----------------------------------------------------------------------
    "llama-4-maverick-17b-128e": 1312,
    "llama-4-scout-17b-16e": 1290,
    "llama-3.3-70b": 1279,
    "llama-3.1-405b": 1299,
    "llama-3.1-70b": 1268,
    "llama-3.1-8b": 1203,
    "llama-3-70b": 1216,
    # -----------------------------------------------------------------------
    # Qwen / Alibaba
    # -----------------------------------------------------------------------
    "qwen3-max": 1468,
    "qwen3-235b-a22b": 1394,
    "qwen3-235b-a22b-instruct-2507": 1457,
    "qwen3-235b-a22b-thinking-2507": 1442,
    "qwen3-32b": 1376,
    "qwen3-30b-a3b": 1346,
    "qwen3-coder-480b-a35b": 1406,
    "qwq-32b": 1351,
    "qwen2.5-72b": 1302,
    "qwen2.5-max": 1373,
    # -----------------------------------------------------------------------
    # GLM (Zhipu AI / ZAI)
    # -----------------------------------------------------------------------
    "glm-5": 1461,
    "glm-4.7": 1460,
    "glm-4.6": 1458,
    "glm-4.5": 1448,
    "glm-4.5-air": 1410,
    # -----------------------------------------------------------------------
    # Minimax
    # -----------------------------------------------------------------------
    "minimax-m2.1": 1430,
    "minimax-m1": 1369,
    "minimax-m2": 1430,
    # -----------------------------------------------------------------------
    # Amazon Nova
    # -----------------------------------------------------------------------
    "nova-pro": 1282,
    "nova-lite": 1253,
    "nova-micro": 1228,
    # -----------------------------------------------------------------------
    # MiMo (Xiaomi)
    # -----------------------------------------------------------------------
    "mimo-v2-flash": 1411,
    # -----------------------------------------------------------------------
    # Gemma (Google open)
    # -----------------------------------------------------------------------
    "gemma-3-27b": 1350,
    "gemma-3-12b": 1310,
    "gemma-3-4b": 1265,
    # -----------------------------------------------------------------------
    # NVIDIA Nemotron
    # -----------------------------------------------------------------------
    "llama-3.3-nemotron-super-49b": 1359,
    "llama-3.1-nemotron-70b": 1289,
    # -----------------------------------------------------------------------
    # Phi (Microsoft)
    # -----------------------------------------------------------------------
    "phi-4": 1242,
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
    "cohere", "cohere_chat", "meta_llama", "dashscope",
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
    r"allenai|NousResearch|nvidia|MiniMaxAI)/",
    re.IGNORECASE,
)

# Fireworks account path: accounts/fireworks/models/ (or any account)
_FIREWORKS_ACCOUNT = re.compile(
    r"^accounts/[^/]+/models/",
    re.IGNORECASE,
)

# Anthropic fast/us routing prefixes on bare IDs
_FAST_PREFIX = re.compile(r"^(?:fast/us/|fast/|us/)", re.IGNORECASE)

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
        # Only chat mode
        if entry.get("mode") != "chat":
            continue
        # Skip deprecated
        if _is_deprecated(entry):
            continue
        # Skip placeholder/tier entries
        if _is_placeholder(model_id):
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

    # Sort: ELO descending, then model name ascending
    rows.sort(key=lambda r: (-r["coding_arena_elo"], r["model"]))
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
    print("\nTop providers by model count:")
    for provider, count in providers.most_common(20):
        print(f"  {provider}: {count}")


if __name__ == "__main__":
    main()
