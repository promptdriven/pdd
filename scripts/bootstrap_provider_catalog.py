#!/usr/bin/env python3
"""One-time importer for the v1 provider catalog source manifest.

Run only when deliberately migrating a hand-maintained CSV into a new catalog
schema. Normal edits go to ``data/provider_catalog.v1.json`` and then use
``provider_catalog.py`` to regenerate derived files.
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import OrderedDict
from pathlib import Path
from typing import Any


def _api_key(field: str = "api_key", label: str = "API key") -> dict[str, Any]:
    return {
        "kind": "api_key",
        "fields": [{"id": field, "label": label, "secret": True}],
    }


def _openai_request(
    base_path: str = "/v1", *, responses: bool = False
) -> dict[str, Any]:
    return {
        "methods": ["POST"],
        "paths": ["/responses", "/chat/completions"]
        if responses
        else ["/chat/completions"],
        "query": [],
        "headers": ["accept", "content-type", "user-agent"],
        "base_path": base_path,
    }


def _failure() -> dict[str, list[int]]:
    return {
        "unauthorized": [401],
        "forbidden": [403],
        "quota": [429],
        "transient": [408, 425, 500, 502, 503, 504],
    }


def _profile(
    provider_id: str,
    display_name: str,
    *,
    origin: str | None,
    protocol: str = "openai_chat_completions",
    label: str,
    eligible: bool = False,
    reason: str = "Execution profile has not passed GitHub App conformance tests.",
    execution_profile: str = "manual_review",
    model_labels: dict[str, str] | None = None,
    auth: dict[str, Any] | None = None,
    base_path: str = "/v1",
    source_prefix: str = "",
) -> dict[str, Any]:
    if protocol == "specialized":
        request = {
            "methods": [],
            "paths": [],
            "query": [],
            "headers": [],
            "base_path": "",
        }
        probe = {"method": "NONE", "path": ""}
    elif protocol == "anthropic_messages":
        request = {
            "methods": ["POST"],
            "paths": ["/v1/messages"],
            "query": [],
            "headers": ["accept", "anthropic-version", "content-type", "user-agent"],
            "base_path": "",
        }
        probe = {"method": "POST", "path": "/v1/messages"}
    elif protocol == "gemini_generate":
        request = {
            "methods": ["POST"],
            "paths": ["/v1beta/models/{model}:generateContent"],
            "query": ["alt"],
            "headers": ["accept", "content-type", "user-agent"],
            "base_path": "",
        }
        probe = {"method": "GET", "path": "/v1beta/models"}
    else:
        request = _openai_request(base_path, responses=protocol == "openai_responses")
        probe = {"method": "GET", "path": "/models"}
    return {
        "id": provider_id,
        "display_name": display_name,
        "origin": origin,
        "origin_reason": reason if origin is None else "",
        "protocol": protocol,
        "auth": auth or _api_key(),
        "request": request,
        "probe": probe,
        "failure": _failure(),
        "github": {
            "label": label,
            **({"model_labels": model_labels} if model_labels else {}),
            "execution_profile": execution_profile,
            "eligible": eligible,
            "reason": "" if eligible else reason,
        },
        "source_prefix": source_prefix,
    }


MULTI_AWS = {
    "kind": "multi_field",
    "fields": [
        {"id": "access_key_id", "label": "Access key ID", "secret": True},
        {"id": "secret_access_key", "label": "Secret access key", "secret": True},
        {"id": "region", "label": "AWS region", "secret": False},
    ],
}
MULTI_AZURE = {
    "kind": "multi_field",
    "fields": [
        {"id": "api_key", "label": "API key", "secret": True},
        {"id": "endpoint", "label": "HTTPS endpoint", "secret": False},
        {"id": "api_version", "label": "API version", "secret": False},
    ],
}
MULTI_VERTEX = {
    "kind": "cloud_identity",
    "fields": [
        {"id": "service_account_json", "label": "Service account JSON", "secret": True},
        {"id": "project_id", "label": "Google Cloud project", "secret": False},
        {"id": "location", "label": "Vertex region", "secret": False},
    ],
}


# This table is public protocol metadata, not a list of stored secrets.  The
# small `eligible` set has a concrete protocol adapter and contract tests in
# the GitHub App; all other catalog rows remain visible with an honest reason
# until they receive a reviewed execution profile.
PROFILES: dict[str, dict[str, Any]] = {
    "Anthropic": _profile(
        "claude",
        "Anthropic / Claude",
        origin="https://api.anthropic.com",
        protocol="anthropic_messages",
        label="pdd-opus",
        eligible=True,
        execution_profile="native_claude",
        source_prefix="",
    ),
    "AWS Bedrock": _profile(
        "aws_bedrock",
        "AWS Bedrock",
        origin=None,
        protocol="specialized",
        label="pdd-bedrock",
        auth=MULTI_AWS,
        reason="AWS request signing and per-account IAM identity need a reviewed Bedrock profile.",
    ),
    "Azure AI": _profile(
        "azure_ai",
        "Azure AI",
        origin=None,
        label="pdd-azure-ai",
        auth=MULTI_AZURE,
        reason="Azure AI deployment routing needs a reviewed multi-field profile.",
    ),
    "Azure OpenAI": _profile(
        "azure_openai",
        "Azure OpenAI",
        origin=None,
        protocol="openai_responses",
        label="pdd-azure-openai",
        auth=MULTI_AZURE,
        reason="Azure deployment and API-version routing need a reviewed multi-field profile.",
    ),
    "Baseten": _profile(
        "baseten",
        "Baseten",
        origin="https://inference.baseten.co",
        label="pdd-baseten",
        source_prefix="baseten/",
    ),
    "Dashscope": _profile(
        "dashscope",
        "DashScope",
        origin="https://dashscope.aliyuncs.com",
        label="pdd-dashscope",
        base_path="/compatible-mode/v1",
        source_prefix="dashscope/",
    ),
    "DeepInfra": _profile(
        "deepinfra",
        "DeepInfra",
        origin="https://api.deepinfra.com",
        label="pdd-deepinfra",
        base_path="/v1/openai",
        source_prefix="deepinfra/",
    ),
    "DeepSeek": _profile(
        "deepseek",
        "DeepSeek",
        origin="https://api.deepseek.com",
        label="pdd-deepseek",
        eligible=True,
        execution_profile="opencode_openai_chat",
        source_prefix="deepseek/",
    ),
    "Fireworks AI": _profile(
        "fireworks",
        "Fireworks AI",
        origin="https://api.fireworks.ai",
        label="pdd-fireworks",
        eligible=True,
        execution_profile="opencode_openai_chat",
        source_prefix="fireworks_ai/",
    ),
    "Github Copilot": _profile(
        "github_copilot",
        "GitHub Copilot",
        origin=None,
        protocol="specialized",
        label="pdd-copilot",
        auth={
            "kind": "interactive_subscription",
            "fields": [{"id": "device_login", "label": "Device login", "secret": True}],
        },
        reason="GitHub Copilot uses an interactive device/subscription flow, not a reusable cloud API key.",
        execution_profile="interactive_only",
    ),
    "GMI Cloud": _profile(
        "gmi_cloud",
        "GMI Cloud",
        origin="https://api.gmi-serving.com",
        label="pdd-gmi",
        source_prefix="gmi/",
    ),
    "Google Gemini": _profile(
        "gemini",
        "Google Gemini",
        origin="https://generativelanguage.googleapis.com",
        protocol="gemini_generate",
        label="pdd-gemini",
        eligible=True,
        execution_profile="native_gemini",
        source_prefix="gemini/",
    ),
    "Google Vertex AI": _profile(
        "vertex_ai",
        "Google Vertex AI",
        origin=None,
        protocol="specialized",
        label="pdd-vertex",
        auth=MULTI_VERTEX,
        reason="Vertex identity, regional endpoint, and service-account handling need a reviewed cloud-identity profile.",
    ),
    "Heroku": _profile(
        "heroku",
        "Heroku",
        origin="https://us.inference.heroku.com",
        label="pdd-heroku",
        source_prefix="heroku/",
    ),
    "Hyperbolic": _profile(
        "hyperbolic",
        "Hyperbolic",
        origin="https://api.hyperbolic.xyz",
        label="pdd-hyperbolic",
        source_prefix="hyperbolic/",
    ),
    "Lambda AI": _profile(
        "lambda",
        "Lambda AI",
        origin="https://api.lambda.ai",
        label="pdd-lambda",
        source_prefix="lambda_ai/",
    ),
    "lm_studio": _profile(
        "lm_studio",
        "LM Studio",
        origin=None,
        label="pdd-lm-studio",
        auth={
            "kind": "multi_field",
            "fields": [{"id": "base_url", "label": "Local URL", "secret": False}],
        },
        reason="Localhost and private-network endpoints cannot run through the GitHub App without a separately reviewed tunnel.",
        execution_profile="local_only",
    ),
    "MiniMax": _profile(
        "minimax",
        "MiniMax",
        origin="https://api.minimax.io",
        label="pdd-minimax",
        source_prefix="minimax/",
    ),
    "Moonshot AI": _profile(
        "moonshot",
        "Moonshot AI",
        origin="https://api.moonshot.ai",
        label="pdd-moonshot",
        eligible=True,
        execution_profile="opencode_openai_chat",
        model_labels={"pdd-kimi": "moonshot/kimi-k3"},
        source_prefix="moonshot/",
    ),
    "Nebius": _profile(
        "nebius",
        "Nebius",
        origin="https://api.studio.nebius.ai",
        label="pdd-nebius",
        source_prefix="nebius/",
    ),
    "Novita AI": _profile(
        "novita",
        "Novita AI",
        origin="https://api.novita.ai",
        label="pdd-novita",
        base_path="/v3/openai",
        source_prefix="novita/",
    ),
    "Oci": _profile(
        "oci",
        "Oracle Cloud Infrastructure",
        origin=None,
        protocol="specialized",
        label="pdd-oci",
        auth={
            "kind": "multi_field",
            "fields": [
                {"id": "api_key", "label": "API key", "secret": True},
                {"id": "endpoint", "label": "HTTPS endpoint", "secret": False},
            ],
        },
        reason="OCI tenancy, region, and request-signing support need a reviewed profile.",
    ),
    "OpenAI": _profile(
        "openai",
        "OpenAI API",
        origin="https://api.openai.com",
        protocol="openai_responses",
        label="pdd-openai",
        eligible=True,
        execution_profile="opencode_openai_chat",
    ),
    "OpenAI ChatGPT": _profile(
        "codex",
        "ChatGPT subscription",
        origin=None,
        protocol="specialized",
        label="pdd-codex",
        auth={
            "kind": "interactive_subscription",
            "fields": [
                {
                    "id": "subscription_token",
                    "label": "Subscription login",
                    "secret": True,
                }
            ],
        },
        reason="ChatGPT/Codex subscription connections keep their specialized device-login lifecycle.",
        execution_profile="interactive_only",
    ),
    "OpenRouter": _profile(
        "openrouter",
        "OpenRouter",
        origin="https://openrouter.ai",
        label="pdd-openrouter",
        eligible=True,
        execution_profile="opencode_openai_chat",
        source_prefix="openrouter/",
    ),
    "Perplexity": _profile(
        "perplexity",
        "Perplexity",
        origin="https://api.perplexity.ai",
        label="pdd-perplexity",
        source_prefix="perplexity/",
    ),
    "Replicate": _profile(
        "replicate",
        "Replicate",
        origin="https://api.replicate.com",
        protocol="specialized",
        label="pdd-replicate",
        reason="Replicate prediction lifecycle needs a reviewed specialized execution profile.",
    ),
    "SambaNova": _profile(
        "sambanova",
        "SambaNova",
        origin="https://api.sambanova.ai",
        label="pdd-sambanova",
        source_prefix="sambanova/",
    ),
    "Snowflake": _profile(
        "snowflake",
        "Snowflake Cortex",
        origin=None,
        protocol="specialized",
        label="pdd-snowflake",
        auth={
            "kind": "multi_field",
            "fields": [
                {"id": "api_key", "label": "API key", "secret": True},
                {"id": "account", "label": "Account identifier", "secret": False},
            ],
        },
        reason="Snowflake account and regional endpoint handling need a reviewed profile.",
    ),
    "Together AI": _profile(
        "together",
        "Together AI",
        origin="https://api.together.xyz",
        label="pdd-together",
        eligible=True,
        execution_profile="opencode_openai_chat",
        source_prefix="together_ai/",
    ),
    "Vercel AI Gateway": _profile(
        "vercel_ai_gateway",
        "Vercel AI Gateway",
        origin="https://ai-gateway.vercel.sh",
        label="pdd-vercel",
        source_prefix="vercel_ai_gateway/",
    ),
    "W&B Inference": _profile(
        "wandb",
        "Weights & Biases Inference",
        origin="https://api.inference.wandb.ai",
        label="pdd-wandb",
        source_prefix="wandb/",
    ),
    "xAI": _profile(
        "grok",
        "xAI / Grok",
        origin="https://api.x.ai",
        label="pdd-grok",
        eligible=True,
        execution_profile="opencode_openai_chat",
        source_prefix="xai/",
    ),
    "Z.AI": _profile(
        "zai",
        "Z.AI",
        origin="https://api.z.ai",
        label="pdd-zai",
        base_path="/api/paas/v4",
        source_prefix="openai/",
    ),
    "Z.AI Coding Plan": _profile(
        "glm",
        "Z.AI Coding Plan",
        origin="https://api.z.ai",
        protocol="anthropic_messages",
        label="pdd-glm",
        eligible=True,
        execution_profile="native_glm",
        base_path="/api/coding/paas/v4",
        source_prefix="openai/",
    ),
    "Zai": _profile(
        "zai",
        "Z.AI",
        origin="https://api.z.ai",
        label="pdd-zai",
        base_path="/api/paas/v4",
        source_prefix="zai/",
    ),
}


def _upstream_model(row: dict[str, str], profile: dict[str, Any]) -> str:
    model = row["model"]
    prefix = str(profile.get("source_prefix") or "")
    if prefix and model.startswith(prefix):
        return model.removeprefix(prefix)
    # LiteLLM catalog prefixes identify a routing adapter, not necessarily the
    # upstream model string.  Keep unknown/specialized rows exact rather than
    # accidentally inventing an upstream id.
    return model


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cli-csv", type=Path, required=True)
    parser.add_argument("--cloud-csv", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    with args.cli_csv.open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
        columns = list(
            csv.DictReader(args.cli_csv.open(encoding="utf-8", newline="")).fieldnames
            or []
        )
    unknown = sorted({row["provider"] for row in rows} - set(PROFILES))
    if unknown:
        raise SystemExit(f"Missing catalog profiles: {', '.join(unknown)}")

    grouped: OrderedDict[str, dict[str, Any]] = OrderedDict()
    for order, row in enumerate(rows):
        profile = PROFILES[row["provider"]]
        provider_id = str(profile["id"])
        provider = grouped.setdefault(
            provider_id,
            {
                key: value
                for key, value in profile.items()
                if key not in {"source_prefix", "csv_providers", "models"}
            }
            | {"csv_providers": [], "models": []},
        )
        if row["provider"] not in provider["csv_providers"]:
            provider["csv_providers"].append(row["provider"])
        provider["models"].append(
            {
                "order": order,
                "csv": {column: row.get(column, "") for column in columns},
                "upstream_model": _upstream_model(row, profile),
                "capabilities": ["text_generation", "streaming", "tools"],
                "byok_eligible": bool(profile["github"]["eligible"]),
            }
        )

    with args.cloud_csv.open(encoding="utf-8", newline="") as handle:
        cloud_reader = csv.DictReader(handle)
        cloud_columns = list(cloud_reader.fieldnames or [])
        cloud_rows = list(cloud_reader)
    manifest = {
        "schema_version": 1,
        "catalog_version": "2026-07-22",
        "providers": list(grouped.values()),
        "cloud_csv_columns": cloud_columns,
        "cloud_csv": cloud_rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(manifest, indent=2, sort_keys=False) + "\n", encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
