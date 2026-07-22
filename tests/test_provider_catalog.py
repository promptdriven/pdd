"""Drift guards for the canonical provider catalog source."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "pdd" / "data" / "provider_catalog.v1.json"
CLI_CSV = ROOT / "pdd" / "data" / "llm_model.csv"
GENERATOR = ROOT / "scripts" / "provider_catalog.py"


def _generator_module():
    spec = importlib.util.spec_from_file_location(
        "provider_catalog_generator", GENERATOR
    )
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_cli_catalog_is_generated_from_the_v1_manifest() -> None:
    generator = _generator_module()
    manifest = generator._read_json(MANIFEST)
    providers = generator._validate_manifest(manifest)
    entries = sorted(
        (entry for provider in providers for entry in provider["models"]),
        key=lambda entry: entry["order"],
    )
    expected = generator._csv_bytes([entry["csv"] for entry in entries])
    assert CLI_CSV.read_bytes() == expected


def test_catalog_declares_an_honest_github_execution_status_for_every_provider() -> (
    None
):
    generator = _generator_module()
    manifest = generator._read_json(MANIFEST)
    providers = generator._validate_manifest(manifest)
    assert {provider["id"] for provider in providers} >= {
        "grok",
        "openrouter",
        "deepseek",
        "together",
        "fireworks",
        "claude",
        "gemini",
    }
    for provider in providers:
        github = provider["github"]
        if not github["eligible"]:
            assert github["reason"]


def test_fixed_origin_openai_compatible_rows_use_the_reviewed_gateway_profile() -> None:
    """Single-key catalog providers must not be left as a CSV-only promise."""
    generator = _generator_module()
    manifest = generator._read_json(MANIFEST)
    providers = generator._validate_manifest(manifest)
    cloud_compatible = [
        provider
        for provider in providers
        if provider["protocol"] == "openai_chat_completions"
        and provider["origin"]
        and provider["auth"]["kind"] == "api_key"
        and provider["request"]["methods"] == ["POST"]
        and provider["request"]["paths"] == ["/chat/completions"]
        and provider["probe"] == {"method": "GET", "path": "/models"}
    ]
    assert cloud_compatible
    for provider in cloud_compatible:
        github = provider["github"]
        assert github["eligible"] is True
        assert github["execution_profile"] == "opencode_openai_chat"
        assert github["reason"] == ""
        assert all(model["byok_eligible"] for model in provider["models"])
