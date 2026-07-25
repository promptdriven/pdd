"""Drift guards for the canonical provider catalog source."""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

from pdd import provider_manager


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "pdd" / "data" / "provider_catalog.v1.json"
CLI_CSV = ROOT / "pdd" / "data" / "llm_model.csv"
GENERATOR = ROOT / "scripts" / "provider_catalog.py"
BOOTSTRAP = ROOT / "scripts" / "bootstrap_provider_catalog.py"


def _load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(
        name, path
    )
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _generator_module():
    return _load_module(GENERATOR, "provider_catalog_generator")


def _manifest_and_generator():
    generator = _generator_module()
    return generator._read_json(MANIFEST), generator


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


def test_kimi_k3_model_route_and_strict_label_are_canonical() -> None:
    manifest, generator = _manifest_and_generator()
    providers = generator._validate_manifest(manifest)
    assert provider_manager.parse_api_key_vars("MOONSHOT_API_KEY") == [
        "MOONSHOT_API_KEY"
    ]
    metadata = generator._catalog_metadata(
        manifest,
        providers,
        source_digest=generator.source_sha256(MANIFEST),
    )
    moonshot = next(
        provider for provider in metadata["providers"] if provider["id"] == "moonshot"
    )
    assert moonshot["origin"] == "https://api.moonshot.ai"
    assert moonshot["github"]["label"] == "pdd-moonshot"
    assert moonshot["github"]["model_labels"] == {
        "pdd-kimi": "moonshot/kimi-k3"
    }
    by_model = {model["model"]: model for model in moonshot["models"]}
    assert by_model["moonshot/kimi-k3"] == {
        "model": "moonshot/kimi-k3",
        "upstream_model": "kimi-k3",
        "capabilities": [
            "text_generation",
            "streaming",
            "tools",
            "structured_output",
            "reasoning_content",
            "long_context",
        ],
        "context_limit": "1048576",
        "input": "2.951594",
        "output": "14.757969",
        "reasoning_type": "effort",
        "byok_eligible": True,
        "base_url": "https://api.moonshot.cn/v1",
    }
    assert "base_url" not in by_model["moonshot/kimi-k2.6"]


@pytest.mark.parametrize(
    ("label", "target", "message"),
    [
        ("kimi", "moonshot/kimi-k3", "GitHub model label is invalid"),
        ("pdd-openai", "moonshot/kimi-k3", "Duplicate GitHub label"),
        ("pdd-kimi", "moonshot/not-a-model", "targets unknown model"),
    ],
)
def test_model_labels_fail_closed(label: str, target: str, message: str) -> None:
    manifest, generator = _manifest_and_generator()
    moonshot = next(
        provider for provider in manifest["providers"] if provider["id"] == "moonshot"
    )
    moonshot["github"]["model_labels"] = {label: target}
    with pytest.raises(generator.CatalogError, match=message):
        generator._validate_manifest(manifest)


def test_model_label_cannot_target_an_ineligible_model() -> None:
    manifest, generator = _manifest_and_generator()
    moonshot = next(
        provider for provider in manifest["providers"] if provider["id"] == "moonshot"
    )
    k3 = next(
        model
        for model in moonshot["models"]
        if model["csv"]["model"] == "moonshot/kimi-k3"
    )
    k3["byok_eligible"] = False
    with pytest.raises(generator.CatalogError, match="targets an ineligible model"):
        generator._validate_manifest(manifest)


def test_byok_model_base_url_must_be_a_fixed_https_api_base() -> None:
    manifest, generator = _manifest_and_generator()
    moonshot = next(
        provider for provider in manifest["providers"] if provider["id"] == "moonshot"
    )
    k3 = next(
        model
        for model in moonshot["models"]
        if model["csv"]["model"] == "moonshot/kimi-k3"
    )
    k3["csv"]["base_url"] = "http://attacker.invalid/v1"
    with pytest.raises(generator.CatalogError, match="fixed HTTPS API base URL"):
        generator._validate_manifest(manifest)


def test_catalog_model_orders_are_globally_unique() -> None:
    manifest, generator = _manifest_and_generator()
    first, second = manifest["providers"][0]["models"][:2]
    second["order"] = first["order"]
    with pytest.raises(generator.CatalogError, match="Duplicate catalog model order"):
        generator._validate_manifest(manifest)


def test_cloud_csv_projection_tracks_the_current_gemini_default() -> None:
    manifest, generator = _manifest_and_generator()
    generator._validate_manifest(manifest)
    first = manifest["cloud_csv"][0]
    assert first == {
        "provider": "Google",
        "model": "vertex_ai/gemini-3.6-flash",
        "input": "1.5",
        "output": "7.5",
        "coding_arena_elo": "",
        "base_url": "",
        "api_key": "VERTEX_CREDENTIALS",
        "max_reasoning_tokens": "0",
        "structured_output": "True",
        "reasoning_type": "effort",
        "location": "global",
    }


def test_bootstrap_preserves_the_kimi_strict_label_contract() -> None:
    bootstrap = _load_module(BOOTSTRAP, "provider_catalog_bootstrap")
    moonshot = bootstrap.PROFILES["Moonshot AI"]
    assert moonshot["github"] == {
        "label": "pdd-moonshot",
        "model_labels": {"pdd-kimi": "moonshot/kimi-k3"},
        "execution_profile": "opencode_openai_chat",
        "eligible": True,
        "reason": "",
    }
