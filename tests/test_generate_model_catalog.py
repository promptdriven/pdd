"""Tests for agentic score-manifest catalog generation."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from pdd import generate_model_catalog as gmc  # noqa: E402


def _manifest(scores):
    expanded = []
    for score in scores:
        entry = {
            "source_url": "https://example.test/lmarena",
            "raw_model_name": score.get("model", "test-model"),
            "leaderboard": "webdev",
            "category": "overall",
            "leaderboard_publish_date": "2026-04-28",
            "retrieved_at": "2026-04-29",
            "rank": 1,
            "rating": score.get("elo", 1400),
            "rating_lower": score.get("elo", 1400) - 10,
            "rating_upper": score.get("elo", 1400) + 10,
            "vote_count": score.get("votes", score.get("vote_count", 10)),
            "match_reason": "test reviewed alias",
        }
        entry.update(score)
        expanded.append(entry)
    return {
        "schema_version": gmc.AGENTIC_ELO_MANIFEST_SCHEMA_VERSION,
        "policy": {"summary": "test"},
        "scores": expanded,
    }


def test_module_exports_agentic_manifest_surface():
    required = [
        "AGENTIC_ELO_MANIFEST_PATH",
        "AGENTIC_ELO_MANIFEST_SCHEMA_VERSION",
        "ARENA_LEADERBOARD_POLICY",
        "STATIC_ELO_FALLBACK",
        "_parse_agentic_elo_manifest",
        "_fetch_arena_elo",
        "_normalize_model_name",
        "_get_elo",
        "build_rows",
        "main",
    ]
    missing = [name for name in required if not hasattr(gmc, name)]
    assert not missing


def test_manifest_file_is_checked_in_and_loadable():
    assert gmc.AGENTIC_ELO_MANIFEST_PATH.exists()
    index = gmc._fetch_arena_elo()
    assert index
    assert "claude-opus-4-7" in index
    assert index["claude-opus-4-7"]["elo"] >= 1500
    assert index["gpt-5-5"]["elo"] == 1450.0
    assert index["gpt-5-5-high"]["elo"] == 1500.0


def test_parse_agentic_manifest_indexes_reviewed_aliases():
    payload = _manifest([
        {
            "model": "gpt-5.2-codex",
            "elo": 1335,
            "votes": 12,
            "source": "agent-reviewed:test",
            "aliases": ["chatgpt/gpt-5.2-codex", "gpt-5-2-codex"],
        }
    ])

    index = gmc._parse_agentic_elo_manifest(payload)

    assert index["gpt-5-2-codex"]["elo"] == 1335.0
    assert index["gpt-5-2-codex"]["source"] == "agent-reviewed:test"
    assert index["gpt-5-2-codex"]["raw_name"] == "gpt-5.2-codex"


def test_parse_agentic_manifest_requires_auditable_provenance():
    payload = {
        "schema_version": gmc.AGENTIC_ELO_MANIFEST_SCHEMA_VERSION,
        "policy": {"summary": "test"},
        "scores": [
            {
                "model": "gpt-5",
                "elo": 1393,
                "source": "agent-reviewed:test",
            }
        ],
    }

    assert gmc._parse_agentic_elo_manifest(payload) == {}


def test_parse_agentic_manifest_rejects_conflicting_alias_collisions():
    payload = _manifest([
        {
            "model": "gpt-5.5-high",
            "elo": 1500,
            "source": "agent-reviewed:test",
            "raw_model_name": "gpt-5.5-high (codex-harness)",
            "aliases": ["shared-alias"],
        },
        {
            "model": "gpt-5.5",
            "elo": 1450,
            "source": "agent-reviewed:test",
            "raw_model_name": "gpt-5.5 (codex-harness)",
            "aliases": ["shared-alias"],
        },
    ])

    assert gmc._parse_agentic_elo_manifest(payload) == {}


def test_reasoning_effort_variants_do_not_collapse():
    payload = _manifest([
        {
            "model": "gpt-5.5-high",
            "elo": 1500,
            "source": "agent-reviewed:test",
            "raw_model_name": "gpt-5.5-high (codex-harness)",
            "aliases": ["gpt-5.5-high (codex-harness)"],
        },
        {
            "model": "gpt-5.5",
            "elo": 1450,
            "source": "agent-reviewed:test",
            "raw_model_name": "gpt-5.5 (codex-harness)",
            "aliases": ["gpt-5.5 (codex-harness)"],
        },
    ])

    index = gmc._parse_agentic_elo_manifest(payload)

    assert gmc._normalize_model_name("gpt-5.5-high (codex-harness)") == "gpt-5-5-high"
    assert gmc._normalize_model_name("gpt-5.5 (codex-harness)") == "gpt-5-5"
    assert gmc._get_elo("gpt-5.5-high", index) == (1500, "arena-exact")
    assert gmc._get_elo("gpt-5.5", index) == (1450, "arena-exact")


def test_parse_agentic_manifest_rejects_wrong_schema_version():
    payload = _manifest([
        {"model": "gpt-5", "elo": 1393, "source": "agent-reviewed:test"}
    ])
    payload["schema_version"] = 999

    assert gmc._parse_agentic_elo_manifest(payload) == {}


def test_fetch_arena_elo_uses_manifest_without_optional_fetch_deps(tmp_path, monkeypatch):
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps(_manifest([
        {
            "model": "claude-opus-4-7",
            "elo": 1565,
            "source": "agent-reviewed:test",
        }
    ])), encoding="utf-8")
    monkeypatch.setitem(sys.modules, "huggingface_hub", None)
    monkeypatch.setitem(sys.modules, "pyarrow", None)
    monkeypatch.setitem(sys.modules, "rapidfuzz", None)

    index = gmc._fetch_arena_elo(manifest_path=manifest)

    assert index["claude-opus-4-7"]["elo"] == 1565.0


def test_fetch_arena_elo_rejects_python_refresh(tmp_path):
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps(_manifest([
        {
            "model": "claude-opus-4-7",
            "elo": 1565,
            "source": "agent-reviewed:test",
        }
    ])), encoding="utf-8")

    with pytest.raises(RuntimeError, match="not a Python live-fetch path"):
        gmc._fetch_arena_elo(refresh=True, manifest_path=manifest)


def test_cli_refresh_elo_exits_with_agentic_instruction(tmp_path):
    output = tmp_path / "llm_model.csv"

    result = subprocess.run(
        [
            sys.executable,
            str(_ROOT / "pdd" / "generate_model_catalog.py"),
            "--refresh-elo",
            "--output",
            str(output),
        ],
        cwd=_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == 2
    assert "not a Python live-fetch path" in result.stderr


def test_fetch_arena_elo_missing_manifest_gracefully_falls_back(tmp_path):
    missing = tmp_path / "missing.json"

    assert gmc._fetch_arena_elo(manifest_path=missing) == {}


def test_get_elo_agentic_manifest_wins_over_static_fallback():
    arena = {
        "claude-opus-4-6": {
            "elo": 1548.0,
            "votes": 0,
            "raw_name": "claude-opus-4-6",
        }
    }

    elo, source = gmc._get_elo("claude-opus-4-6", arena)

    assert elo == 1548
    assert source == "arena-exact"
    assert gmc.STATIC_ELO_FALLBACK["claude-opus-4-6"] != 1548


def test_get_elo_falls_back_to_static_when_manifest_has_no_match():
    elo, source = gmc._get_elo("gpt-4.1", {})

    assert elo == gmc.STATIC_ELO_FALLBACK["gpt-4.1"]
    assert source == "static"


def test_normalize_model_name_handles_provider_noise():
    assert gmc._normalize_model_name("openrouter/anthropic/claude-opus-4.7") == "claude-opus-4-7"
    assert gmc._normalize_model_name("azure/global/gpt-5.1-codex-mini") == "gpt-5-1-codex-mini"
    assert gmc._normalize_model_name("fireworks_ai/glm-4p7") == "glm-4-7"
    assert gmc._normalize_model_name("gemini-3-flash (thinking-minimal)") == "gemini-3-flash-thinking-minimal"


def test_build_rows_does_not_generate_chatgpt_from_model_cost(monkeypatch):
    """chatgpt/* must never be GENERATED from litellm.model_cost (chatgpt stays in
    _SKIP_PROVIDER_ROOTS) — but the hand-managed subscription family IS preserved
    via _merge_chatgpt_subscription_rows (issue #1269). So: no chatgpt row sourced
    from model_cost, yet the 4 curated chatgpt/ rows are present."""
    fake_cost = {
        "chatgpt/gpt-5.2": {
            "mode": "responses",
            "input_cost_per_token": 0.0,
            "output_cost_per_token": 0.0,
            "litellm_provider": "chatgpt",
            "supports_function_calling": True,
        },
        "gpt-5": {
            "mode": "chat",
            "input_cost_per_token": 1e-6,
            "output_cost_per_token": 1e-6,
            "litellm_provider": "openai",
            "supports_function_calling": True,
        },
    }
    fake_litellm = type("L", (), {"model_cost": fake_cost})
    monkeypatch.setitem(sys.modules, "litellm", fake_litellm)
    monkeypatch.setattr(gmc, "_fetch_arena_elo", lambda **_kw: {
        "gpt-5": {"elo": 1393.0, "votes": 0, "raw_name": "gpt-5"},
        "gpt-5-2": {"elo": 1404.0, "votes": 0, "raw_name": "gpt-5.2"},
    })

    rows = gmc.build_rows()

    assert rows
    # the model_cost chatgpt/gpt-5.2 (provider "chatgpt") must NOT be generated...
    assert not any(r.get("provider") == "chatgpt" for r in rows)
    # ...but the curated subscription family IS preserved (provider "OpenAI ChatGPT")
    chatgpt_rows = {r["model"] for r in rows if r["model"].startswith("chatgpt/")}
    assert chatgpt_rows == {
        "chatgpt/gpt-5.4", "chatgpt/gpt-5.3-codex",
        "chatgpt/gpt-5.2", "chatgpt/gpt-5.3-codex-spark",
    }
    assert all(
        r["provider"] == "OpenAI ChatGPT"
        for r in rows if r["model"].startswith("chatgpt/")
    )


def test_build_rows_accepts_custom_score_manifest(tmp_path, monkeypatch):
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps(_manifest([
        {
            "model": "gpt-5",
            "elo": 1777,
            "source": "agent-reviewed:test",
        }
    ])), encoding="utf-8")
    fake_cost = {
        "gpt-5": {
            "mode": "chat",
            "input_cost_per_token": 1e-6,
            "output_cost_per_token": 1e-6,
            "litellm_provider": "openai",
            "supports_function_calling": True,
        },
    }
    fake_litellm = type("L", (), {"model_cost": fake_cost})
    monkeypatch.setitem(sys.modules, "litellm", fake_litellm)

    rows = gmc.build_rows(score_manifest=manifest)

    row = next(r for r in rows if r["model"] == "gpt-5")
    assert row["coding_arena_elo"] == 1777


def test_local_runner_default_survives_when_score_known(monkeypatch):
    monkeypatch.setattr(gmc, "_fetch_arena_elo", lambda **_kw: {})

    rows = gmc.build_rows()

    assert any(r["model"] == "lm_studio/qwen3-coder-next" for r in rows)


def test_build_rows_includes_vertex_gemini_flash_ci_default(monkeypatch):
    fake_litellm = type("L", (), {"model_cost": {
        "vertex_ai/zai-org/glm-4.7-maas": {
            "mode": "chat",
            "input_cost_per_token": 0.6e-6,
            "output_cost_per_token": 2.2e-6,
            "litellm_provider": "vertex_ai",
            "supports_function_calling": True,
        },
    }})
    monkeypatch.setitem(sys.modules, "litellm", fake_litellm)
    monkeypatch.setattr(gmc, "_fetch_arena_elo", lambda **_kw: {})

    rows = gmc.build_rows()

    row = next(
        r for r in rows
        if r["model"] == "vertex_ai/gemini-3-flash-preview"
    )
    assert row["provider"] == "Google Vertex AI"
    assert row["api_key"] == "GOOGLE_APPLICATION_CREDENTIALS|VERTEXAI_PROJECT|VERTEXAI_LOCATION"
    assert row["location"] == "global"


def test_committed_csv_has_curated_chatgpt_subscription_rows():
    """The committed CSV carries the hand-managed ChatGPT subscription family
    (issue #1269): 4 chatgpt/ rows under provider "OpenAI ChatGPT", empty api_key
    (device-flow / codex login). They must NOT be the OPENAI_API_KEY-billed rows."""
    csv_path = _ROOT / "pdd" / "data" / "llm_model.csv"
    text = csv_path.read_text(encoding="utf-8")

    for model in (
        "chatgpt/gpt-5.4", "chatgpt/gpt-5.3-codex",
        "chatgpt/gpt-5.2", "chatgpt/gpt-5.3-codex-spark",
    ):
        assert f"OpenAI ChatGPT,{model},0.0,0.0," in text, model
    # subscription rows carry NO API key (device-flow / codex login). The cloud
    # deploy guard only rejects literal OPENAI_API_KEY rows; these chatgpt/ rows
    # are not those.
    for line in text.splitlines():
        if line.startswith("OpenAI ChatGPT,chatgpt/"):
            fields = line.split(",")
            assert fields[6] == "", f"chatgpt row must have empty api_key: {line!r}"


def test_committed_csv_includes_vertex_gemini_flash_ci_default():
    csv_path = _ROOT / "pdd" / "data" / "llm_model.csv"
    text = csv_path.read_text(encoding="utf-8")

    assert "Google Vertex AI,vertex_ai/gemini-3-flash-preview," in text


# ==============================================================================
# Regression tests: adaptive reasoning_type classification for Opus 4.7
#
# Anthropic enforced the new adaptive thinking API for Claude Opus 4.7 on
# 2026-05-23 ~17:25 UTC; the legacy thinking.type.enabled shape now 400s.
# The generator must classify direct-Anthropic-provider Opus 4.7 rows as
# adaptive (the consumer ``llm_invoke.py`` gates adaptive serialization on
# ``provider_lower == 'anthropic'``). Azure AI / Bedrock / Vertex relays
# stay on budget/effort pending a separate audit.
# ==============================================================================


def test_infer_reasoning_type_returns_adaptive_for_opus_47_anthropic():
    entry = {"supports_reasoning": True}
    assert gmc._infer_reasoning_type("claude-opus-4-7", "anthropic", entry) == "adaptive"


def test_infer_reasoning_type_returns_budget_for_opus_47_azure_ai():
    """Azure AI relay isn't audited for adaptive shape yet — keep at budget."""
    entry = {"supports_reasoning": True}
    assert gmc._infer_reasoning_type("azure_ai/claude-opus-4-7", "azure_ai", entry) == "budget"


def test_infer_reasoning_type_returns_budget_for_other_anthropic_models():
    """Models not in the adaptive allowlist stay on budget."""
    entry = {"supports_reasoning": True}
    assert gmc._infer_reasoning_type("claude-sonnet-4-6", "anthropic", entry) == "budget"


def test_infer_max_reasoning_tokens_returns_16000_for_opus_47_anthropic():
    """Adaptive serialization doesn't read this value, but match the
    validated pdd_cloud backend CSV (16000)."""
    entry = {"supports_reasoning": True}
    assert gmc._infer_max_reasoning_tokens("claude-opus-4-7", "anthropic", entry) == 16000


def test_infer_max_reasoning_tokens_returns_128000_for_other_anthropic_models():
    """Budget-mode default for non-adaptive Anthropic rows."""
    entry = {"supports_reasoning": True}
    assert gmc._infer_max_reasoning_tokens("claude-sonnet-4-6", "anthropic", entry) == 128000


# ==============================================================================
# Claude Opus 4.8 — same adaptive-thinking contract as 4.7 (released 2026-05-28).
# 4.8 is adaptive-thinking-only: thinking={"type":"adaptive"} + effort; the
# legacy thinking.type="enabled" budget shape 400s. Because 4.8 is brand new it
# has no live arena ELO yet, so it relies on a STATIC_ELO_FALLBACK seed to
# survive the documented catalog regen.
# ==============================================================================


def test_infer_reasoning_type_returns_adaptive_for_opus_48_anthropic():
    entry = {"supports_reasoning": True}
    assert gmc._infer_reasoning_type("claude-opus-4-8", "anthropic", entry) == "adaptive"


def test_infer_reasoning_type_returns_budget_for_opus_48_azure_ai():
    """Azure AI relay isn't audited for adaptive shape yet — keep at budget."""
    entry = {"supports_reasoning": True}
    assert gmc._infer_reasoning_type("azure_ai/claude-opus-4-8", "azure_ai", entry) == "budget"


def test_infer_max_reasoning_tokens_returns_16000_for_opus_48_anthropic():
    entry = {"supports_reasoning": True}
    assert gmc._infer_max_reasoning_tokens("claude-opus-4-8", "anthropic", entry) == 16000


def test_opus_48_static_elo_seed_clears_cutoff():
    """No live arena entry yet → a STATIC_ELO_FALLBACK seed must resolve the
    ELO above ELO_CUTOFF (the property we depend on; the source label may
    change to 'arena' once the model is listed live)."""
    elo, _source = gmc._get_elo("claude-opus-4-8", {})
    assert elo >= gmc.ELO_CUTOFF


def test_opus_48_is_seeded_when_litellm_unaware():
    """litellm.model_cost has no claude-opus-4-8 entry until litellm ships it,
    so the litellm-driven build loop would drop the row. It must be carried by
    _MANDATORY_MODEL_ROWS and survive _mandatory_rows_missing_from (ELO from the
    static seed clears the cutoff), with reasoning_type='adaptive'."""
    from collections import defaultdict

    seeded = gmc._mandatory_rows_missing_from(
        rows=[], arena_index={}, elo_source_counts=defaultdict(int)
    )
    by_model = {r["model"]: r for r in seeded}
    assert "claude-opus-4-8" in by_model, (
        "claude-opus-4-8 must be seeded when litellm is unaware of it"
    )
    row = by_model["claude-opus-4-8"]
    assert row["reasoning_type"] == "adaptive"
    assert row["api_key"] == "ANTHROPIC_API_KEY"
    assert row["coding_arena_elo"] >= gmc.ELO_CUTOFF


def test_opus_48_mandatory_row_deduped_once_litellm_knows_it():
    """When the catalog already contains a claude-opus-4-8 row (e.g. once
    litellm registers it), the mandatory seed must not duplicate it."""
    from collections import defaultdict

    seeded = gmc._mandatory_rows_missing_from(
        rows=[{"model": "claude-opus-4-8"}],
        arena_index={},
        elo_source_counts=defaultdict(int),
    )
    assert all(r["model"] != "claude-opus-4-8" for r in seeded)


def test_opus_48_bedrock_and_vertex_relays_seeded_when_litellm_unaware():
    """Opus 4.8 is available on Bedrock/Vertex at launch, but litellm doesn't
    ship those ids yet, so they must be carried by _MANDATORY_MODEL_ROWS too.
    Relays are NOT on the direct-Anthropic adaptive enforcement path, so they
    seed reasoning_type='effort' (mirroring the opus-4-7 relay rows), and their
    ELO must clear the cutoff via the static-prefix fallback."""
    from collections import defaultdict

    seeded = gmc._mandatory_rows_missing_from(
        rows=[], arena_index={}, elo_source_counts=defaultdict(int)
    )
    by_model = {r["model"]: r for r in seeded}

    bedrock = by_model.get("anthropic.claude-opus-4-8")
    assert bedrock is not None, "Bedrock opus-4-8 must be seeded"
    assert bedrock["reasoning_type"] == "effort"
    assert bedrock["api_key"] == "AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME"
    assert bedrock["coding_arena_elo"] >= gmc.ELO_CUTOFF

    vertex = by_model.get("vertex_ai/claude-opus-4-8")
    assert vertex is not None, "Vertex opus-4-8 must be seeded"
    assert vertex["reasoning_type"] == "effort"
    assert vertex["coding_arena_elo"] >= gmc.ELO_CUTOFF


def test_opus_48_relays_deduped_once_litellm_knows_them():
    """Once litellm registers the relay ids, the mandatory seed must not
    duplicate them."""
    from collections import defaultdict

    seeded = gmc._mandatory_rows_missing_from(
        rows=[
            {"model": "anthropic.claude-opus-4-8"},
            {"model": "vertex_ai/claude-opus-4-8"},
        ],
        arena_index={},
        elo_source_counts=defaultdict(int),
    )
    seeded_models = {r["model"] for r in seeded}
    assert "anthropic.claude-opus-4-8" not in seeded_models
    assert "vertex_ai/claude-opus-4-8" not in seeded_models


def test_infer_reasoning_type_returns_effort_for_opus_48_bedrock_and_vertex():
    """Relay Opus 4.8 stays on 'effort' (not adaptive) — only direct-Anthropic
    is on the adaptive enforcement path."""
    entry = {"supports_reasoning": True}
    assert gmc._infer_reasoning_type("anthropic.claude-opus-4-8", "bedrock", entry) == "effort"
    assert gmc._infer_reasoning_type("vertex_ai/claude-opus-4-8", "vertex_ai", entry) == "effort"


def test_azure_opus_48_is_deferred_even_when_litellm_knows_it(monkeypatch):
    """Azure AI / Foundry Opus 4.8 is intentionally deferred pending validation
    (it rides the legacy budget shape via AzureAIStudioConfig, which the adaptive
    relay patches don't reach). The deferral must be ENFORCED by the generator,
    not just documented: even when LiteLLM's registry ships azure_ai/claude-opus-4-8,
    a regen must omit it so the generator never diverges from the committed CSV
    (which deliberately has no Azure 4.8 row)."""
    import litellm

    fake_id = "azure_ai/claude-opus-4-8"
    monkeypatch.setitem(
        litellm.model_cost,
        fake_id,
        {
            "mode": "chat",
            "litellm_provider": "azure_ai",
            "input_cost_per_token": 5e-6,
            "output_cost_per_token": 25e-6,
            "max_tokens": 128000,
            "max_input_tokens": 200000,
            "supports_reasoning": True,
        },
    )
    # Sanity: the fake entry is actually visible to the build loop.
    assert fake_id in litellm.model_cost

    rows = gmc.build_rows(refresh_elo=False)
    assert all(r.get("model") != fake_id for r in rows), (
        "azure_ai/claude-opus-4-8 is deferred pending validation and must not be "
        "emitted by a regen even when LiteLLM knows the id"
    )
    # The direct-Anthropic 4.8 row must still be present (deferral is scoped).
    assert any(r.get("model") == "claude-opus-4-8" for r in rows)
