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


def test_build_rows_skips_chatgpt_provider(monkeypatch):
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
    assert all(not r["model"].startswith("chatgpt/") for r in rows)


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


def test_committed_csv_has_no_chatgpt_rows():
    csv_path = Path("pdd/data/llm_model.csv")
    text = csv_path.read_text(encoding="utf-8")

    assert "chatgpt/" not in text
    assert "ChatGPT," not in text


def test_committed_csv_includes_vertex_gemini_flash_ci_default():
    csv_path = Path("pdd/data/llm_model.csv")
    text = csv_path.read_text(encoding="utf-8")

    assert "Google Vertex AI,vertex_ai/gemini-3-flash-preview," in text
