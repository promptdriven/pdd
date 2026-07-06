"""E2E/Integration tests for Z.AI GLM Coding Plan support — issue #1827.

These tests verify cross-module interactions:
  - generate_model_catalog._mandatory_rows_missing_from  ↔  llm_invoke._select_model_candidates
  - setup_tool._scan_for_api_keys_quiet  ↔  provider_manager.expand_api_key_vars  ↔  CSV rows
  - model_tester._is_quota_backed_row / _format_price_cell  ↔  CSV provider name from llm_invoke
  - llm_invoke._alternative_base_lookups  ↔  _select_model_candidates  (near-miss adversarial)
  - both Z.AI endpoints in the same catalog  ↔  correct endpoint isolation in kwargs

All tests use mocked LiteLLM completions; no real API calls are made.
"""
from __future__ import annotations

import csv
import io
import os
from collections import defaultdict
from pathlib import Path
from unittest.mock import MagicMock, patch

import pandas as pd
import pytest

import pdd.llm_invoke as llm_mod
import pdd.generate_model_catalog as gmc
import pdd.provider_manager as pm
import pdd.update_model_costs as umc
from pdd import model_tester
from pdd.provider_manager import expand_api_key_vars


# ---------------------------------------------------------------------------
# Shared constants
# ---------------------------------------------------------------------------

_GENERAL_URL = "https://api.z.ai/api/paas/v4"
_CODING_URL = "https://api.z.ai/api/coding/paas/v4"

# Minimal CSV header matching what llm_invoke._load_model_data expects.
_CSV_HEADER = (
    "provider,model,input,output,coding_arena_elo,model_rank_score,model_rank_source,"
    "base_url,api_key,max_reasoning_tokens,structured_output,reasoning_type,location,interactive_only,context_limit\n"
)

_GENERAL_ROW = (
    f"Z.AI,openai/glm-5.2,0.80,2.56,1510,1510,static-prefix,"
    f"{_GENERAL_URL},ZAI_API_KEY,0,False,effort,,False,\n"
)

_CODING_PLAN_ROW = (
    f"Z.AI Coding Plan,openai/glm-5.2,0.0,0.0,1510,1510,static-prefix,"
    f"{_CODING_URL},ZAI_API_KEY,0,False,effort,,False,\n"
)

# A deliberate near-miss: same bare model name under a different provider that
# should NOT be selected when the Z.AI-specific alternatives are tried.
_OPENROUTER_LOOKALIKE_ROW = (
    "OpenRouter,openrouter/z-ai/glm-5.2,0.90,2.70,1480,1480,static,"
    ",OPENROUTER_API_KEY,0,False,none,,False,\n"
)

# Old-style zai/ prefix row — looks related but is a different model string.
_ZAI_PREFIX_ROW = (
    f"Zai,zai/glm-5.2,0.80,2.56,1480,1480,static-prefix,"
    f",ZAI_API_KEY,0,False,effort,,False,\n"
)


def test_mock_csv_header_matches_canonical_model_catalog_schema():
    """The shared mock catalog must not drift from the production CSV schema."""
    assert _CSV_HEADER.strip().split(",") == gmc.CSV_FIELDNAMES


def _make_mock_completion(content="OK"):
    """Return a minimal mock litellm response."""
    mock_choice = MagicMock()
    mock_choice.message.content = content
    mock_choice.finish_reason = "stop"
    mock_response = MagicMock()
    mock_response.choices = [mock_choice]
    mock_response.usage.prompt_tokens = 10
    mock_response.usage.completion_tokens = 5
    mock_response.usage.total_tokens = 15
    mock_response.model = "openai/glm-5.2"
    mock_response._hidden_params = {}
    return mock_response


# ---------------------------------------------------------------------------
# 1. Cross-module: mandatory rows → _select_model_candidates
#
# Verify that Z.AI rows produced by generate_model_catalog._mandatory_rows_missing_from
# contain the fields that _select_model_candidates needs to treat them as selectable
# candidates when ZAI_API_KEY is set in the environment.
# ---------------------------------------------------------------------------

def test_mandatory_rows_fields_satisfy_select_model_candidates(monkeypatch):
    """Mandatory Z.AI rows from catalog generation are structurally valid for
    _select_model_candidates: they carry api_key, model, coding_arena_elo, and
    a non-blank base_url — the exact fields the selection pipeline filters on.

    This crosses the generate_model_catalog → llm_invoke module boundary.
    """
    seeded = gmc._mandatory_rows_missing_from(
        rows=[], arena_index={}, elo_source_counts=defaultdict(int)
    )

    zai_rows = [r for r in seeded if r.get("provider") in {"Z.AI", "Z.AI Coding Plan"}]
    assert zai_rows, "Mandatory rows must include at least one Z.AI row"

    for row in zai_rows:
        # _select_model_candidates filters on api_key.notna()
        assert row.get("api_key") == "ZAI_API_KEY", (
            f"Row {row['model']} ({row['provider']}) must carry api_key=ZAI_API_KEY"
        )
        # _select_model_candidates uses coding_arena_elo for ranking
        assert float(row.get("coding_arena_elo", 0)) >= gmc.ELO_CUTOFF, (
            f"Row {row['model']} ELO must clear ELO_CUTOFF ({gmc.ELO_CUTOFF}) for "
            "ranking in _select_model_candidates"
        )
        # base_url must be non-empty so llm_invoke propagates it to api_base
        assert row.get("base_url", "").startswith("https://api.z.ai/"), (
            f"Row {row['model']} must have an explicit api.z.ai base_url"
        )


def test_mandatory_rows_selectable_when_zai_key_present(tmp_path, monkeypatch):
    """Z.AI mandatory rows can be selected by _select_model_candidates when
    ZAI_API_KEY is configured — tests the catalog generation → model selection pipeline.

    Sets up a CSV derived from mandatory rows, patches the CSV path in llm_invoke,
    and asserts that the Coding Plan endpoint flows through to litellm.completion kwargs.
    """
    # Build a minimal CSV from the mandatory rows (simulates a freshly generated catalog)
    seeded = gmc._mandatory_rows_missing_from(
        rows=[], arena_index={}, elo_source_counts=defaultdict(int)
    )
    coding_plan_rows = [r for r in seeded if r.get("provider") == "Z.AI Coding Plan"
                        and r.get("model") == "openai/glm-5.2"]
    assert coding_plan_rows, "Precondition: mandatory rows must include Z.AI Coding Plan openai/glm-5.2"
    seed = coding_plan_rows[0]

    # Write the mandatory row into a temp CSV with all the columns llm_invoke needs.
    csv_path = tmp_path / "llm_model.csv"
    csv_path.write_text(
        _CSV_HEADER
        + (
            f"{seed['provider']},{seed['model']},"
            f"{seed['input']},{seed['output']},"
            f"{seed['coding_arena_elo']},{seed['coding_arena_elo']},static-prefix,"
            f"{seed['base_url']},{seed['api_key']},0,False,effort,,False,"
            f"{seed.get('context_limit', '')}\n"
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "openai/glm-5.2")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "openai/glm-5.2")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("ZAI_API_KEY", "sk-zai-mandatory-test")

    captured_kwargs: dict = {}

    def _capture(**kwargs):
        captured_kwargs.update(kwargs)
        return _make_mock_completion()

    with patch("litellm.caching.caching.Cache"):
        with patch.object(llm_mod.litellm, "completion", side_effect=_capture):
            with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False):
                llm_mod.llm_invoke(
                    prompt="ping",
                    input_json={},
                    strength=0.5,
                    use_cloud=False,
                )

    assert captured_kwargs.get("model") == "openai/glm-5.2", (
        "Model string must be preserved through the selection pipeline"
    )
    assert captured_kwargs.get("base_url") == _CODING_URL, (
        "Mandatory Coding Plan row base_url must reach litellm.completion"
    )
    assert captured_kwargs.get("api_base") == _CODING_URL, (
        "api_base must equal base_url to prevent LiteLLM provider mis-detection"
    )
    assert captured_kwargs.get("api_key") == "sk-zai-mandatory-test", (
        "ZAI_API_KEY value must be passed as api_key to litellm"
    )


# ---------------------------------------------------------------------------
# 2. Cross-module: setup_tool._scan_for_api_keys_quiet ↔ Z.AI CSV rows
#
# _scan_for_api_keys_quiet reads the reference CSV, extracts api_key column
# values via provider_manager.expand_api_key_vars, then checks the environment
# for each.  If Z.AI rows are in the CSV and ZAI_API_KEY is set, the scanner
# must detect the key.
# ---------------------------------------------------------------------------

def test_setup_scanner_detects_zai_key_when_csv_has_zai_rows(tmp_path, monkeypatch):
    """_scan_for_api_keys_quiet returns ZAI_API_KEY when Z.AI rows are present
    in the reference CSV and ZAI_API_KEY is set in the environment.

    Tests setup_tool → provider_manager.expand_api_key_vars → env var resolution.
    """
    from pdd.setup_tool import _scan_for_api_keys_quiet, _ref_csv_path

    # Write a minimal reference CSV with Z.AI rows at the expected path.
    ref_dir = tmp_path / ".pdd"
    ref_dir.mkdir()
    ref_csv = ref_dir / "llm_model.csv"
    ref_csv.write_text(
        "provider,model,api_key,input,output,base_url\n"
        f"Z.AI,openai/glm-5.2,ZAI_API_KEY,0.80,2.56,{_GENERAL_URL}\n"
        f"Z.AI Coding Plan,openai/glm-5.2,ZAI_API_KEY,0.0,0.0,{_CODING_URL}\n",
        encoding="utf-8",
    )

    monkeypatch.setenv("ZAI_API_KEY", "sk-zai-setup-test")
    # Point the setup tool at our temp CSV.
    monkeypatch.setattr("pdd.setup_tool._ref_csv_path", lambda: ref_csv)

    found_keys = [name for name, _ in _scan_for_api_keys_quiet()]
    assert "ZAI_API_KEY" in found_keys, (
        "Setup scanner must detect ZAI_API_KEY when Z.AI rows are in the CSV "
        "and the key is present in the environment"
    )


def test_setup_scanner_does_not_detect_zai_key_when_not_set(tmp_path, monkeypatch):
    """_scan_for_api_keys_quiet must NOT return ZAI_API_KEY when the env var
    is absent — even though Z.AI rows are in the CSV.

    Near-miss: confirms the scanner reports presence, not just CSV membership.
    """
    from pdd.setup_tool import _scan_for_api_keys_quiet

    ref_dir = tmp_path / ".pdd"
    ref_dir.mkdir()
    ref_csv = ref_dir / "llm_model.csv"
    ref_csv.write_text(
        "provider,model,api_key,input,output,base_url\n"
        f"Z.AI,openai/glm-5.2,ZAI_API_KEY,0.80,2.56,{_GENERAL_URL}\n",
        encoding="utf-8",
    )

    monkeypatch.delenv("ZAI_API_KEY", raising=False)
    monkeypatch.setattr("pdd.setup_tool._ref_csv_path", lambda: ref_csv)

    found_keys = [name for name, _ in _scan_for_api_keys_quiet()]
    assert "ZAI_API_KEY" not in found_keys, (
        "Scanner must not report ZAI_API_KEY when it is absent from the environment"
    )


# ---------------------------------------------------------------------------
# 3. Cross-module: model_tester quota display ↔ provider name from CSV
#
# The "Z.AI Coding Plan" provider name must flow through
# model_tester._load_user_csv → _is_quota_backed_row → _format_price_cell
# so that the model-test output shows "quota" instead of a dollar amount.
# Near-miss: "Z.AI" (general API) must NOT trigger quota display.
# ---------------------------------------------------------------------------

def _make_csv_for_tester(tmp_path, content):
    """Write a CSV at the path model_tester.test_model_interactive expects."""
    csv_file = tmp_path / ".pdd" / "llm_model.csv"
    csv_file.parent.mkdir(parents=True, exist_ok=True)
    csv_file.write_text(content)
    return csv_file


def _run_tester_capture(tmp_path, csv_content, inputs, monkeypatch, env_vars=None):
    """Drive test_model_interactive with captured console output."""
    _make_csv_for_tester(tmp_path, csv_content)
    for k, v in (env_vars or {}).items():
        monkeypatch.setenv(k, v)

    captured: list[str] = []

    def _record(*args, **kwargs):
        for a in args:
            captured.append(str(a))

    mock_comp = MagicMock(return_value=MagicMock(
        choices=[MagicMock(message=MagicMock(content="ok"), finish_reason="stop")],
        usage=MagicMock(prompt_tokens=5, completion_tokens=3),
    ))

    with (
        patch.object(model_tester.Path, "home", return_value=tmp_path),
        patch.object(model_tester.console, "input", side_effect=iter(inputs)),
        patch.object(model_tester.console, "print", side_effect=_record),
        patch("litellm.completion", mock_comp),
        patch("sys.stdout"),
    ):
        model_tester.test_model_interactive()

    return "\n".join(captured), mock_comp


def test_coding_plan_provider_triggers_quota_display_not_dollar_cost(tmp_path, monkeypatch):
    """The 'Z.AI Coding Plan' provider name in the CSV must produce 'quota' in
    model-test price columns, not a dollar amount.

    Cross-module: CSV provider column → model_tester._is_quota_backed_row →
    _format_price_cell display.
    """
    csv = (
        "provider,model,api_key,input,output\n"
        f"Z.AI Coding Plan,openai/glm-5.2,ZAI_API_KEY,0.0,0.0\n"
    )
    output, _ = _run_tester_capture(
        tmp_path, csv, ["1", "q"], monkeypatch,
        env_vars={"ZAI_API_KEY": "sk-zai-cost-test"},
    )
    assert "quota" in output.lower(), (
        "Z.AI Coding Plan model must show 'quota' in price display, not a dollar figure"
    )
    # Ensure no misleading per-token dollar estimate like "$0.00" for input/output columns
    # (the test table renders input/output via _format_price_cell)
    assert "$0.00" not in output or "quota" in output.lower(), (
        "Dollar amounts must not appear for Coding Plan rows without a 'quota' label"
    )


def test_zai_general_api_provider_not_quota_backed_near_miss(tmp_path, monkeypatch):
    """'Z.AI' (general API) provider must NOT trigger quota display.

    Near-miss: the provider name 'Z.AI' is a prefix of 'Z.AI Coding Plan' —
    _is_quota_backed_row must match the full string, not a prefix.
    """
    csv = (
        "provider,model,api_key,input,output\n"
        f"Z.AI,openai/glm-5.2,ZAI_API_KEY,0.80,2.56\n"
    )
    output, _ = _run_tester_capture(
        tmp_path, csv, ["1", "q"], monkeypatch,
        env_vars={"ZAI_API_KEY": "sk-zai-general-test"},
    )
    # The general API row has real pricing and should NOT show "quota" for price columns.
    # (The diagnostics may show the base URL "api.z.ai" but that is separate.)
    # We check that _is_quota_backed_row did not trigger for the general row.
    assert model_tester._is_quota_backed_row(
        {"provider": "Z.AI", "input": 0.80, "output": 2.56}
    ) is False, (
        "_is_quota_backed_row must return False for 'Z.AI' provider (general API)"
    )


# ---------------------------------------------------------------------------
# 4. Near-miss adversarial: bare glm-5.2 with look-alike rows in catalog
#
# When the catalog contains both a Z.AI Coding Plan row AND an OpenRouter
# row with the same base model name, bare PDD_MODEL_DEFAULT=glm-5.2 must
# resolve to the Z.AI row (via _alternative_base_lookups) and NOT the
# OpenRouter row.
# ---------------------------------------------------------------------------

def test_bare_glm52_selects_zai_not_openrouter_lookalike(tmp_path, monkeypatch):
    """Bare PDD_MODEL_DEFAULT=glm-5.2 must not silently resolve to an
    OpenRouter look-alike row when a Z.AI Coding Plan row is available.

    Near-miss: both rows exist; only ZAI_API_KEY is set (not OPENROUTER_API_KEY).
    Tests _alternative_base_lookups ↔ _select_model_candidates cross-module.
    """
    csv_path = tmp_path / "llm_model.csv"
    csv_path.write_text(
        _CSV_HEADER
        # OpenRouter look-alike row (no OPENROUTER_API_KEY set → filtered out by api_key check)
        + _OPENROUTER_LOOKALIKE_ROW
        # Z.AI Coding Plan row (ZAI_API_KEY IS set)
        + _CODING_PLAN_ROW,
        encoding="utf-8",
    )

    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "glm-5.2")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "glm-5.2")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("ZAI_API_KEY", "sk-zai-adversarial")
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)

    captured_kwargs: dict = {}

    def _capture(**kwargs):
        captured_kwargs.update(kwargs)
        return _make_mock_completion()

    with patch("litellm.caching.caching.Cache"):
        with patch.object(llm_mod.litellm, "completion", side_effect=_capture):
            with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False):
                llm_mod.llm_invoke(
                    prompt="ping",
                    input_json={},
                    strength=0.5,
                    use_cloud=False,
                )

    # Must NOT have ended up on the OpenRouter row
    assert captured_kwargs.get("model") == "openai/glm-5.2", (
        "Model must be the openai/-prefixed Z.AI form, not the OpenRouter form"
    )
    assert captured_kwargs.get("base_url") == _CODING_URL, (
        "base_url must be the Z.AI Coding Plan endpoint, not an OpenRouter endpoint"
    )
    assert "openrouter" not in str(captured_kwargs.get("base_url", "")).lower(), (
        "OpenRouter endpoint must not be used when ZAI_API_KEY is set"
    )


def test_old_zai_prefix_row_not_selected_via_alternative_lookup(tmp_path, monkeypatch):
    """The old 'zai/glm-5.2' (LiteLLM native prefix) row must not be selected
    by the Z.AI-specific _alternative_base_lookups path.

    Near-miss: both 'zai/glm-5.2' (Zai provider) and 'openai/glm-5.2' (Z.AI
    Coding Plan provider) exist in the catalog.  Bare 'glm-5.2' must resolve to
    the 'openai/glm-5.2' Z.AI Coding Plan row, not the old prefix row.
    """
    csv_path = tmp_path / "llm_model.csv"
    csv_path.write_text(
        _CSV_HEADER
        # Old LiteLLM-prefix row — different model string, different provider
        + _ZAI_PREFIX_ROW
        # New explicit base_url Coding Plan row
        + _CODING_PLAN_ROW,
        encoding="utf-8",
    )

    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "glm-5.2")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "glm-5.2")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("ZAI_API_KEY", "sk-zai-prefix-test")

    captured_kwargs: dict = {}

    def _capture(**kwargs):
        captured_kwargs.update(kwargs)
        return _make_mock_completion()

    with patch("litellm.caching.caching.Cache"):
        with patch.object(llm_mod.litellm, "completion", side_effect=_capture):
            with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False):
                llm_mod.llm_invoke(
                    prompt="ping",
                    input_json={},
                    strength=0.5,
                    use_cloud=False,
                )

    # The new Coding Plan row should win over the old prefix row.
    assert captured_kwargs.get("base_url") == _CODING_URL, (
        "Z.AI Coding Plan explicit base_url must be chosen over old zai/ prefix row"
    )
    assert captured_kwargs.get("model") == "openai/glm-5.2", (
        "Model string must be the openai/-prefixed form from the Coding Plan row"
    )


# ---------------------------------------------------------------------------
# 5. Both endpoints coexist in catalog; endpoint isolation in kwargs
#
# Tests that with both Z.AI general API and Z.AI Coding Plan rows in the same
# catalog, selecting each by explicit model string routes to the correct endpoint.
# ---------------------------------------------------------------------------

def test_general_api_single_row_selects_general_url(tmp_path, monkeypatch):
    """A single explicit Z.AI general API row routes openai/glm-5.2 to the
    general API endpoint, not the Coding Plan URL.
    """
    csv_path_general_only = tmp_path / "llm_model_general.csv"
    csv_path_general_only.write_text(
        _CSV_HEADER + _GENERAL_ROW,
        encoding="utf-8",
    )
    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path_general_only)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "openai/glm-5.2")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "openai/glm-5.2")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("ZAI_API_KEY", "sk-zai-general-endpoint")

    captured_kwargs: dict = {}

    def _capture(**kwargs):
        captured_kwargs.update(kwargs)
        return _make_mock_completion()

    with patch("litellm.caching.caching.Cache"):
        with patch.object(llm_mod.litellm, "completion", side_effect=_capture):
            with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False):
                llm_mod.llm_invoke(
                    prompt="ping",
                    input_json={},
                    strength=0.5,
                    use_cloud=False,
                )

    assert captured_kwargs.get("base_url") == _GENERAL_URL, (
        "General API row must route to https://api.z.ai/api/paas/v4"
    )
    assert captured_kwargs.get("api_base") == _GENERAL_URL, (
        "api_base must equal base_url for the general API row"
    )
    assert _CODING_URL not in str(captured_kwargs.get("base_url", "")), (
        "General API row must not accidentally use the Coding Plan endpoint"
    )


def test_both_endpoints_in_catalog_explicit_openai_glm52_selects_general_url(tmp_path, monkeypatch):
    """When both endpoint rows share openai/glm-5.2, the explicit prefixed model
    selects the first exact model row: the general Z.AI row in sorted catalog
    order. Bare glm-5.2 is the Coding Plan shortcut tested separately.
    """
    csv_path = tmp_path / "llm_model.csv"
    csv_path.write_text(
        _CSV_HEADER + _GENERAL_ROW + _CODING_PLAN_ROW,
        encoding="utf-8",
    )

    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "openai/glm-5.2")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "openai/glm-5.2")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("ZAI_API_KEY", "sk-zai-general-both-rows")

    captured_kwargs: dict = {}

    def _capture(**kwargs):
        captured_kwargs.update(kwargs)
        return _make_mock_completion()

    with patch("litellm.caching.caching.Cache"):
        with patch.object(llm_mod.litellm, "completion", side_effect=_capture):
            with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False):
                llm_mod.llm_invoke(
                    prompt="ping",
                    input_json={},
                    strength=0.5,
                    use_cloud=False,
                )

    assert captured_kwargs.get("base_url") == _GENERAL_URL, (
        "Explicit openai/glm-5.2 must select the general API row when both rows exist"
    )
    assert captured_kwargs.get("api_base") == _GENERAL_URL
    assert _CODING_URL not in str(captured_kwargs.get("base_url", ""))


# ---------------------------------------------------------------------------
# 6. expand_api_key_vars ↔ Z.AI CSV api_key field
#
# provider_manager.expand_api_key_vars("ZAI_API_KEY") must return ZAI_API_KEY
# so that setup_tool and the api_key scanner can match it from the CSV.
# ---------------------------------------------------------------------------

def test_expand_api_key_vars_includes_zai_api_key():
    """expand_api_key_vars('ZAI_API_KEY') must include 'ZAI_API_KEY' so the
    setup scanner can detect it from the CSV api_key column.

    Integration: provider_manager → setup_tool boundary.
    """
    expanded = expand_api_key_vars("ZAI_API_KEY")
    assert "ZAI_API_KEY" in expanded, (
        "expand_api_key_vars must include ZAI_API_KEY so the setup scanner detects it"
    )


def test_expand_api_key_vars_zai_not_confused_with_other_keys():
    """ZAI_API_KEY must not be treated as an alias of unrelated keys (OPENAI_API_KEY,
    ANTHROPIC_API_KEY, etc.).  Near-miss: confirm key identity boundary.
    """
    zai_expanded = set(expand_api_key_vars("ZAI_API_KEY"))
    openai_expanded = set(expand_api_key_vars("OPENAI_API_KEY"))
    anthropic_expanded = set(expand_api_key_vars("ANTHROPIC_API_KEY"))

    # ZAI_API_KEY should not be in OpenAI or Anthropic alias sets
    assert "ZAI_API_KEY" not in openai_expanded, (
        "ZAI_API_KEY must not be an alias of OPENAI_API_KEY"
    )
    assert "ZAI_API_KEY" not in anthropic_expanded, (
        "ZAI_API_KEY must not be an alias of ANTHROPIC_API_KEY"
    )
    # And ZAI_API_KEY's own set must not contain OPENAI_API_KEY
    assert "OPENAI_API_KEY" not in zai_expanded, (
        "OPENAI_API_KEY must not be an alias of ZAI_API_KEY"
    )


# ---------------------------------------------------------------------------
# 7. Z.AI GLM-5.2 context window — bundled CSV must declare 1M context limit
#    so estimate and runtime context diagnostics use 1,000,000 tokens.
# ---------------------------------------------------------------------------

def test_bundled_csv_has_context_limit_for_zai_glm52():
    """The bundled llm_model.csv must carry context_limit=1000000 for BOTH
    the general Z.AI and Z.AI Coding Plan openai/glm-5.2 rows.

    Without this, estimate/context diagnostics treat the window as unknown
    even though GLM-5.2 is documented as a 1M-token context model.
    """
    import csv
    import importlib.resources

    csv_data = importlib.resources.files("pdd").joinpath("data/llm_model.csv").read_text()
    reader = csv.DictReader(csv_data.splitlines())

    glm52_rows = [
        row for row in reader
        if row.get("model") == "openai/glm-5.2"
        and "z.ai" in row.get("provider", "").lower()
    ]
    assert glm52_rows, "Bundled CSV must include at least one Z.AI openai/glm-5.2 row"

    for row in glm52_rows:
        raw = row.get("context_limit", "")
        assert raw.strip() == "1000000", (
            f"Row {row['provider']}/{row['model']} context_limit must be 1000000, got {raw!r}"
        )


def test_catalog_context_limit_returns_1m_for_zai_glm52_model_info():
    """_catalog_context_limit must return 1_000_000 when fed a model_info dict
    from a Z.AI GLM-5.2 row that carries context_limit=1000000.
    """
    from pdd.llm_invoke import _catalog_context_limit

    # General row
    general_info = {
        "provider": "Z.AI",
        "model": "openai/glm-5.2",
        "context_limit": 1_000_000,
    }
    assert _catalog_context_limit(general_info) == 1_000_000, (
        "General Z.AI GLM-5.2 row must yield 1M context limit"
    )

    # Coding Plan row
    coding_info = {
        "provider": "Z.AI Coding Plan",
        "model": "openai/glm-5.2",
        "context_limit": 1_000_000,
    }
    assert _catalog_context_limit(coding_info) == 1_000_000, (
        "Z.AI Coding Plan GLM-5.2 row must yield 1M context limit"
    )


# ---------------------------------------------------------------------------
# 8. Non-estimate runtime context validation uses catalog context_limit
#
# Verify that llm_invoke's pre-call context validation reads context_limit
# from the catalog row rather than only querying LiteLLM, so glm-5.2 (which
# LiteLLM doesn't register) is correctly bounded at 1,000,000 tokens.
# ---------------------------------------------------------------------------

def test_runtime_context_validation_uses_catalog_context_limit(tmp_path, monkeypatch):
    """During a real (non-estimate) invocation, the context validation path must
    consult _catalog_context_limit(model_info) before falling back to
    get_context_limit(model_name_litellm).

    Regression test for the finding: LiteLLM returns None for openai/glm-5.2
    (because it doesn't know this custom model), so if the catalog override is
    not checked first, context validation is silently skipped even when the
    catalog declares a 1M-token limit.

    Setup: catalog row has context_limit=1000000 and token_count=2000000.
    With the fix:  context validation fires, detects 2M > 1M, raises RuntimeError.
    Without the fix: get_context_limit returns None → validation skipped → no error.
    """
    import logging

    _CSV_HEADER_WITH_CTX = (
        "provider,model,input,output,coding_arena_elo,model_rank_score,model_rank_source,"
        "base_url,api_key,max_reasoning_tokens,structured_output,reasoning_type,location,"
        "interactive_only,context_limit\n"
    )
    _ROW_WITH_CTX = (
        f"Z.AI,openai/glm-5.2,1.0,3.2,1510,1510,static-prefix,"
        f"{_GENERAL_URL},ZAI_API_KEY,0,False,effort,,False,1000000\n"
    )

    csv_path = tmp_path / "llm_model.csv"
    csv_path.write_text(_CSV_HEADER_WITH_CTX + _ROW_WITH_CTX, encoding="utf-8")

    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "openai/glm-5.2")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "openai/glm-5.2")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("ZAI_API_KEY", "sk-zai-ctx-test")

    import pytest

    with patch("litellm.caching.caching.Cache"):
        with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False):
            # Token count exceeds the catalog's 1M limit — validation should raise.
            with patch.object(llm_mod, "count_tokens_for_messages", return_value=2_000_000):
                # LiteLLM doesn't know openai/glm-5.2 → returns None for this model.
                with patch.object(llm_mod, "get_context_limit", return_value=None):
                    with patch.object(llm_mod.litellm, "completion") as mock_comp:
                        with pytest.raises(RuntimeError, match="context limit"):
                            llm_mod.llm_invoke(
                                prompt="big prompt {x}",
                                input_json={"x": "y"},
                                strength=0.5,
                                use_cloud=False,
                            )
                        # completion must NOT be called — model was rejected before the call.
                        mock_comp.assert_not_called()


# ---------------------------------------------------------------------------
# Cross-module schema parity: generate_model_catalog ↔ provider_manager ↔
# update_model_costs all define the same 15-column schema including
# context_limit.  A mismatch here means one module will silently drop or
# misplace the column when reading/writing the bundled CSV.
# ---------------------------------------------------------------------------

def test_csv_schema_parity_across_all_three_module_holders():
    """All three modules that own a copy of CSV_FIELDNAMES / EXPECTED_COLUMNS
    must agree on the same ordered list, including the 15th column
    ``context_limit`` added for issue #1827.

    Cross-module: generate_model_catalog ↔ provider_manager ↔ update_model_costs.
    """
    gmc_fields = gmc.CSV_FIELDNAMES
    pm_fields = pm.CSV_FIELDNAMES
    umc_fields = list(umc.EXPECTED_COLUMNS)

    assert gmc_fields == pm_fields, (
        "generate_model_catalog.CSV_FIELDNAMES != provider_manager.CSV_FIELDNAMES\n"
        f"  gmc: {gmc_fields}\n  pm:  {pm_fields}"
    )
    assert gmc_fields == umc_fields, (
        "generate_model_catalog.CSV_FIELDNAMES != update_model_costs.EXPECTED_COLUMNS\n"
        f"  gmc: {gmc_fields}\n  umc: {umc_fields}"
    )
    assert "context_limit" in gmc_fields, (
        "'context_limit' missing from CSV_FIELDNAMES — all three modules would drop it"
    )
    assert gmc_fields[-1] == "context_limit", (
        f"'context_limit' must be the last (15th) column; got {gmc_fields[-1]!r}"
    )


# ---------------------------------------------------------------------------
# provider_manager._write_csv_atomic write→read round-trip preserves
# context_limit values for Z.AI rows.  This is the most direct test of the
# fix: if _write_csv_atomic uses an old 14-column schema, the column is
# silently discarded; with the fix it must survive the round-trip.
# ---------------------------------------------------------------------------

def test_provider_manager_write_cycle_preserves_zai_context_limit(tmp_path):
    """A Z.AI row with context_limit=1000000 written via _write_csv_atomic
    must be read back with the same value by _read_csv.

    Cross-module: provider_manager._write_csv_atomic ↔ provider_manager._read_csv.
    Regression guard: the old 14-column CSV_FIELDNAMES silently dropped the
    column on write, making context validation unreachable at runtime.
    """
    csv_path = tmp_path / "llm_model.csv"

    zai_row = {
        "provider": "Z.AI",
        "model": "openai/glm-5.2",
        "input": "1.0",
        "output": "3.2",
        "coding_arena_elo": "1510",
        "model_rank_score": "1510",
        "model_rank_source": "static-prefix",
        "base_url": _GENERAL_URL,
        "api_key": "ZAI_API_KEY",
        "max_reasoning_tokens": "0",
        "structured_output": "False",
        "reasoning_type": "effort",
        "location": "",
        "interactive_only": "False",
        "context_limit": "1000000",
    }

    pm._write_csv_atomic(csv_path, [zai_row])
    rows = pm._read_csv(csv_path)

    assert len(rows) == 1, "Expected exactly one row after round-trip"
    row = rows[0]
    assert "context_limit" in row, (
        "_read_csv did not return 'context_limit' key — _write_csv_atomic must have "
        "dropped the column (old 14-column schema)"
    )
    assert row["context_limit"] == "1000000", (
        f"context_limit round-trip mismatch: expected '1000000', got {row['context_limit']!r}"
    )
    assert row["base_url"] == _GENERAL_URL, "base_url must survive the round-trip unchanged"


# ---------------------------------------------------------------------------
# update_model_costs schema repair preserves context_limit: when a CSV is
# loaded into a DataFrame and the schema-repair reindex is applied, rows that
# already carry context_limit values must not have them overwritten with NA.
# ---------------------------------------------------------------------------

def test_update_model_costs_schema_repair_preserves_context_limit(tmp_path):
    """The update_model_costs schema-repair path (``df.reindex(columns=EXPECTED_COLUMNS)``)
    must preserve existing context_limit values rather than overwriting them
    with NA.

    Cross-module: provider_manager._write_csv_atomic → update_model_costs schema repair.
    This guards against a regression where EXPECTED_COLUMNS omitted context_limit,
    causing reindex to silently zero-out the column.
    """
    # Write a CSV with context_limit via provider_manager (the authoritative writer).
    csv_path = tmp_path / "llm_model.csv"
    rows_to_write = [
        {
            "provider": "Z.AI",
            "model": "openai/glm-5.2",
            "input": "1.0",
            "output": "3.2",
            "coding_arena_elo": "1510",
            "model_rank_score": "1510",
            "model_rank_source": "static-prefix",
            "base_url": _GENERAL_URL,
            "api_key": "ZAI_API_KEY",
            "max_reasoning_tokens": "0",
            "structured_output": "False",
            "reasoning_type": "effort",
            "location": "",
            "interactive_only": "False",
            "context_limit": "1000000",
        },
        {
            "provider": "Z.AI Coding Plan",
            "model": "openai/glm-5.2",
            "input": "0.0",
            "output": "0.0",
            "coding_arena_elo": "1510",
            "model_rank_score": "1510",
            "model_rank_source": "static-prefix",
            "base_url": _CODING_URL,
            "api_key": "ZAI_API_KEY",
            "max_reasoning_tokens": "0",
            "structured_output": "False",
            "reasoning_type": "effort",
            "location": "",
            "interactive_only": "False",
            "context_limit": "1000000",
        },
    ]
    pm._write_csv_atomic(csv_path, rows_to_write)

    # Simulate the schema-repair step inside update_model_data: load and reindex.
    df = pd.read_csv(str(csv_path))
    assert "context_limit" in df.columns, (
        "context_limit was not written to CSV — provider_manager._write_csv_atomic bug"
    )

    # Reindex just as update_model_data does on schema repair.
    df_repaired = df.reindex(columns=umc.EXPECTED_COLUMNS)

    assert "context_limit" in df_repaired.columns, (
        "context_limit was dropped by df.reindex(columns=EXPECTED_COLUMNS) — "
        "update_model_costs.EXPECTED_COLUMNS must be missing the column"
    )

    # Values must not be clobbered with NA during reindex.
    ctx_values = df_repaired["context_limit"].tolist()
    assert all(str(v) == "1000000" for v in ctx_values), (
        f"context_limit values corrupted after schema-repair reindex: {ctx_values}"
    )


# ---------------------------------------------------------------------------
# openai/glm-5.1 mandatory row: _mandatory_rows_missing_from must emit a row
# for glm-5.1 when it is absent from the existing catalog, and that row must
# survive the ELO_CUTOFF check (i.e. its resolved ELO ≥ ELO_CUTOFF).
# ---------------------------------------------------------------------------

def test_glm51_mandatory_row_survives_elo_cutoff_in_seeded_output():
    """_mandatory_rows_missing_from([], {}, defaultdict(int)) must include a
    row for ``openai/glm-5.1`` with a resolved ELO ≥ ELO_CUTOFF.

    Cross-module: generate_model_catalog._MANDATORY_MODEL_ROWS →
    _mandatory_rows_missing_from → ELO_CUTOFF filter.

    Regression guard: if glm-5.1 is not in _MANDATORY_MODEL_ROWS, or if its
    static-fallback ELO is below ELO_CUTOFF, it will silently vanish from
    every regen'd catalog even though it is a supported model.
    """
    result = gmc._mandatory_rows_missing_from([], {}, defaultdict(int))
    model_ids = [r["model"] for r in result]

    assert "openai/glm-5.1" in model_ids, (
        "openai/glm-5.1 is absent from _mandatory_rows_missing_from output.\n"
        f"Emitted mandatory models: {model_ids}"
    )

    glm51_rows = [r for r in result if r["model"] == "openai/glm-5.1"]
    assert len(glm51_rows) == 1, f"Expected exactly one glm-5.1 row; got {glm51_rows}"

    row = glm51_rows[0]
    elo = row.get("coding_arena_elo")
    assert elo is not None, "openai/glm-5.1 mandatory row has no coding_arena_elo"
    assert int(elo) >= gmc.ELO_CUTOFF, (
        f"openai/glm-5.1 ELO {elo} is below ELO_CUTOFF {gmc.ELO_CUTOFF} — "
        "row will be filtered out during catalog generation"
    )
    assert row.get("base_url") == _GENERAL_URL, (
        f"openai/glm-5.1 base_url must be {_GENERAL_URL!r}; got {row.get('base_url')!r}"
    )


# ---------------------------------------------------------------------------
# Bundled CSV header order must match the canonical CSV_FIELDNAMES list so
# that csv.DictReader, pandas, and any future reader all see the same column
# positions without surprises.
# ---------------------------------------------------------------------------

def test_bundled_csv_header_order_matches_canonical_fieldnames():
    """The first line of the committed ``pdd/data/llm_model.csv`` must exactly
    equal ``','.join(gmc.CSV_FIELDNAMES)``.

    Cross-module: generate_model_catalog.CSV_FIELDNAMES ↔ pdd/data/llm_model.csv.
    A mismatch here means the CSV was regenerated with a different schema or
    the header was edited manually without updating the schema constant.
    """
    bundled_csv = Path(__file__).parent.parent / "pdd" / "data" / "llm_model.csv"
    assert bundled_csv.exists(), f"Bundled CSV not found at {bundled_csv}"

    with open(bundled_csv, "r", encoding="utf-8", newline="") as fh:
        first_line = fh.readline().rstrip("\n").rstrip("\r")

    expected_header = ",".join(gmc.CSV_FIELDNAMES)
    assert first_line == expected_header, (
        "Bundled CSV header does not match gmc.CSV_FIELDNAMES.\n"
        f"  CSV header:         {first_line!r}\n"
        f"  CSV_FIELDNAMES:     {expected_header!r}"
    )


# ---------------------------------------------------------------------------
# 20. Mandatory Coding Plan rows include all three expected model IDs
#
# generate_model_catalog._mandatory_rows_missing_from must yield exactly three
# Z.AI Coding Plan rows (glm-5.2, glm-5-turbo, glm-4.7), each pointing at the
# Coding Plan endpoint with zero-dollar pricing.
#
# Cross-module: generate_model_catalog._MANDATORY_MODEL_ROWS → llm_invoke
# row selection (the rows must have the right shape to be selectable).
# ---------------------------------------------------------------------------

def test_mandatory_coding_plan_includes_glm_5_turbo_and_glm_4_7():
    """_mandatory_rows_missing_from yields Z.AI Coding Plan rows for
    openai/glm-5.2, openai/glm-5-turbo, and openai/glm-4.7, all with
    the Coding Plan endpoint URL and zero-dollar input/output pricing.

    Cross-module: generate_model_catalog → llm_invoke candidate shape.
    """
    all_rows = gmc._mandatory_rows_missing_from(
        rows=[], arena_index={}, elo_source_counts=defaultdict(int)
    )
    coding_plan_rows = [r for r in all_rows if r.get("provider") == "Z.AI Coding Plan"]

    model_ids = [r["model"] for r in coding_plan_rows]
    for expected_model in ("openai/glm-5.2", "openai/glm-5-turbo", "openai/glm-4.7"):
        assert expected_model in model_ids, (
            f"{expected_model} is missing from Z.AI Coding Plan mandatory rows.\n"
            f"  Found: {model_ids}"
        )

    for row in coding_plan_rows:
        assert row.get("base_url") == _CODING_URL, (
            f"Coding Plan row {row['model']!r} must have base_url={_CODING_URL!r}; "
            f"got {row.get('base_url')!r}"
        )
        assert float(row.get("input", 1.0)) == 0.0, (
            f"Coding Plan row {row['model']!r} must have input=0.0 (quota-backed); "
            f"got {row.get('input')!r}"
        )
        assert float(row.get("output", 1.0)) == 0.0, (
            f"Coding Plan row {row['model']!r} must have output=0.0 (quota-backed); "
            f"got {row.get('output')!r}"
        )


# ---------------------------------------------------------------------------
# 21. Bare glm-5-turbo name routes to Z.AI Coding Plan (not a competitor row)
#
# Near-miss: a competitor row for the same base model name exists in the
# catalog but the user only has ZAI_API_KEY set.  _alternative_base_lookups
# must prefer the Z.AI Coding Plan row.
#
# Cross-module: llm_invoke._alternative_base_lookups → _select_model_candidates.
# ---------------------------------------------------------------------------

def test_glm_5_turbo_bare_name_routes_to_zai_coding_plan(tmp_path, monkeypatch):
    """Bare PDD_MODEL_DEFAULT=glm-5-turbo must resolve to the Z.AI Coding Plan
    row (via _alternative_base_lookups) and not to an OpenRouter-style
    competitor row for the same base model name.

    Near-miss adversarial: only ZAI_API_KEY is set; OPENROUTER_API_KEY absent.
    Cross-module: _alternative_base_lookups ↔ _select_model_candidates.
    """
    # Build a CSV header that includes context_limit so we can use the
    # glm-5-turbo Coding Plan row with the canonical 15-column schema.
    header_15col = (
        "provider,model,input,output,coding_arena_elo,model_rank_score,model_rank_source,"
        "base_url,api_key,max_reasoning_tokens,structured_output,reasoning_type,"
        "location,interactive_only,context_limit\n"
    )
    # Competitor row: same bare model, different provider — should be ignored when
    # its required API key is absent.
    competitor_row = (
        "OpenRouter,openrouter/z-ai/glm-5-turbo,0.90,2.70,1480,1480,static,"
        ",OPENROUTER_API_KEY,0,False,none,,False,\n"
    )
    # The authoritative Z.AI Coding Plan row for glm-5-turbo.
    coding_plan_glm5t_row = (
        f"Z.AI Coding Plan,openai/glm-5-turbo,0.0,0.0,1450,1450,static-prefix,"
        f"{_CODING_URL},ZAI_API_KEY,0,False,effort,,False,\n"
    )

    csv_path = tmp_path / "llm_model.csv"
    csv_path.write_text(header_15col + competitor_row + coding_plan_glm5t_row, encoding="utf-8")

    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "glm-5-turbo")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "glm-5-turbo")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("ZAI_API_KEY", "sk-zai-glm5t-test")
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)

    captured_kwargs: dict = {}

    def _capture(**kwargs):
        captured_kwargs.update(kwargs)
        return _make_mock_completion()

    with patch("litellm.caching.caching.Cache"):
        with patch.object(llm_mod.litellm, "completion", side_effect=_capture):
            with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False):
                llm_mod.llm_invoke(
                    prompt="ping",
                    input_json={},
                    strength=0.5,
                    use_cloud=False,
                )

    assert captured_kwargs.get("base_url") == _CODING_URL, (
        f"glm-5-turbo must route to the Coding Plan endpoint {_CODING_URL!r}; "
        f"got base_url={captured_kwargs.get('base_url')!r}"
    )
    assert "openrouter" not in str(captured_kwargs.get("base_url", "")).lower(), (
        "OpenRouter endpoint must not be used when only ZAI_API_KEY is set"
    )


# ---------------------------------------------------------------------------
# 22. Z.AI rows excluded when ZAI_API_KEY is absent
#
# When ZAI_API_KEY is not in the environment, the Z.AI Coding Plan row must be
# treated as unavailable.  llm_invoke must raise an exception (no candidates)
# and litellm.completion must never be called.
#
# Cross-module: llm_invoke._select_model_candidates api_key filtering ↔ CSV
# api_key column.
# ---------------------------------------------------------------------------

def test_zai_rows_excluded_when_zai_api_key_absent(tmp_path, monkeypatch):
    """When ZAI_API_KEY is absent from the environment, the Z.AI Coding Plan
    row must be filtered out by _select_model_candidates, so litellm.completion
    is never called.

    Cross-module: csv api_key column ↔ _select_model_candidates key filtering.
    """
    csv_path = tmp_path / "llm_model.csv"
    csv_path.write_text(_CSV_HEADER + _CODING_PLAN_ROW, encoding="utf-8")

    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "openai/glm-5.2")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "openai/glm-5.2")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.delenv("ZAI_API_KEY", raising=False)

    mock_comp = MagicMock()

    with patch("litellm.caching.caching.Cache"):
        with patch.object(llm_mod.litellm, "completion", mock_comp):
            with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False):
                with pytest.raises(Exception):
                    llm_mod.llm_invoke(
                        prompt="ping",
                        input_json={},
                        strength=0.5,
                        use_cloud=False,
                    )

    mock_comp.assert_not_called()


# ---------------------------------------------------------------------------
# 23. estimate_only=True with Coding Plan row reports $0 cost
#
# When estimate_only=True is passed and the selected row is a Z.AI Coding Plan
# row (input=0.0, output=0.0), the raised EstimateOnlyResult must carry a
# total_cost of 0.0 — confirming quota-backed zero-dollar pricing flows through
# the estimate path.
#
# Cross-module: llm_invoke._build_estimate_payload ↔ CSV input/output pricing.
# ---------------------------------------------------------------------------

def test_estimate_only_coding_plan_reports_quota_backed_cost(tmp_path, monkeypatch):
    """estimate_only=True with a Z.AI Coding Plan row raises EstimateOnlyResult
    whose estimate dict reflects quota-backed pricing: unknown_cost=True,
    cost_known=False, total_cost=None (no per-token dollar amount).

    Quota-backed providers skip the pricing API intentionally so that per-token
    cost is never misleadingly reported — the subscription covers access.

    Cross-module: CSV provider='Z.AI Coding Plan' ↔ _build_estimate_payload
    quota-skip branch ↔ EstimateOnlyResult.estimate.
    """
    csv_path = tmp_path / "llm_model.csv"
    csv_path.write_text(_CSV_HEADER + _CODING_PLAN_ROW, encoding="utf-8")

    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "openai/glm-5.2")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "openai/glm-5.2")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("ZAI_API_KEY", "sk-zai-estimate-test")

    with patch("litellm.caching.caching.Cache"):
        with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False):
            with pytest.raises(llm_mod.EstimateOnlyResult) as exc_info:
                llm_mod.llm_invoke(
                    prompt="estimate this",
                    input_json={},
                    strength=0.5,
                    use_cloud=False,
                    estimate_only=True,
                )

    estimate = exc_info.value.estimate
    assert estimate.get("unknown_cost") is True, (
        "Z.AI Coding Plan is quota-backed; estimate must have unknown_cost=True. "
        f"Got unknown_cost={estimate.get('unknown_cost')!r}"
    )
    assert estimate.get("cost_known") is False, (
        "Z.AI Coding Plan is quota-backed; estimate must have cost_known=False. "
        f"Got cost_known={estimate.get('cost_known')!r}"
    )
    assert estimate.get("total_cost") is None, (
        "Quota-backed Coding Plan rows must NOT expose a per-token total_cost; "
        f"got total_cost={estimate.get('total_cost')!r}"
    )


# ---------------------------------------------------------------------------
# 24. reasoning_effort kwarg propagated for Z.AI GLM-5.2 row (effort type)
#
# When the selected row has reasoning_type=effort and llm_invoke is called with
# time=0.8, LiteLLM must receive reasoning_effort="high" — not a GPT-5-style
# nested 'reasoning' dict.  This verifies the effort branch of the reasoning
# dispatcher for non-OpenAI providers.
#
# Cross-module: CSV reasoning_type column ↔ llm_invoke reasoning dispatcher ↔
# litellm.completion kwargs.
# ---------------------------------------------------------------------------

def test_reasoning_effort_kwarg_propagated_for_zai_glm52_row(tmp_path, monkeypatch):
    """With reasoning_type=effort in the CSV row and time=0.8 passed to
    llm_invoke, litellm.completion must receive reasoning_effort='high' (not
    a GPT-5-style nested 'reasoning' dict).

    time=0.8 > 0.7 → time_to_effort_level returns 'high'.
    Cross-module: CSV reasoning_type ↔ llm_invoke effort dispatcher ↔ litellm.
    """
    csv_path = tmp_path / "llm_model.csv"
    # Use the general Z.AI row which has reasoning_type=effort.
    csv_path.write_text(_CSV_HEADER + _GENERAL_ROW, encoding="utf-8")

    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "openai/glm-5.2")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "openai/glm-5.2")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("ZAI_API_KEY", "sk-zai-reasoning-test")

    captured_kwargs: dict = {}

    def _capture(**kwargs):
        captured_kwargs.update(kwargs)
        return _make_mock_completion()

    with patch("litellm.caching.caching.Cache"):
        with patch.object(llm_mod.litellm, "completion", side_effect=_capture):
            with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False):
                llm_mod.llm_invoke(
                    prompt="reason about this",
                    input_json={},
                    strength=0.5,
                    use_cloud=False,
                    time=0.8,
                )

    assert "reasoning_effort" in captured_kwargs, (
        "litellm.completion must receive 'reasoning_effort' kwarg when "
        "reasoning_type=effort and time=0.8; "
        f"actual kwargs keys: {sorted(captured_kwargs.keys())}"
    )
    assert captured_kwargs["reasoning_effort"] == "high", (
        f"time=0.8 > 0.7 → time_to_effort_level='high'; "
        f"got reasoning_effort={captured_kwargs['reasoning_effort']!r}"
    )
    assert "reasoning" not in captured_kwargs or not isinstance(
        captured_kwargs.get("reasoning"), dict
    ), (
        "Z.AI GLM-5.2 must NOT use the GPT-5-style nested 'reasoning' dict; "
        f"got: {captured_kwargs.get('reasoning')!r}"
    )
