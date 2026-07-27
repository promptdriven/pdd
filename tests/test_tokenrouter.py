"""Focused tests for the deterministic TokenRouter integration."""

from __future__ import annotations

import csv
import os
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import MagicMock, patch

import pandas as pd
import pytest

from pdd.llm_invoke import _select_exact_model_candidate
from pdd.tokenrouter import (
    TOKENROUTER_API_KEY_ENV,
    TOKENROUTER_BASE_URL,
    TOKENROUTER_MODEL_ENDPOINTS,
    TOKENROUTER_PROVIDER,
    tokenrouter_catalog_models,
    tokenrouter_litellm_base_url,
    tokenrouter_litellm_model,
)


CATALOG_PATH = Path(__file__).parents[1] / "pdd" / "data" / "llm_model.csv"


def _catalog_rows() -> list[dict[str, str]]:
    with CATALOG_PATH.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle))


def test_tokenrouter_snapshot_exactly_matches_packaged_provider_rows() -> None:
    rows = [
        row for row in _catalog_rows()
        if row["provider"] == TOKENROUTER_PROVIDER
    ]

    assert {row["model"] for row in rows} == tokenrouter_catalog_models()
    assert len(rows) == len(TOKENROUTER_MODEL_ENDPOINTS)
    assert {row["api_key"] for row in rows} == {TOKENROUTER_API_KEY_ENV}
    assert {row["base_url"] for row in rows} == {TOKENROUTER_BASE_URL}
    assert {row["interactive_only"] for row in rows} == {"False"}


@pytest.mark.parametrize(
    ("model_id", "endpoint_type", "expected"),
    [
        ("openai/gpt-5.2", "openai", "openai/openai/gpt-5.2"),
        (
            "openai/gpt-5.4",
            "openai-response",
            "openai/responses/openai/gpt-5.4",
        ),
        (
            "openai/gpt-5.6-sol",
            "openai-response",
            "openai/responses/openai/gpt-5.6-sol",
        ),
        (
            "anthropic/claude-opus-4.6",
            "anthropic-compatible",
            "anthropic/anthropic/claude-opus-4.6",
        ),
        (
            "google/gemini-3.1-pro-preview",
            "gemini",
            "gemini/google/gemini-3.1-pro-preview",
        ),
    ],
)
def test_tokenrouter_protocols_have_explicit_litellm_routes(
    model_id: str,
    endpoint_type: str,
    expected: str,
) -> None:
    assert tokenrouter_litellm_model(model_id, endpoint_type) == expected


def test_tokenrouter_rejects_unimplemented_endpoint_type() -> None:
    with pytest.raises(ValueError, match="Unsupported TokenRouter endpoint type"):
        tokenrouter_litellm_model("vendor/model", "image-generation")


def test_tokenrouter_gpt_5_6_sol_catalog_metadata() -> None:
    row = next(
        row
        for row in _catalog_rows()
        if row["provider"] == TOKENROUTER_PROVIDER
        and row["model"] == "openai/responses/openai/gpt-5.6-sol"
    )

    assert row["input"] == "5.0"
    assert row["output"] == "30.0"
    assert row["model_rank_score"] == "17001"
    assert row["model_rank_source"] == "platform-default"
    assert row["structured_output"] == "True"
    assert row["reasoning_type"] == "none"


def test_litellm_recognizes_tokenrouter_responses_route() -> None:
    from litellm.litellm_core_utils.get_llm_provider_logic import (
        get_llm_provider,
    )
    from litellm.main import responses_api_bridge_check

    model, provider, _key, base_url = get_llm_provider(
        "openai/responses/openai/gpt-5.4",
        api_base=TOKENROUTER_BASE_URL,
    )
    route_info, routed_model = responses_api_bridge_check(model, provider)

    assert provider == "openai"
    assert base_url == TOKENROUTER_BASE_URL
    assert route_info["mode"] == "responses"
    assert routed_model == "openai/gpt-5.4"


def test_tokenrouter_anthropic_url_avoids_duplicate_v1_suffix() -> None:
    assert tokenrouter_litellm_base_url(
        TOKENROUTER_PROVIDER,
        "anthropic/anthropic/claude-opus-4.6",
        TOKENROUTER_BASE_URL,
    ) == "https://api.tokenrouter.com/v1/messages"
    assert tokenrouter_litellm_base_url(
        TOKENROUTER_PROVIDER,
        "openai/openai/gpt-5.2",
        TOKENROUTER_BASE_URL,
    ) == TOKENROUTER_BASE_URL


def test_direct_and_local_device_rows_remain_in_catalog() -> None:
    identities = {
        (row["provider"], row["model"], row["api_key"])
        for row in _catalog_rows()
    }

    assert ("Anthropic", "claude-opus-4-6", "ANTHROPIC_API_KEY") in identities
    assert ("OpenAI", "gpt-5.2", "OPENAI_API_KEY") in identities
    assert (
        "Google Gemini",
        "gemini/gemini-3.1-pro-preview",
        "GEMINI_API_KEY",
    ) in identities
    assert ("lm_studio", "lm_studio/qwen3-coder-next", "") in identities
    assert any(
        provider == "Github Copilot" and api_key == ""
        for provider, _model, api_key in identities
    )


def test_request_scoped_exact_selection_is_concurrency_safe() -> None:
    frame = pd.DataFrame(
        [
            {"provider": "TokenRouter", "model": "openai/openai/gpt-5.2"},
            {"provider": "OpenAI", "model": "gpt-5.2"},
        ]
    )
    before = dict(os.environ)

    selections = [
        ("openai/openai/gpt-5.2", "TokenRouter"),
        ("gpt-5.2", "OpenAI"),
    ]
    with ThreadPoolExecutor(max_workers=2) as executor:
        results = list(
            executor.map(
                lambda pair: _select_exact_model_candidate(
                    frame,
                    pair[0],
                    pair[1],
                )[0],
                selections,
            )
        )

    assert [(row["model"], row["provider"]) for row in results] == selections
    assert dict(os.environ) == before


def test_exact_selection_fails_closed_for_missing_or_ambiguous_rows() -> None:
    frame = pd.DataFrame(
        [
            {"provider": "Gateway A", "model": "shared/model"},
            {"provider": "Gateway B", "model": "shared/model"},
        ]
    )

    with pytest.raises(ValueError, match="ambiguous"):
        _select_exact_model_candidate(frame, "shared/model", None)
    with pytest.raises(ValueError, match="was not found"):
        _select_exact_model_candidate(frame, "missing/model", "TokenRouter")
    with pytest.raises(ValueError, match="requires an exact"):
        _select_exact_model_candidate(frame, None, "TokenRouter")


def test_llm_invoke_exact_pair_reaches_only_requested_tokenrouter_row(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import pdd.llm_invoke as llm_module

    csv_path = tmp_path / "llm_model.csv"
    csv_path.write_text(
        "provider,model,input,output,coding_arena_elo,model_rank_score,"
        "model_rank_source,base_url,api_key,max_reasoning_tokens,"
        "structured_output,reasoning_type,location,interactive_only,"
        "context_limit\n"
        "OpenAI,gpt-5.2,1.75,14,1404,1404,test,,OPENAI_API_KEY,0,"
        "True,effort,,False,\n"
        "TokenRouter,anthropic/anthropic/claude-opus-4.6,5,25,1548,1548,"
        "test,https://api.tokenrouter.com/v1,TOKENROUTER_API_KEY,0,"
        "False,none,,False,\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(llm_module, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setenv("TOKENROUTER_API_KEY", "test-placeholder-not-a-secret")

    response = MagicMock()
    message = MagicMock()
    message.content = "selected"
    message.get.side_effect = lambda key, default=None: getattr(
        message, key, default
    )
    choice = MagicMock(message=message, finish_reason="stop")
    response.choices = [choice]
    response.usage = MagicMock(
        prompt_tokens=1,
        completion_tokens=1,
        total_tokens=2,
    )
    response.model = "anthropic/anthropic/claude-opus-4.6"
    response._hidden_params = {}

    with (
        patch.object(llm_module.litellm, "completion", return_value=response)
        as completion,
        patch.object(
            llm_module,
            "_LAST_CALLBACK_DATA",
            {"cost": 0.0, "input_tokens": 1, "output_tokens": 1},
        ),
    ):
        result = llm_module.llm_invoke(
            messages=[{"role": "user", "content": "hello"}],
            model="anthropic/anthropic/claude-opus-4.6",
            model_provider="TokenRouter",
            use_cloud=False,
            time=0,
        )

    assert result["result"] == "selected"
    completion.assert_called_once()
    kwargs = completion.call_args.kwargs
    assert kwargs["model"] == "anthropic/anthropic/claude-opus-4.6"
    assert kwargs["base_url"] == "https://api.tokenrouter.com/v1/messages"
    assert kwargs["api_key"] == "test-placeholder-not-a-secret"
    assert "extra_headers" not in kwargs


def test_exact_pair_refuses_cloud_dispatch() -> None:
    import pdd.llm_invoke as llm_module

    with pytest.raises(ValueError, match="local invocation contract"):
        llm_module.llm_invoke(
            messages=[{"role": "user", "content": "hello"}],
            model="openai/openai/gpt-5.2",
            model_provider="TokenRouter",
            use_cloud=True,
        )
