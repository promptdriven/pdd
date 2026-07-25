from __future__ import annotations

import csv
import json
from collections import defaultdict
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import litellm
import httpx
import pandas as pd
import pytest
from openai import OpenAI

from pdd import generate_model_catalog as catalog
from pdd import llm_invoke as llm_mod
from pdd import provider_manager


K3_MODEL = "moonshot/kimi-k3"
K3_BASE_URL = "https://api.moonshot.cn/v1"


def _response(content: str = "ok"):
    message = MagicMock()
    message.content = content
    message.get.side_effect = lambda key, default=None: getattr(
        message, key, default
    )
    choice = SimpleNamespace(message=message, finish_reason="stop")
    usage = SimpleNamespace(
        prompt_tokens=10, completion_tokens=5, total_tokens=15
    )
    return SimpleNamespace(
        choices=[choice],
        usage=usage,
        model=K3_MODEL,
        _hidden_params={},
    )


def _write_k3_csv(path) -> None:
    path.write_text(
        "provider,model,input,output,coding_arena_elo,model_rank_score,"
        "model_rank_source,base_url,api_key,max_reasoning_tokens,"
        "structured_output,reasoning_type,location,interactive_only,"
        "context_limit\n"
        "Moonshot AI,moonshot/kimi-k3,2.951594,14.757969,0,0,"
        "platform-default,https://api.moonshot.cn/v1,MOONSHOT_API_KEY,0,"
        "True,effort,,False,1048576\n",
        encoding="utf-8",
    )


def _invoke_k3(tmp_path, monkeypatch, *, time=0.5, output_schema=None):
    csv_path = tmp_path / "llm_model.csv"
    _write_k3_csv(csv_path)
    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
    monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", K3_MODEL)
    monkeypatch.setenv("PDD_MODEL_DEFAULT", K3_MODEL)
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("MOONSHOT_API_KEY", "moonshot-test-key")
    captured = {}

    def capture(**kwargs):
        captured.update(kwargs)
        return _response('{"answer":"ok"}' if output_schema else "ok")

    with (
        patch("litellm.caching.caching.Cache"),
        patch("pdd.core.cloud.CloudConfig.is_cloud_enabled", return_value=False),
        patch.object(llm_mod, "count_tokens_for_messages", return_value=10),
        patch.object(llm_mod.litellm, "completion", side_effect=capture),
    ):
        result = llm_mod.llm_invoke(
            prompt="Say {word}",
            input_json={"word": "OK"},
            strength=0.5,
            time=time,
            output_schema=output_schema,
            use_cloud=False,
        )
    return captured, result


def test_k3_mandatory_row_and_packaged_catalog_are_durable():
    seeded = catalog._mandatory_rows_missing_from(
        rows=[], arena_index={}, elo_source_counts=defaultdict(int)
    )
    row = next(item for item in seeded if item["model"] == K3_MODEL)
    assert row["model_rank_source"] == "platform-default"
    assert row["coding_arena_elo"] == 0
    assert row["base_url"] == K3_BASE_URL
    assert row["api_key"] == "MOONSHOT_API_KEY"
    assert row["structured_output"] is True
    assert row["reasoning_type"] == "effort"
    assert row["context_limit"] == 1_048_576
    assert row["input"] == round(20 / 6.7760, 6)
    assert row["output"] == round(100 / 6.7760, 6)

    with open("pdd/data/llm_model.csv", encoding="utf-8", newline="") as handle:
        packaged = next(
            item for item in csv.DictReader(handle) if item["model"] == K3_MODEL
        )
    assert packaged["base_url"] == K3_BASE_URL
    assert (
        Path("data/llm_model.csv").read_bytes()
        == Path("pdd/data/llm_model.csv").read_bytes()
    )


def test_k3_catalog_registration_includes_cost_and_limits():
    litellm.model_cost.pop(K3_MODEL, None)
    frame = pd.DataFrame(
        [
            {
                "provider": "Moonshot AI",
                "model": K3_MODEL,
                "input": 2.951594,
                "output": 14.757969,
                "context_limit": 1_048_576,
            }
        ]
    )
    try:
        llm_mod._set_model_rate_map(frame)
        registered = litellm.model_cost[K3_MODEL]
        assert registered["litellm_provider"] == "moonshot"
        assert registered["input_cost_per_token"] == pytest.approx(
            2.951594 / 1_000_000
        )
        assert registered["output_cost_per_token"] == pytest.approx(
            14.757969 / 1_000_000
        )
        assert registered["max_input_tokens"] == 1_048_576
        assert registered["max_tokens"] == 1_048_576
        assert registered["max_output_tokens"] == 1_048_576
        assert registered["supports_reasoning"] is True
        assert registered["supports_response_schema"] is True
    finally:
        litellm.model_cost.pop(K3_MODEL, None)


@pytest.mark.parametrize(
    "model_name",
    [None, 3, ["moonshot/kimi-k3"], {"model": "moonshot/kimi-k3"}],
)
def test_k3_model_match_rejects_non_strings(model_name):
    assert llm_mod._is_kimi_k3_model(model_name) is False


def test_k3_extra_body_effort_is_visible_to_safe_attribution():
    kwargs = {"extra_body": {"reasoning_effort": "high"}}
    assert llm_mod._has_thinking_or_reasoning_payload(kwargs) is True
    assert llm_mod._summarize_litellm_kwargs(kwargs)["has_reasoning"] is True


def test_pinned_litellm_merges_k3_effort_into_mock_http_body():
    """Exercise LiteLLM's actual Moonshot HTTP path without a paid call."""
    frame = pd.DataFrame(
        [
            {
                "provider": "Moonshot AI",
                "model": K3_MODEL,
                "input": 2.951594,
                "output": 14.757969,
                "context_limit": 1_048_576,
            }
        ]
    )
    requests = []

    def mock_provider(request: httpx.Request) -> httpx.Response:
        requests.append(request)
        return httpx.Response(
            200,
            json={
                "id": "mock-k3",
                "object": "chat.completion",
                "created": 0,
                "model": "kimi-k3",
                "choices": [
                    {
                        "index": 0,
                        "message": {"role": "assistant", "content": "ok"},
                        "finish_reason": "stop",
                    }
                ],
                "usage": {
                    "prompt_tokens": 1,
                    "completion_tokens": 1,
                    "total_tokens": 2,
                },
            },
        )

    litellm.model_cost.pop(K3_MODEL, None)
    transport = httpx.MockTransport(mock_provider)
    http_client = httpx.Client(transport=transport)
    client = OpenAI(
        api_key="mock-key", base_url=K3_BASE_URL, http_client=http_client
    )
    original_cache = litellm.cache
    try:
        litellm.cache = None
        llm_mod._set_model_rate_map(frame)
        litellm.completion(
            model=K3_MODEL,
            messages=[{"role": "user", "content": "hi"}],
            api_key="mock-key",
            base_url=K3_BASE_URL,
            extra_body={"reasoning_effort": "high"},
            caching=False,
            client=client,
        )
    finally:
        litellm.cache = original_cache
        client.close()
        litellm.model_cost.pop(K3_MODEL, None)

    assert len(requests) == 1
    request = requests[0]
    assert str(request.url) == f"{K3_BASE_URL}/chat/completions"
    body = json.loads(request.content)
    assert body["model"] == "kimi-k3"
    assert body["reasoning_effort"] == "high"
    assert "extra_body" not in body
    for parameter in llm_mod._KIMI_K3_FIXED_SAMPLING_PARAMETERS:
        assert parameter not in body


@pytest.mark.parametrize(
    ("time_value", "expected_effort"),
    [(0.1, "low"), (0.5, "high"), (0.9, "max")],
)
def test_k3_request_contract_maps_effort_and_endpoint(
    tmp_path, monkeypatch, time_value, expected_effort
):
    monkeypatch.delenv("PDD_REASONING_EFFORT", raising=False)
    captured, _ = _invoke_k3(tmp_path, monkeypatch, time=time_value)
    assert captured["model"] == K3_MODEL
    assert captured["base_url"] == K3_BASE_URL
    assert captured["api_base"] == K3_BASE_URL
    assert captured["api_key"] == "moonshot-test-key"
    assert captured["extra_body"]["reasoning_effort"] == expected_effort
    assert "reasoning_effort" not in captured
    for parameter in llm_mod._KIMI_K3_FIXED_SAMPLING_PARAMETERS:
        assert parameter not in captured


@pytest.mark.parametrize("effort", ["low", "high", "max"])
def test_k3_explicit_effort_override(tmp_path, monkeypatch, effort):
    monkeypatch.setenv("PDD_REASONING_EFFORT", effort)
    captured, _ = _invoke_k3(tmp_path, monkeypatch, time=0.1)
    assert captured["extra_body"]["reasoning_effort"] == effort


def test_k3_rejects_medium_override_before_provider_call(tmp_path, monkeypatch):
    monkeypatch.setenv("PDD_REASONING_EFFORT", "medium")
    with pytest.raises(ValueError, match="supported values: high, low, max"):
        _invoke_k3(tmp_path, monkeypatch)


def test_k3_structured_output_preserves_request_contract(tmp_path, monkeypatch):
    monkeypatch.delenv("PDD_REASONING_EFFORT", raising=False)
    schema = {
        "type": "object",
        "properties": {"answer": {"type": "string"}},
        "required": ["answer"],
    }
    captured, result = _invoke_k3(
        tmp_path, monkeypatch, time=0.5, output_schema=schema
    )
    assert captured["response_format"]["type"] == "json_schema"
    assert captured["extra_body"] == {"reasoning_effort": "high"}
    assert result["result"] == '{"answer":"ok"}'


def test_setup_provider_catalog_discovers_moonshot_k3(monkeypatch):
    reference_row = {
        "provider": "Moonshot AI",
        "model": K3_MODEL,
        "api_key": "MOONSHOT_API_KEY",
        "base_url": K3_BASE_URL,
    }
    writes = []
    monkeypatch.setattr(
        provider_manager, "_read_csv", MagicMock(side_effect=[[reference_row], []])
    )
    monkeypatch.setattr(
        provider_manager, "_write_csv_atomic", lambda _path, rows: writes.extend(rows)
    )
    monkeypatch.setattr(provider_manager.Prompt, "ask", MagicMock(return_value="1"))
    monkeypatch.setattr(provider_manager.Confirm, "ask", MagicMock(return_value=False))
    monkeypatch.setattr(
        provider_manager, "_is_key_set", MagicMock(return_value="shell environment")
    )
    monkeypatch.setattr(provider_manager, "_get_user_csv_path", lambda: None)
    with patch.object(provider_manager.console, "print"):
        assert provider_manager.add_provider_from_registry() is True
    assert writes == [reference_row]
