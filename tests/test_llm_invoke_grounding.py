"""Grounding metadata tests for llm_invoke cloud and local paths."""
from __future__ import annotations

import os
from unittest.mock import MagicMock, patch

import pandas as pd
import pytest

from pdd import llm_invoke as llm_mod
from pdd.llm_invoke import llm_invoke


def _make_completion_response(content: str = "ok") -> MagicMock:
    message = MagicMock()
    message.content = content
    choice = MagicMock()
    choice.message = message
    choice.finish_reason = "stop"
    response = MagicMock()
    response.choices = [choice]
    return response


@pytest.mark.timeout(60)
def test_llm_invoke_cloud_returns_grounding_metadata() -> None:
  cloud_response = MagicMock()
  cloud_response.status_code = 200
  cloud_response.json.return_value = {
      "result": "ok",
      "totalCost": 0.01,
      "modelName": "cloud-model",
      "examplesUsed": [
          {
              "slug": "refund_payment",
              "promptSha256": "prompt-hash",
              "similarity": 0.88,
              "source": "cloud-history",
          }
      ],
  }

  with patch.dict("os.environ", {"PDD_FORCE_LOCAL": ""}):
    with patch("pdd.core.cloud.CloudConfig") as mock_config:
      mock_config.is_cloud_enabled.return_value = True
      mock_config.get_jwt_token.return_value = "token"
      mock_config.get_endpoint_url.return_value = "https://example.test/llm"
      with patch("requests.post", return_value=cloud_response):
        result = llm_invoke(
            prompt="hello {name}",
            input_json={"name": "world"},
            strength=0.5,
            use_cloud=True,
            verbose=False,
            grounding_overrides={"pinned": ["refund_payment"], "excluded": []},
        )

  grounding = result["grounding"]
  assert grounding["mode"] == "cloud"
  assert grounding["pinned"] == ["refund_payment"]
  assert grounding["selected_examples"][0]["module"] == "refund_payment"
  assert grounding["selected_examples"][0]["prompt_sha256"] == "prompt-hash"


def test_llm_invoke_uses_source_prompt_for_overrides() -> None:
  cloud_response = MagicMock()
  cloud_response.status_code = 200
  cloud_response.json.return_value = {
      "result": "ok",
      "totalCost": 0.0,
      "modelName": "cloud-model",
  }

  prompt = "Use <pin>auth</pin> and skip <exclude>legacy</exclude>."
  with patch.dict("os.environ", {"PDD_FORCE_LOCAL": ""}):
    with patch("pdd.core.cloud.CloudConfig") as mock_config:
      mock_config.is_cloud_enabled.return_value = True
      mock_config.get_jwt_token.return_value = "token"
      mock_config.get_endpoint_url.return_value = "https://example.test/llm"
      with patch("requests.post", return_value=cloud_response):
        result = llm_invoke(
            prompt="hello",
            input_json={},
            strength=0.5,
            use_cloud=True,
            source_prompt=prompt,
        )

  assert result["grounding"]["pinned"] == ["auth"]
  assert result["grounding"]["excluded"] == ["legacy"]


@pytest.mark.timeout(60)
@patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "OPENAI_API_KEY": "test-key"})
def test_llm_invoke_local_returns_unavailable_grounding() -> None:
    """Local runs record unavailable grounding with pin/exclude overrides preserved."""
    mock_model = {
        "provider": "Anthropic",
        "model": "claude-test-model",
        "input": 3.0,
        "output": 15.0,
        "coding_arena_elo": 1500,
        "structured_output": False,
        "base_url": "",
        "api_key": "OPENAI_API_KEY",
        "max_tokens": "",
        "max_completion_tokens": "",
        "reasoning_type": "none",
        "max_reasoning_tokens": 0,
    }
    llm_mod._LAST_CALLBACK_DATA["cost"] = 0.01
    llm_mod._LAST_CALLBACK_DATA["input_tokens"] = 10
    llm_mod._LAST_CALLBACK_DATA["output_tokens"] = 5

    with patch("pdd.llm_invoke._load_model_data", return_value=pd.DataFrame([mock_model])), patch(
        "pdd.llm_invoke._select_model_candidates", return_value=[mock_model]
    ), patch("pdd.llm_invoke._ensure_api_key", return_value=True), patch(
        "pdd.llm_invoke.litellm"
    ) as mock_litellm:
        mock_litellm.completion = MagicMock(return_value=_make_completion_response())
        mock_litellm.cache = None
        mock_litellm.drop_params = True
        result = llm_invoke(
            prompt="Say <pin>auth</pin> hello {name}",
            input_json={"name": "world"},
            strength=0.5,
            use_cloud=False,
            source_prompt="Say <pin>auth</pin> hello",
        )

    grounding = result["grounding"]
    assert grounding["mode"] == "unavailable"
    assert grounding["pinned"] == ["auth"]
    assert grounding["selected_examples"] == []
