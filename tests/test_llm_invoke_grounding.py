"""Grounding metadata tests for llm_invoke cloud path."""
from __future__ import annotations

from unittest.mock import MagicMock, patch

import pytest

from pdd.llm_invoke import llm_invoke


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
