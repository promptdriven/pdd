"""Verify CSV-defined models are registered with LiteLLM so completion_cost
returns nonzero for models LiteLLM doesn't ship pricing for, and that the
success callback falls back to CSV rates when LiteLLM silently returns 0.

Regression: in cloud tests, CSV-defined models may be present in the project
``.pdd/llm_model.csv`` but missing from LiteLLM's bundled pricing DB. Without
registration, ``litellm.completion_cost`` returned 0.0 silently, leaving the
``@pytest.mark.real`` cost-tracking assertions broken.
"""
from __future__ import annotations

from types import SimpleNamespace

import litellm
import pandas as pd
from litellm import Choices, Message, ModelResponse, Usage

from pdd import llm_invoke
from pdd.llm_invoke import _litellm_success_callback, _set_model_rate_map  # type: ignore

CSV_ONLY_MODEL = "fireworks_ai/accounts/pdd-ci/models/csv-only-registration-test"


def test_csv_only_model_completion_cost_is_nonzero():
    model = CSV_ONLY_MODEL
    assert model not in litellm.model_cost, (
        "Precondition: LiteLLM should not ship pricing for this CSV-only model."
    )
    df = pd.DataFrame(
        [{"provider": "Fireworks", "model": model, "input": 0.95, "output": 4.0}]
    )

    try:
        _set_model_rate_map(df)
        assert llm_invoke._MODEL_RATE_MAP.get(model) == (0.95, 4.0)
        assert model in litellm.model_cost, (
            "_set_model_rate_map must register CSV models with LiteLLM."
        )

        resp = ModelResponse(
            id="t",
            choices=[
                Choices(
                    finish_reason="stop",
                    index=0,
                    message=Message(role="assistant", content="hi"),
                )
            ],
            model=model,
            usage=Usage(prompt_tokens=1000, completion_tokens=500, total_tokens=1500),
        )
        cost = litellm.completion_cost(completion_response=resp)
        expected = (1000 * 0.95 + 500 * 4.0) / 1_000_000.0
        assert cost == expected
    finally:
        litellm.model_cost.pop(model, None)


def test_callback_falls_back_to_csv_when_litellm_returns_zero(monkeypatch):
    """When LiteLLM silently returns 0.0 for an unpriced model, the success
    callback must fall back to CSV rates if the model is in _MODEL_RATE_MAP."""
    model = CSV_ONLY_MODEL
    df = pd.DataFrame(
        [{"provider": "Fireworks", "model": model, "input": 0.95, "output": 4.0}]
    )
    _set_model_rate_map(df)
    try:
        # Force LiteLLM's cost path to return 0 silently, simulating a model
        # missing from its bundled pricing.
        monkeypatch.setattr(
            llm_invoke.litellm, "completion_cost", lambda **_: 0.0
        )

        usage = SimpleNamespace(prompt_tokens=1000, completion_tokens=500)
        response = SimpleNamespace(
            usage=usage,
            choices=[SimpleNamespace(finish_reason="stop")],
        )
        _litellm_success_callback(
            kwargs={"model": model},
            completion_response=response,
            start_time=0.0,
            end_time=1.0,
        )
        expected = (1000 * 0.95 + 500 * 4.0) / 1_000_000.0
        assert llm_invoke._LAST_CALLBACK_DATA["cost"] == expected
    finally:
        litellm.model_cost.pop(model, None)
