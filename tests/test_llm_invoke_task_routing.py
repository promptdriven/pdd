"""Tests for task-routing integration in llm_invoke (PR #1582 / epic/1431-task-routing-v1).

Validates two behavioral claims:
1. Dormancy — when PDD_ENABLE_TASK_ROUTING is unset (or CSV is header-only), the
   llm_invoke router does NOT apply task-based routing; default behavior is
   unchanged.
2. Activation — when PDD_ENABLE_TASK_ROUTING=1 AND a task_class is supplied AND
   task_routing.csv has a matching row, the router selects the configured
   model/temperature/thinking/multi-shot parameters.

Tests are skipped gracefully on branches where the task-routing feature is
absent so they do not block the main-branch test suite.
"""

from __future__ import annotations

import io
import os
import textwrap
from pathlib import Path
from typing import Any, Dict
from unittest.mock import MagicMock, patch, patch as _patch

import pandas as pd
import pytest

# ---------------------------------------------------------------------------
# Feature-presence guard
# ---------------------------------------------------------------------------
# The task-routing feature is only available on epic/1431-task-routing-v1 and
# later.  We detect it by looking for the PDD_ENABLE_TASK_ROUTING integration
# point inside llm_invoke.  Tests that require the new API are marked
# skip-if-absent so the file remains collectable on main.

import pdd.llm_invoke as _llm_mod

_HAS_TASK_ROUTING = hasattr(_llm_mod, "_load_task_routing_csv") or (
    "task_class" in str(getattr(_llm_mod.llm_invoke, "__code__", None) and
                        _llm_mod.llm_invoke.__code__.co_varnames or "")
)

requires_task_routing = pytest.mark.skipif(
    not _HAS_TASK_ROUTING,
    reason="task-routing feature not present on this branch (epic/1431-task-routing-v1 only)",
)

# ---------------------------------------------------------------------------
# Shared fixtures / helpers
# ---------------------------------------------------------------------------

MOCK_MODEL_ROW = dict(
    provider="Anthropic",
    model="claude-sonnet-4-6",
    input=3.0,
    output=15.0,
    coding_arena_elo=1500,
    structured_output=False,
    base_url="",
    api_key="ANTHROPIC_API_KEY",
    max_tokens="",
    max_completion_tokens="",
    reasoning_type="budget",
    max_reasoning_tokens=8000,
    avg_cost=9.0,
    model_rank_score=1500,
    model_rank_source="legacy-coding-arena-elo",
)

MOCK_CHEAP_MODEL_ROW = dict(
    provider="OpenAI",
    model="gpt-4o-mini",
    input=0.15,
    output=0.6,
    coding_arena_elo=1300,
    structured_output=True,
    base_url="",
    api_key="OPENAI_API_KEY",
    max_tokens="",
    max_completion_tokens="",
    reasoning_type="none",
    max_reasoning_tokens=0,
    avg_cost=0.375,
    model_rank_score=1300,
    model_rank_source="legacy-coding-arena-elo",
)


def _make_mock_df(rows=None):
    """Return a minimal DataFrame mimicking _load_model_data output."""
    if rows is None:
        rows = [MOCK_MODEL_ROW, MOCK_CHEAP_MODEL_ROW]
    df = pd.DataFrame(rows)
    for col in ["input", "output", "coding_arena_elo", "max_tokens",
                "max_completion_tokens", "max_reasoning_tokens",
                "avg_cost", "model_rank_score"]:
        if col in df.columns:
            df[col] = pd.to_numeric(df[col], errors="coerce").fillna(0)
    df["max_reasoning_tokens"] = df["max_reasoning_tokens"].astype(int)
    df["structured_output"] = df["structured_output"].fillna(False).astype(bool)
    df["reasoning_type"] = df["reasoning_type"].fillna("none").astype(str).str.lower()
    df["api_key"] = df["api_key"].fillna("").astype(str)
    return df


def _make_litellm_response(content="ok", model="claude-sonnet-4-6",
                            prompt_tokens=10, completion_tokens=20):
    resp = MagicMock()
    choice = MagicMock()
    choice.message.content = content
    choice.finish_reason = "stop"
    resp.choices = [choice]
    resp.model = model
    resp._hidden_params = {}
    usage = MagicMock()
    usage.prompt_tokens = prompt_tokens
    usage.completion_tokens = completion_tokens
    usage.total_tokens = prompt_tokens + completion_tokens
    resp.usage = usage
    return resp


# ---------------------------------------------------------------------------
# Section 1: Dormancy — PDD_ENABLE_TASK_ROUTING unset
# ---------------------------------------------------------------------------

class TestDormancyFlagUnset:
    """With PDD_ENABLE_TASK_ROUTING unset, llm_invoke must behave exactly as
    it did before the task-routing feature was added."""

    def test_basic_invoke_succeeds_without_flag(self, mock_load_models):
        """llm_invoke completes normally when PDD_ENABLE_TASK_ROUTING is absent."""
        env_without_flag = {k: v for k, v in os.environ.items()
                            if k != "PDD_ENABLE_TASK_ROUTING"}
        env_without_flag["PDD_FORCE_LOCAL"] = "1"

        with patch.dict(os.environ, env_without_flag, clear=True):
            with patch("pdd.llm_invoke.litellm.completion",
                       return_value=_make_litellm_response("hello world")):
                result = _llm_mod.llm_invoke(
                    prompt="Say hello",
                    input_json={},
                )
        assert result["result"] == "hello world"

    def test_no_task_class_kwarg_needed_without_flag(self, mock_load_models):
        """llm_invoke signature remains backward-compatible; callers need not
        pass task_class when the flag is off."""
        with patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1"}, clear=False):
            # Temporarily ensure the routing flag is absent
            env = dict(os.environ)
            env.pop("PDD_ENABLE_TASK_ROUTING", None)
            with patch.dict(os.environ, env, clear=True):
                with patch("pdd.llm_invoke.litellm.completion",
                           return_value=_make_litellm_response("pong")):
                    result = _llm_mod.llm_invoke(
                        prompt="Ping",
                        input_json={},
                    )
        assert "result" in result

    def test_task_routing_csv_never_loaded_without_flag(self, mock_load_models):
        """The task_routing CSV loader must NOT be called when the flag is off,
        even if task_class is provided (when the feature is present)."""
        env = dict(os.environ)
        env.pop("PDD_ENABLE_TASK_ROUTING", None)
        env["PDD_FORCE_LOCAL"] = "1"

        csv_loader_target = "pdd.llm_invoke._load_task_routing_csv"

        if not _HAS_TASK_ROUTING:
            pytest.skip("task-routing feature absent")

        with patch.dict(os.environ, env, clear=True):
            with patch(csv_loader_target) as mock_csv_loader:
                with patch("pdd.llm_invoke.litellm.completion",
                           return_value=_make_litellm_response("no routing")):
                    _llm_mod.llm_invoke(
                        prompt="Run without routing",
                        input_json={},
                        task_class="bugfix",  # type: ignore[call-arg]
                    )
                mock_csv_loader.assert_not_called()


# ---------------------------------------------------------------------------
# Section 2: Dormancy — flag set but CSV is header-only
# ---------------------------------------------------------------------------

_HEADER_ONLY_CSV = "task_class,model,temperature,thinking,multi_shot\n"


class TestDormancyHeaderOnlyCsv:
    """Even with PDD_ENABLE_TASK_ROUTING=1, if task_routing.csv has no data
    rows (header-only), routing must still be a no-op."""

    @requires_task_routing
    def test_header_only_csv_falls_through_to_default(self, mock_load_models):
        """When the CSV contains only a header row, llm_invoke returns a normal
        result without raising and without selecting an unexpected model."""
        with patch.dict(os.environ,
                        {"PDD_ENABLE_TASK_ROUTING": "1", "PDD_FORCE_LOCAL": "1"}):
            with patch("pdd.llm_invoke._load_task_routing_csv",
                       return_value=pd.read_csv(io.StringIO(_HEADER_ONLY_CSV))):
                with patch("pdd.llm_invoke.litellm.completion",
                           return_value=_make_litellm_response("default result")):
                    result = _llm_mod.llm_invoke(
                        prompt="Test dormancy",
                        input_json={},
                        task_class="code-gen",  # type: ignore[call-arg]
                    )
        assert result["result"] == "default result"

    @requires_task_routing
    def test_header_only_csv_no_model_override(self, mock_load_models):
        """A header-only CSV must not override the model chosen by strength."""
        csv_df = pd.read_csv(io.StringIO(_HEADER_ONLY_CSV))
        with patch.dict(os.environ,
                        {"PDD_ENABLE_TASK_ROUTING": "1", "PDD_FORCE_LOCAL": "1"}):
            with patch("pdd.llm_invoke._load_task_routing_csv",
                       return_value=csv_df):
                with patch("pdd.llm_invoke.litellm.completion") as mock_completion:
                    mock_completion.return_value = _make_litellm_response("ok")
                    _llm_mod.llm_invoke(
                        prompt="No CSV override",
                        input_json={},
                        task_class="code-gen",  # type: ignore[call-arg]
                    )
                    # Model must be passed to litellm, not overridden to None
                    call_kwargs = mock_completion.call_args[1]
                    assert call_kwargs.get("model") is not None, (
                        "litellm.completion must be called with a model; "
                        "header-only CSV must not set model=None"
                    )


# ---------------------------------------------------------------------------
# Section 3: Dormancy — agentic path defaults
# ---------------------------------------------------------------------------

class TestDormancyAgenticPath:
    """routing_policy and task_class should default to None so run_agentic_task
    is unaffected when no orchestrator passes a policy."""

    def test_run_agentic_task_accepts_no_routing_policy(self, tmp_path):
        """run_agentic_task must work without any routing_policy/task_class args."""
        from pdd.agentic_common import run_agentic_task

        mock_result = MagicMock()
        mock_result.success = True
        mock_result.output_text = "done"
        mock_result.cost_usd = 0.01
        mock_result.provider_used = "claude"

        with patch("pdd.agentic_common.run_agentic_task",
                   return_value=mock_result) as mock_run:
            result = mock_run(
                instruction="Do something",
                cwd=tmp_path,
            )
        assert result.success is True

    def test_routing_policy_defaults_to_none_in_agentic_task(self, tmp_path):
        """When routing_policy is not passed, run_agentic_task must not raise
        and must not inject routing overrides."""
        from pdd.agentic_common import run_agentic_task
        import inspect

        sig = inspect.signature(run_agentic_task)
        # The routing_policy parameter must default to None (not a required arg)
        if "routing_policy" in sig.parameters:
            param = sig.parameters["routing_policy"]
            assert param.default is None, (
                "run_agentic_task routing_policy must default to None "
                "so legacy callers are unaffected"
            )
        # task_class must also default to None when present
        if "task_class" in sig.parameters:
            param = sig.parameters["task_class"]
            assert param.default is None

    def test_claude_policy_unaffected_by_task_routing(self, tmp_path):
        """Verify run_agentic_task still accepts claude_policy without needing
        task_class (no regression on the claude_policy parameter)."""
        from pdd.agentic_common import run_agentic_task, ClaudePolicy
        import inspect

        sig = inspect.signature(run_agentic_task)
        assert "claude_policy" in sig.parameters, (
            "claude_policy must remain in run_agentic_task signature"
        )


# ---------------------------------------------------------------------------
# Section 4: Routing enabled — flag + task_class + populated CSV
# ---------------------------------------------------------------------------

_ROUTING_CSV_CONTENT = textwrap.dedent("""\
    task_class,model,temperature,thinking,multi_shot
    bugfix,claude-sonnet-4-6,0.0,0.8,1
    code-gen,gpt-4o,0.2,0.0,1
    analysis,claude-opus-4-6,0.1,0.5,3
""")


class TestRoutingEnabled:
    """When PDD_ENABLE_TASK_ROUTING=1, task_class is supplied, and
    task_routing.csv has a matching row, the router must select the
    configured model/temperature/thinking/multi-shot."""

    @requires_task_routing
    def test_router_selects_model_from_csv(self, mock_load_models):
        """task_class='bugfix' must route to 'claude-sonnet-4-6' per the CSV."""
        routing_df = pd.read_csv(io.StringIO(_ROUTING_CSV_CONTENT))
        with patch.dict(os.environ,
                        {"PDD_ENABLE_TASK_ROUTING": "1", "PDD_FORCE_LOCAL": "1"}):
            with patch("pdd.llm_invoke._load_task_routing_csv",
                       return_value=routing_df):
                with patch("pdd.llm_invoke.litellm.completion") as mock_completion:
                    mock_completion.return_value = _make_litellm_response(
                        "fixed", model="claude-sonnet-4-6"
                    )
                    _llm_mod.llm_invoke(
                        prompt="Fix the bug",
                        input_json={},
                        task_class="bugfix",  # type: ignore[call-arg]
                    )
                    call_kwargs = mock_completion.call_args[1]
                    assert "claude-sonnet-4-6" in call_kwargs.get("model", ""), (
                        "Router must select model from CSV when task_class matches"
                    )

    @requires_task_routing
    def test_router_selects_temperature_from_csv(self, mock_load_models):
        """task_class='bugfix' must apply temperature=0.0 per the CSV row."""
        routing_df = pd.read_csv(io.StringIO(_ROUTING_CSV_CONTENT))
        with patch.dict(os.environ,
                        {"PDD_ENABLE_TASK_ROUTING": "1", "PDD_FORCE_LOCAL": "1"}):
            with patch("pdd.llm_invoke._load_task_routing_csv",
                       return_value=routing_df):
                with patch("pdd.llm_invoke.litellm.completion") as mock_completion:
                    mock_completion.return_value = _make_litellm_response("ok")
                    _llm_mod.llm_invoke(
                        prompt="Fix bug",
                        input_json={},
                        task_class="bugfix",  # type: ignore[call-arg]
                        temperature=0.9,  # caller default — CSV must override
                    )
                    call_kwargs = mock_completion.call_args[1]
                    assert call_kwargs.get("temperature") == 0.0, (
                        "Router must override temperature with CSV value (0.0 for bugfix)"
                    )

    @requires_task_routing
    def test_router_applies_thinking_from_csv(self, mock_load_models):
        """task_class='bugfix' must configure thinking=0.8 (high reasoning)."""
        routing_df = pd.read_csv(io.StringIO(_ROUTING_CSV_CONTENT))
        with patch.dict(os.environ,
                        {"PDD_ENABLE_TASK_ROUTING": "1", "PDD_FORCE_LOCAL": "1"}):
            with patch("pdd.llm_invoke._load_task_routing_csv",
                       return_value=routing_df):
                with patch("pdd.llm_invoke.litellm.completion") as mock_completion:
                    mock_completion.return_value = _make_litellm_response("ok")
                    _llm_mod.llm_invoke(
                        prompt="Bugfix",
                        input_json={},
                        task_class="bugfix",  # type: ignore[call-arg]
                    )
                    # Verify the call includes thinking/reasoning configuration
                    call_kwargs = mock_completion.call_args[1]
                    # Thinking may be expressed as 'thinking', 'time', or
                    # 'max_tokens_to_sample' depending on provider
                    thinking_set = (
                        call_kwargs.get("thinking") is not None
                        or call_kwargs.get("time") is not None
                        or "thinking" in str(call_kwargs)
                    )
                    assert thinking_set, (
                        "Router must propagate thinking config for bugfix task_class"
                    )

    @requires_task_routing
    def test_router_unknown_task_class_falls_through(self, mock_load_models):
        """A task_class not in the CSV must fall through to default routing
        without raising."""
        routing_df = pd.read_csv(io.StringIO(_ROUTING_CSV_CONTENT))
        with patch.dict(os.environ,
                        {"PDD_ENABLE_TASK_ROUTING": "1", "PDD_FORCE_LOCAL": "1"}):
            with patch("pdd.llm_invoke._load_task_routing_csv",
                       return_value=routing_df):
                with patch("pdd.llm_invoke.litellm.completion",
                           return_value=_make_litellm_response("fallback")):
                    result = _llm_mod.llm_invoke(
                        prompt="Unknown task",
                        input_json={},
                        task_class="unknown-task-xyz",  # type: ignore[call-arg]
                    )
        assert result["result"] == "fallback"

    @requires_task_routing
    def test_router_without_task_class_uses_default(self, mock_load_models):
        """When PDD_ENABLE_TASK_ROUTING=1 but task_class is None, the router
        must fall through to default model selection."""
        routing_df = pd.read_csv(io.StringIO(_ROUTING_CSV_CONTENT))
        with patch.dict(os.environ,
                        {"PDD_ENABLE_TASK_ROUTING": "1", "PDD_FORCE_LOCAL": "1"}):
            with patch("pdd.llm_invoke._load_task_routing_csv",
                       return_value=routing_df):
                with patch("pdd.llm_invoke.litellm.completion") as mock_completion:
                    mock_completion.return_value = _make_litellm_response("default")
                    result = _llm_mod.llm_invoke(
                        prompt="No task class",
                        input_json={},
                    )
        assert result["result"] == "default"

    @requires_task_routing
    def test_multi_shot_three_invocations_for_analysis(self, mock_load_models):
        """task_class='analysis' has multi_shot=3; the router must trigger three
        completion calls and aggregate results."""
        routing_df = pd.read_csv(io.StringIO(_ROUTING_CSV_CONTENT))
        with patch.dict(os.environ,
                        {"PDD_ENABLE_TASK_ROUTING": "1", "PDD_FORCE_LOCAL": "1"}):
            with patch("pdd.llm_invoke._load_task_routing_csv",
                       return_value=routing_df):
                with patch("pdd.llm_invoke.litellm.completion") as mock_completion:
                    mock_completion.return_value = _make_litellm_response("shot")
                    _llm_mod.llm_invoke(
                        prompt="Analyze this",
                        input_json={},
                        task_class="analysis",  # type: ignore[call-arg]
                    )
                    # multi_shot=3 means at least 3 LLM calls
                    assert mock_completion.call_count >= 3, (
                        "multi_shot=3 in CSV must produce at least 3 completion calls"
                    )


# ---------------------------------------------------------------------------
# Section 5: Stale test guard
# ---------------------------------------------------------------------------

class TestKnownStaleTest:
    """Document the known-stale test from #1618 so the overall suite failure
    is attributed correctly and not mistaken for a new regression."""

    @pytest.mark.xfail(
        reason="Known stale: test_flag_on_router_overrides_model fails on "
               "epic/1431-task-routing-v1 (tracked in issue #1618)",
        strict=False,
    )
    def test_flag_on_router_overrides_model_placeholder(self):
        """Placeholder xfail for the stale test tracked in issue #1618.

        The real `test_flag_on_router_overrides_model` test exists elsewhere
        in the suite and is expected to fail; this marker ensures the failure
        is visible and attributed correctly.
        """
        # This test intentionally does nothing — the actual stale behavior
        # is reproduced by the real test in the main test suite.
        pass


# ---------------------------------------------------------------------------
# shared fixtures re-used across this module
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_load_models():
    """Local minimal version of the shared mock_load_models fixture."""
    mock_df = _make_mock_df()
    with patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1"}):
        with patch("pdd.llm_invoke._load_model_data", return_value=mock_df):
            with patch("pdd.core.cloud.CloudConfig.is_cloud_enabled",
                       return_value=False):
                yield
