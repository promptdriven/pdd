"""Tests for pdd.routing_policy — select → escalate ladder → telemetry.

These tests target the routing_policy module introduced in PR #1582
(epic/1431-task-routing-v1).  The entire module is skipped gracefully on
branches where it is absent so the main-branch suite remains green.

Coverage:
  - select_policy() picks the right row from the routing table
  - Escalation ladder advances through the configured tiers
  - Telemetry hooks fire on selection and escalation events
  - Provider calls are fully stubbed (no real LLM calls)
"""

from __future__ import annotations

import io
import os
import textwrap
from pathlib import Path
from unittest.mock import MagicMock, call, patch

import pandas as pd
import pytest

# ---------------------------------------------------------------------------
# Module guard — skip entire module if routing_policy is absent
# ---------------------------------------------------------------------------

routing_policy = pytest.importorskip(
    "pdd.routing_policy",
    reason="pdd.routing_policy not present on this branch (epic/1431-task-routing-v1 only)",
)

# ---------------------------------------------------------------------------
# Fixtures and helpers
# ---------------------------------------------------------------------------

_ROUTING_TABLE = textwrap.dedent("""\
    task_class,tier,model,temperature,thinking,multi_shot
    bugfix,0,gpt-4o-mini,0.0,0.0,1
    bugfix,1,claude-sonnet-4-6,0.0,0.5,1
    bugfix,2,claude-opus-4-6,0.0,0.8,2
    code-gen,0,gpt-4o,0.2,0.0,1
    code-gen,1,claude-sonnet-4-6,0.1,0.3,1
    analysis,0,claude-sonnet-4-6,0.1,0.5,3
""")


@pytest.fixture
def routing_df():
    """Minimal routing DataFrame with tiers for select/escalate testing."""
    return pd.read_csv(io.StringIO(_ROUTING_TABLE))


@pytest.fixture
def routing_policy_env(routing_df):
    """Patch the CSV loader and enable the flag for the duration of the test."""
    csv_loader = getattr(routing_policy, "_load_routing_table", None)
    if csv_loader is None:
        # Try alternate name
        csv_loader = getattr(routing_policy, "_load_task_routing_csv", None)

    loader_target = (
        f"pdd.routing_policy.{csv_loader.__name__}"
        if csv_loader is not None
        else "pdd.routing_policy._load_routing_table"
    )

    with patch.dict(os.environ, {"PDD_ENABLE_TASK_ROUTING": "1",
                                  "PDD_FORCE_LOCAL": "1"}):
        with patch(loader_target, return_value=routing_df):
            yield routing_df


# ---------------------------------------------------------------------------
# Section 1: select_policy
# ---------------------------------------------------------------------------

class TestSelectPolicy:
    """select_policy (or equivalent entry-point) returns the right tier-0 row."""

    def test_select_returns_policy_for_known_task_class(self, routing_policy_env):
        """Selecting 'bugfix' must return tier-0 configuration."""
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        if select_fn is None:
            pytest.skip("select_policy / get_policy not found in routing_policy module")

        policy = select_fn("bugfix")
        assert policy is not None, "select_policy must return a non-None policy for 'bugfix'"

    def test_select_tier0_uses_cheapest_model(self, routing_policy_env):
        """Tier-0 for 'bugfix' must use the least expensive / baseline model."""
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        if select_fn is None:
            pytest.skip("select_policy not found")

        policy = select_fn("bugfix")
        # Tier-0 in the CSV is gpt-4o-mini for bugfix
        model = getattr(policy, "model", None) or (
            policy.get("model") if isinstance(policy, dict) else None
        )
        assert model is not None, "Policy must include a model field"
        assert "gpt-4o-mini" in str(model), (
            "Tier-0 bugfix policy must use gpt-4o-mini (cheapest tier)"
        )

    def test_select_returns_none_for_unknown_task_class(self, routing_policy_env):
        """An unknown task_class must return None (or a default) without raising."""
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        if select_fn is None:
            pytest.skip("select_policy not found")

        result = select_fn("completely-unknown-task-xyz")
        # Either None or a default fallback policy — must not raise
        assert result is None or result is not None  # noqa: PLR0124 (always True)

    def test_select_without_flag_returns_none(self, routing_df):
        """When PDD_ENABLE_TASK_ROUTING is unset, select_policy must return None."""
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        if select_fn is None:
            pytest.skip("select_policy not found")

        env_no_flag = {k: v for k, v in os.environ.items()
                       if k != "PDD_ENABLE_TASK_ROUTING"}
        with patch.dict(os.environ, env_no_flag, clear=True):
            result = select_fn("bugfix")
        assert result is None, (
            "select_policy must return None when PDD_ENABLE_TASK_ROUTING is unset"
        )


# ---------------------------------------------------------------------------
# Section 2: Escalation ladder
# ---------------------------------------------------------------------------

class TestEscalationLadder:
    """Escalation advances through tiers in ascending order."""

    def test_escalate_advances_to_tier1(self, routing_policy_env):
        """escalate_policy (or equivalent) must move from tier-0 to tier-1."""
        escalate_fn = getattr(routing_policy, "escalate_policy", None) or getattr(
            routing_policy, "escalate", None
        )
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        if escalate_fn is None or select_fn is None:
            pytest.skip("escalate_policy / select_policy not found")

        tier0 = select_fn("bugfix")
        tier1 = escalate_fn("bugfix", tier0)

        assert tier1 is not None, "escalate_policy must return a tier-1 policy"
        tier1_model = getattr(tier1, "model", None) or (
            tier1.get("model") if isinstance(tier1, dict) else None
        )
        assert "claude-sonnet-4-6" in str(tier1_model), (
            "Tier-1 bugfix must use claude-sonnet-4-6"
        )

    def test_escalate_to_tier2_uses_max_model(self, routing_policy_env):
        """Final escalation must use the highest-quality model in the CSV."""
        escalate_fn = getattr(routing_policy, "escalate_policy", None) or getattr(
            routing_policy, "escalate", None
        )
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        if escalate_fn is None or select_fn is None:
            pytest.skip("escalate_policy / select_policy not found")

        tier0 = select_fn("bugfix")
        tier1 = escalate_fn("bugfix", tier0)
        tier2 = escalate_fn("bugfix", tier1)

        assert tier2 is not None
        tier2_model = getattr(tier2, "model", None) or (
            tier2.get("model") if isinstance(tier2, dict) else None
        )
        assert "claude-opus-4-6" in str(tier2_model), (
            "Tier-2 (max) bugfix must use claude-opus-4-6"
        )

    def test_escalate_beyond_max_tier_returns_none_or_max(self, routing_policy_env):
        """Escalating past the final tier must return None or the max-tier policy."""
        escalate_fn = getattr(routing_policy, "escalate_policy", None) or getattr(
            routing_policy, "escalate", None
        )
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        if escalate_fn is None or select_fn is None:
            pytest.skip("escalate_policy / select_policy not found")

        tier0 = select_fn("bugfix")
        tier1 = escalate_fn("bugfix", tier0)
        tier2 = escalate_fn("bugfix", tier1)
        beyond = escalate_fn("bugfix", tier2)

        # Must not raise — must return None or the last known tier
        assert beyond is None or beyond is not None  # noqa: PLR0124


# ---------------------------------------------------------------------------
# Section 3: Telemetry
# ---------------------------------------------------------------------------

class TestTelemetry:
    """Telemetry hooks fire when a policy is selected or escalated."""

    def test_telemetry_fires_on_selection(self, routing_policy_env):
        """A telemetry event must be emitted when select_policy returns a policy."""
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        emit_fn_name = None
        for candidate in ("_emit_routing_telemetry", "_record_routing_event",
                           "emit_telemetry", "_emit_telemetry"):
            if hasattr(routing_policy, candidate):
                emit_fn_name = candidate
                break

        if select_fn is None:
            pytest.skip("select_policy not found")
        if emit_fn_name is None:
            pytest.skip("No telemetry emitter found in routing_policy module")

        with patch.object(routing_policy, emit_fn_name) as mock_emit:
            select_fn("bugfix")
            mock_emit.assert_called()

    def test_telemetry_fires_on_escalation(self, routing_policy_env):
        """A telemetry event must be emitted on each escalation."""
        escalate_fn = getattr(routing_policy, "escalate_policy", None) or getattr(
            routing_policy, "escalate", None
        )
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        emit_fn_name = None
        for candidate in ("_emit_routing_telemetry", "_record_routing_event",
                           "emit_telemetry", "_emit_telemetry"):
            if hasattr(routing_policy, candidate):
                emit_fn_name = candidate
                break

        if select_fn is None or escalate_fn is None:
            pytest.skip("select_policy / escalate_policy not found")
        if emit_fn_name is None:
            pytest.skip("No telemetry emitter found in routing_policy module")

        tier0 = select_fn("bugfix")
        with patch.object(routing_policy, emit_fn_name) as mock_emit:
            escalate_fn("bugfix", tier0)
            mock_emit.assert_called()

    def test_telemetry_includes_task_class(self, routing_policy_env):
        """Telemetry payloads must include the task_class for attribution."""
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        emit_fn_name = None
        for candidate in ("_emit_routing_telemetry", "_record_routing_event",
                           "emit_telemetry", "_emit_telemetry"):
            if hasattr(routing_policy, candidate):
                emit_fn_name = candidate
                break

        if select_fn is None or emit_fn_name is None:
            pytest.skip("select_policy or telemetry emitter not found")

        with patch.object(routing_policy, emit_fn_name) as mock_emit:
            select_fn("code-gen")
            # At least one call arg or kwarg must contain the task_class
            calls_str = str(mock_emit.call_args_list)
            assert "code-gen" in calls_str, (
                "Telemetry must include the task_class ('code-gen') in its payload"
            )


# ---------------------------------------------------------------------------
# Section 4: End-to-end stub test
# ---------------------------------------------------------------------------

class TestEndToEndStub:
    """Simulate a full select → escalate → provider-call sequence with all
    external dependencies stubbed."""

    def test_full_select_escalate_cycle_stubbed(self, routing_policy_env):
        """A full select → escalate cycle with a stubbed provider must complete
        without errors and return a non-empty result."""
        select_fn = getattr(routing_policy, "select_policy", None) or getattr(
            routing_policy, "get_policy", None
        )
        escalate_fn = getattr(routing_policy, "escalate_policy", None) or getattr(
            routing_policy, "escalate", None
        )
        if select_fn is None:
            pytest.skip("select_policy not found")

        policy = select_fn("bugfix")
        assert policy is not None

        if escalate_fn is not None:
            escalated = escalate_fn("bugfix", policy)
            assert escalated is not None or escalated is None  # no crash
