from __future__ import annotations

import json
import time

import pytest

from pdd.routing_policy import (
    RoutingConfig,
    RoutingRecord,
    default_policy,
    emit_routing_record,
    escalate,
    load_policy,
    resolve_model_for_tier,
    select_config,
)


def test_default_policy_has_task_class_rows_and_default_fallback():
    policy = default_policy()

    assert policy.rows["bug-fix"].initial_config == RoutingConfig(
        harness="anthropic",
        model_tier=2,
        thinking_effort="medium",
        repeat_runs=1,
    )
    assert len(policy.rows["bug-fix"].escalation_steps) == 4
    assert policy.rows["architecture"].initial_config.model_tier == 1
    assert policy.rows["default"].initial_config is None


def test_load_policy_merges_yaml_rows_and_env_var(tmp_path, monkeypatch):
    policy_path = tmp_path / "routing.yaml"
    policy_path.write_text(
        """
version: "custom"
rows:
  bug-fix:
    initial_config:
      harness: google
      model_tier: 1
      thinking_effort: high
      repeat_runs: 2
  docs:
    initial_config:
      harness: anthropic
      model_tier: 3
      thinking_effort: low
      repeat_runs: 1
""",
        encoding="utf-8",
    )
    monkeypatch.setenv("PDD_ROUTING_POLICY", str(policy_path))

    policy = load_policy(None)

    assert policy.version == "custom"
    assert policy.path == policy_path
    assert policy.rows["bug-fix"].initial_config.harness == "google"
    assert policy.rows["bug-fix"].initial_config.repeat_runs == 2
    assert policy.rows["feature"].initial_config.model_tier == 2
    assert policy.rows["docs"].initial_config.model_tier == 3


def test_load_policy_missing_explicit_path_raises(tmp_path):
    with pytest.raises(FileNotFoundError):
        load_policy(tmp_path / "missing.yaml")


def test_select_config_falls_back_for_unknown_task_class(monkeypatch):
    monkeypatch.setenv("PDD_JOB_ID", "job-1")
    config, record = select_config(default_policy(), "unknown", None, None)

    assert config is None
    assert record.job_id == "job-1"
    assert record.task_class == "default"
    assert record.fallback_reason == "no_policy_row"


def test_escalate_applies_steps_and_stops_on_budget_first():
    policy = default_policy()
    config, record = select_config(policy, "bug-fix", None, None)
    assert config is not None
    record.cost_usd = 10.0
    record.latency_seconds = 10.0

    next_config, next_record = escalate(policy, record, "fail", budget_remaining=100.0, deadline=time.monotonic() + 100)
    assert next_config.harness == "google"
    assert next_record.escalation_step == 1
    assert next_record.fallback_reason is None

    _, halted = escalate(policy, next_record, "fail", budget_remaining=1.0, deadline=time.monotonic() - 1)
    assert halted.fallback_reason == "budget_exhausted"


def test_escalate_exhausts_without_wrapping():
    policy = default_policy()
    _, record = select_config(policy, "bug-fix", None, None)

    for _ in range(4):
        _, record = escalate(policy, record, "fail", None, None)

    _, exhausted = escalate(policy, record, "fail", None, None)
    assert exhausted.escalation_step == 4
    assert exhausted.fallback_reason == "ladder_exhausted"


def test_resolve_model_for_tier_uses_deepswe_manifest():
    assert resolve_model_for_tier(1) == "gpt-5.6-sol"
    assert resolve_model_for_tier(1, provider="anthropic") == "gpt-5.5"
    assert resolve_model_for_tier(3) == "claude-opus-4-7"
    assert resolve_model_for_tier(999) is None


def test_emit_routing_record_serializes_config(tmp_path):
    record = RoutingRecord(
        timestamp_utc="2026-06-16T12:00:00Z",
        job_id="job-1",
        policy_version="1",
        task_class="bug-fix",
        selected_config=RoutingConfig(),
        verifier_result="pass",
    )

    emit_routing_record(record, tmp_path)

    rows = list(tmp_path.glob("routing-*.jsonl"))
    assert len(rows) == 1
    payload = json.loads(rows[0].read_text(encoding="utf-8"))
    assert payload["selected_config"]["harness"] == "anthropic"
    assert payload["verifier_result"] == "pass"


# ---------------------------------------------------------------------------
# Additional coverage: select_config happy-path + dormancy edge cases
# ---------------------------------------------------------------------------

def test_select_config_known_task_class_returns_non_none_config():
    """select_config must return a concrete RoutingConfig for a known task class."""
    policy = default_policy()
    config, record = select_config(policy, "bug-fix", None, None)

    assert config is not None
    assert config.model_tier == 2
    assert config.thinking_effort == "medium"
    assert record.task_class == "bug-fix"
    assert record.fallback_reason is None
    assert record.escalation_step == 0


def test_select_config_none_task_class_resolves_to_default_row():
    """None task_class must resolve to the 'default' row, which has no config."""
    policy = default_policy()
    config, record = select_config(policy, None, None, None)

    assert config is None
    assert record.task_class == "default"
    assert record.fallback_reason == "no_policy_row"


def test_escalate_halts_on_deadline_exhaustion():
    """escalate must return deadline_exhausted when the deadline has already passed."""
    policy = default_policy()
    _, record = select_config(policy, "bug-fix", None, None)
    record.latency_seconds = 1000.0  # estimated cost of next shot is very high

    # deadline in the past relative to monotonic clock
    past_deadline = time.monotonic() - 1
    _, halted = escalate(policy, record, "fail", budget_remaining=None, deadline=past_deadline)

    assert halted.fallback_reason == "deadline_exhausted"


def test_load_policy_malformed_row_type_falls_back_to_builtin_default(tmp_path, monkeypatch):
    """A YAML row whose value is not a mapping is ignored; the built-in default survives."""
    policy_path = tmp_path / "bad_row.yaml"
    policy_path.write_text(
        "rows:\n  bug-fix: not-a-mapping\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("PDD_ROUTING_POLICY", str(policy_path))

    policy = load_policy(None)

    # Malformed row type -> falls back to the built-in "bug-fix" default.
    assert policy.rows["bug-fix"].initial_config is not None
    assert policy.rows["bug-fix"].initial_config.model_tier == 2
