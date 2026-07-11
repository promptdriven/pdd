"""Example usage of pdd.routing_policy.

Demonstrates the static v1 routing policy end to end without any network
access or LLM credentials: pick an initial config for a task class, resolve
the config's DeepSWE model tier to a concrete model name (showing how the
GPT-5.6 Codex default is provider-scoped), escalate on a verifier failure,
and emit a structured routing record to a log directory.

Public API
----------
default_policy() -> RoutingPolicy
load_policy(path: Optional[Path]) -> RoutingPolicy
select_config(policy, task_class, budget_remaining, deadline)
    -> tuple[RoutingConfig | None, RoutingRecord]
escalate(policy, record, verifier_result, budget_remaining, deadline)
    -> tuple[RoutingConfig | None, RoutingRecord]
resolve_model_for_tier(tier: int, provider: Optional[str] = None) -> Optional[str]
emit_routing_record(record: RoutingRecord, log_dir: Path) -> None
"""

from __future__ import annotations

import tempfile
from pathlib import Path

from pdd.routing_policy import (
    default_policy,
    emit_routing_record,
    escalate,
    resolve_model_for_tier,
    select_config,
)


def main() -> None:
    policy = default_policy()

    # 1. Select the initial config for an "architecture" task (tier-1 work).
    config, record = select_config(policy, "architecture", None, None)
    assert config is not None
    print(f"selected: harness={config.harness} tier={config.model_tier} "
          f"effort={config.thinking_effort}")

    # 2. Resolve the tier to a concrete model. The GPT-5.6 Codex platform
    #    default is provider-scoped: only Codex (openai) — or an unscoped
    #    call — gets it; other providers keep the DeepSWE manifest tier-1.
    codex_model = resolve_model_for_tier(config.model_tier, provider="openai")
    claude_model = resolve_model_for_tier(config.model_tier, provider="anthropic")
    print(f"tier-{config.model_tier} model: openai={codex_model} "
          f"anthropic={claude_model}")  # e.g. openai=gpt-5.6-sol anthropic=gpt-5.5
    assert codex_model == "gpt-5.6-sol"      # Codex platform default
    assert claude_model != "gpt-5.6-sol"     # non-Codex keeps the manifest model

    # 3. Escalate once on a verifier failure to get the next bounded config.
    next_config, next_record = escalate(policy, record, "fail", None, None)
    print(f"escalated: step={next_record.escalation_step} "
          f"reason={next_record.fallback_reason}")

    # 4. Emit the routing record as one JSON line under a temp log dir.
    with tempfile.TemporaryDirectory() as tmp:
        log_dir = Path(tmp) / ".pdd" / "agentic-logs"
        emit_routing_record(next_record, log_dir)
        written = list(log_dir.glob("routing-*.jsonl"))
        print(f"emitted {len(written)} routing record(s)")
        assert written


if __name__ == "__main__":
    main()
