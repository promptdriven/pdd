"""Static task-class routing table for agentic CLI config selection."""

from __future__ import annotations

import dataclasses
import json
import logging
import os
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

import yaml

from pdd.reasoning import EffortLevel
from pdd.model_defaults import CODEX_MODEL_DEFAULT


log = logging.getLogger(__name__)


@dataclass
class RoutingConfig:
    """Agentic CLI config selected by the routing policy."""

    harness: str = "anthropic"
    model_tier: int = 2
    thinking_effort: EffortLevel = "medium"
    repeat_runs: int = 1


@dataclass
class EscalationStep:
    """One bounded routing escalation action."""

    axis: str
    value: Any
    reason: str


@dataclass
class RoutingPolicyRow:
    """Policy row keyed by coarse task class."""

    initial_config: Optional[RoutingConfig]
    escalation_steps: List[EscalationStep] = field(default_factory=list)


@dataclass
class RoutingPolicy:
    """Resolved routing policy."""

    version: str = "1"
    rows: Dict[str, RoutingPolicyRow] = field(default_factory=dict)
    path: Optional[Path] = None


@dataclass
class RoutingRecord:
    """Structured routing telemetry for one selected config."""

    timestamp_utc: str
    job_id: Optional[str]
    policy_version: str
    task_class: str
    selected_config: Optional[RoutingConfig]
    escalation_step: int = 0
    fallback_reason: Optional[str] = None
    cost_usd: float = 0.0
    latency_seconds: float = 0.0
    verifier_result: Optional[str] = None


_MANIFEST_CACHE: Optional[list[dict[str, Any]]] = None


def _now_utc() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _default_steps() -> List[EscalationStep]:
    return [
        EscalationStep(
            axis="harness",
            value="google",
            reason="provider rotation on transport failure",
        ),
        EscalationStep(
            axis="model_tier",
            value=1,
            reason="capability failure - promote to rank-1 tier",
        ),
        EscalationStep(
            axis="thinking_effort",
            value="high",
            reason="quality failure - increase reasoning depth",
        ),
        EscalationStep(
            axis="repeat_runs",
            value=2,
            reason="flaky verifier - add one repeat run",
        ),
    ]


def _row(config: Optional[RoutingConfig]) -> RoutingPolicyRow:
    return RoutingPolicyRow(
        initial_config=config,
        escalation_steps=_default_steps() if config is not None else [],
    )


def default_policy() -> RoutingPolicy:
    """Return the built-in static v1 routing policy."""
    return RoutingPolicy(
        version="1",
        rows={
            "bug-fix": _row(RoutingConfig(model_tier=2, thinking_effort="medium", repeat_runs=1)),
            "feature": _row(RoutingConfig(model_tier=2, thinking_effort="medium", repeat_runs=1)),
            "architecture": _row(RoutingConfig(model_tier=1, thinking_effort="high", repeat_runs=1)),
            "refactor": _row(RoutingConfig(model_tier=3, thinking_effort="low", repeat_runs=1)),
            "test": _row(RoutingConfig(model_tier=3, thinking_effort="low", repeat_runs=1)),
            "analysis": _row(RoutingConfig(model_tier=3, thinking_effort="low", repeat_runs=1)),
            "default": RoutingPolicyRow(initial_config=None),
        },
    )


def load_policy(path: Optional[Path]) -> RoutingPolicy:
    """Load routing policy YAML, merging rows over the built-in defaults."""
    if path is None:
        env_path = os.environ.get("PDD_ROUTING_POLICY", "").strip()
        path = Path(env_path) if env_path else None
    policy = default_policy()
    if path is None:
        return policy
    if not path.is_file():
        raise FileNotFoundError(f"Routing policy file not found: {path}")

    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as exc:
        log.warning("Could not parse routing policy YAML at %s: %s", path, exc)
        policy.path = path
        return policy

    if not isinstance(data, dict):
        log.warning("Routing policy YAML at %s must be a mapping; using defaults.", path)
        policy.path = path
        return policy

    policy.path = path
    version = data.get("version")
    if version is not None:
        policy.version = str(version)

    rows = data.get("rows")
    if rows is None:
        return policy
    if not isinstance(rows, dict):
        log.warning("Routing policy rows must be a mapping; using default rows.")
        return policy

    for task_class, raw_row in rows.items():
        if not isinstance(task_class, str):
            log.warning("Skipping routing row with non-string task class: %r", task_class)
            continue
        base = policy.rows.get(task_class, RoutingPolicyRow(initial_config=None))
        policy.rows[task_class] = _merge_row(base, raw_row, task_class)
    return policy


def _merge_row(
    base: RoutingPolicyRow,
    raw_row: Any,
    task_class: str,
) -> RoutingPolicyRow:
    if raw_row is None:
        return RoutingPolicyRow(initial_config=None, escalation_steps=list(base.escalation_steps))
    if not isinstance(raw_row, dict):
        log.warning("Skipping malformed routing row for %s; expected mapping.", task_class)
        return base

    initial = base.initial_config
    if "initial_config" in raw_row:
        initial = _parse_config(raw_row.get("initial_config"), initial, task_class)

    steps = list(base.escalation_steps)
    if "escalation_steps" in raw_row:
        parsed_steps = _parse_steps(raw_row.get("escalation_steps"), task_class)
        if parsed_steps is not None:
            steps = parsed_steps

    return RoutingPolicyRow(initial_config=initial, escalation_steps=steps)


def _parse_config(
    raw_config: Any,
    default: Optional[RoutingConfig],
    task_class: str,
) -> Optional[RoutingConfig]:
    if raw_config is None:
        return None
    if not isinstance(raw_config, dict):
        log.warning("Skipping malformed initial_config for %s; expected mapping.", task_class)
        return default

    values = dataclasses.asdict(default) if default is not None else dataclasses.asdict(RoutingConfig())
    for key in ("harness", "model_tier", "thinking_effort", "repeat_runs"):
        if key in raw_config:
            values[key] = raw_config[key]
    try:
        values["harness"] = str(values["harness"])
        values["model_tier"] = int(values["model_tier"])
        effort = str(values["thinking_effort"])
        values["thinking_effort"] = effort if effort in {"low", "medium", "high"} else "medium"
        values["repeat_runs"] = max(1, int(values["repeat_runs"]))
        return RoutingConfig(**values)
    except (TypeError, ValueError) as exc:
        log.warning("Skipping malformed initial_config for %s: %s", task_class, exc)
        return default


def _parse_steps(raw_steps: Any, task_class: str) -> Optional[List[EscalationStep]]:
    if raw_steps is None:
        return []
    if not isinstance(raw_steps, list):
        log.warning("Skipping malformed escalation_steps for %s; expected list.", task_class)
        return None

    steps: List[EscalationStep] = []
    for raw_step in raw_steps:
        if not isinstance(raw_step, dict):
            log.warning("Skipping malformed escalation step for %s: %r", task_class, raw_step)
            continue
        axis = raw_step.get("axis")
        if axis not in {"harness", "model_tier", "thinking_effort", "repeat_runs"}:
            log.warning("Skipping routing step for %s with unknown axis: %r", task_class, axis)
            continue
        steps.append(
            EscalationStep(
                axis=str(axis),
                value=raw_step.get("value"),
                reason=str(raw_step.get("reason") or ""),
            )
        )
    return steps


def select_config(
    policy: RoutingPolicy,
    task_class: Optional[str],
    budget_remaining: Optional[float],
    deadline: Optional[float],
) -> tuple[Optional[RoutingConfig], RoutingRecord]:
    """Select the initial config for ``task_class`` from ``policy``."""
    del budget_remaining, deadline
    resolved_class = task_class if task_class in policy.rows else "default"
    row = policy.rows.get(resolved_class) or policy.rows.get("default")
    selected = row.initial_config if row is not None else None
    fallback = "no_policy_row" if selected is None else None
    record = RoutingRecord(
        timestamp_utc=_now_utc(),
        job_id=os.environ.get("PDD_JOB_ID") or None,
        policy_version=policy.version,
        task_class=resolved_class,
        selected_config=dataclasses.replace(selected) if selected is not None else None,
        escalation_step=0,
        fallback_reason=fallback,
    )
    return (record.selected_config, record)


def escalate(
    policy: RoutingPolicy,
    record: RoutingRecord,
    verifier_result: str,
    budget_remaining: Optional[float],
    deadline: Optional[float],
) -> tuple[Optional[RoutingConfig], RoutingRecord]:
    """Apply the next bounded escalation step after verifier failure."""
    row = policy.rows.get(record.task_class) or policy.rows.get("default")
    steps = row.escalation_steps if row is not None else []
    next_index = record.escalation_step
    updated = dataclasses.replace(record, verifier_result=verifier_result)

    if next_index >= len(steps):
        updated.fallback_reason = "ladder_exhausted"
        return (updated.selected_config, updated)

    if budget_remaining is not None and budget_remaining < 1.5 * record.cost_usd:
        updated.fallback_reason = "budget_exhausted"
        return (updated.selected_config, updated)

    if deadline is not None:
        now = time.time() if deadline > 1_000_000_000 else time.monotonic()
        if deadline - now < record.latency_seconds:
            updated.fallback_reason = "deadline_exhausted"
            return (updated.selected_config, updated)

    config = dataclasses.replace(updated.selected_config or RoutingConfig())
    step = steps[next_index]
    try:
        if step.axis == "harness":
            config.harness = str(step.value)
        elif step.axis == "model_tier":
            config.model_tier = int(step.value)
        elif step.axis == "thinking_effort":
            effort = str(step.value)
            config.thinking_effort = effort if effort in {"low", "medium", "high"} else config.thinking_effort
        elif step.axis == "repeat_runs":
            config.repeat_runs = max(1, int(step.value))
    except (TypeError, ValueError) as exc:
        log.warning("Skipping malformed routing escalation value %r for %s: %s", step.value, step.axis, exc)
        updated.fallback_reason = f"invalid_escalation_step:{step.axis}"
        return (updated.selected_config, updated)

    updated.selected_config = config
    updated.escalation_step = next_index + 1
    updated.fallback_reason = None
    return (config, updated)


def _resolve_manifest_model_for_tier(tier: int) -> Optional[str]:
    """Resolve a DeepSWE rank tier without applying a platform default."""
    global _MANIFEST_CACHE
    if _MANIFEST_CACHE is None:
        manifest_path = Path(__file__).resolve().parent / "data" / "deepswe_manifest.json"
        try:
            data = json.loads(manifest_path.read_text(encoding="utf-8"))
            scores = data.get("scores") if isinstance(data, dict) else None
            _MANIFEST_CACHE = [item for item in scores if isinstance(item, dict)] if isinstance(scores, list) else []
        except (OSError, json.JSONDecodeError) as exc:
            log.warning("Could not load DeepSWE manifest: %s", exc)
            _MANIFEST_CACHE = []

    try:
        requested_tier = int(tier)
    except (TypeError, ValueError):
        return None

    ranked: list[dict[str, Any]] = []
    for item in _MANIFEST_CACHE:
        model = item.get("model")
        if not isinstance(model, str) or not model:
            continue
        score = item.get("model_rank_score")
        if score is None:
            solve_rate = item.get("solve_rate")
            score = 10000 + round(float(solve_rate) * 100) if isinstance(solve_rate, (int, float)) else None
        ranked.append(
            {
                "model": model,
                "rank": item.get("rank"),
                "score": float(score) if isinstance(score, (int, float)) else None,
            }
        )

    exact = [item for item in ranked if item.get("rank") == requested_tier]
    if exact:
        return str(max(exact, key=lambda item: item["score"] if item["score"] is not None else float("-inf"))["model"])

    by_score = sorted(
        (item for item in ranked if item["score"] is not None),
        key=lambda item: item["score"],
        reverse=True,
    )
    if 1 <= requested_tier <= len(by_score):
        return str(by_score[requested_tier - 1]["model"])
    return None


def resolve_model_for_tier(tier: int, provider: Optional[str] = None) -> Optional[str]:
    """Resolve a tier while keeping the Codex default provider-scoped."""
    try:
        requested_tier = int(tier)
    except (TypeError, ValueError):
        return None
    if requested_tier == 1 and (provider is None or provider.lower() in {"openai", "codex"}):
        return CODEX_MODEL_DEFAULT
    return _resolve_manifest_model_for_tier(requested_tier)


def emit_routing_record(record: RoutingRecord, log_dir: Path) -> None:
    """Append one JSON routing record under ``log_dir``."""
    try:
        log_dir.mkdir(parents=True, exist_ok=True)
        timestamp = record.timestamp_utc.replace(":", "-")
        path = log_dir / f"routing-{timestamp}.jsonl"
        payload = dataclasses.asdict(record)
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(payload, default=str) + "\n")
    except OSError:
        return
