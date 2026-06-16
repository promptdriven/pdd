# Routing Policy

`.pdd/routing_policy.yaml` is an optional file that overrides the built-in
agentic CLI routing policy consumed by `pdd/routing_policy.py`. The policy is
read by `run_agentic_task()` (in `pdd/agentic_common.py`) when a
`routing_policy` argument is supplied to select the initial agentic config for
a task and to escalate through a bounded ladder on verifier failure.

When the file is absent, `load_policy(None)` returns built-in default rows
without error. When a non-None path is given and the file is missing, a
`FileNotFoundError` is raised (matching `gate_policy.py` behavior).

## Schema

```yaml
version: "1"
rows:
  bug-fix:
    initial_config:
      harness: anthropic
      model_tier: 2        # DeepSWE rank; 1 = highest solve rate
      thinking_effort: medium
      repeat_runs: 1
    escalation_steps:
      - axis: harness
        value: google
        reason: provider rotation on transport failure
      - axis: model_tier
        value: 1
        reason: capability failure – promote to rank-1 tier
      - axis: thinking_effort
        value: high
        reason: quality failure – increase reasoning depth
      - axis: repeat_runs
        value: 2
        reason: flaky verifier – add one repeat run
  default:
    initial_config: null    # pass through to orchestrator defaults
```

### Top-level fields

| Field | Type | Default | Meaning |
|-------|------|---------|---------|
| `version` | string | `"1"` | Schema version. |
| `rows` | mapping | built-in rows | Task-class keys → `RoutingPolicyRow`. Unknown task-class keys are accepted and extend the built-in defaults. |

### RoutingPolicyRow fields

| Field | Type | Required | Meaning |
|-------|------|----------|---------|
| `initial_config` | `RoutingConfig` or `null` | yes | Config to use before execution. `null` means fall through to orchestrator defaults and record `fallback_reason = "no_policy_row"`. |
| `escalation_steps` | list of `EscalationStep` | no | Ordered steps to apply after a verifier failure. Defaults to the 4 built-in steps above; user YAML may override with any number of steps. |

### RoutingConfig fields

| Field | Type | Default | Meaning |
|-------|------|---------|---------|
| `harness` | string | `"anthropic"` | Agentic CLI provider key (same tokens as `PDD_AGENTIC_PROVIDER`). |
| `model_tier` | int | `2` | DeepSWE leaderboard rank (1 = highest solve rate). Resolved against `pdd/data/deepswe_manifest.json` `model_rank_score`. |
| `thinking_effort` | `"low"` \| `"medium"` \| `"high"` | `"medium"` | Reasoning effort level forwarded as `reasoning_time` to `run_agentic_task`. |
| `repeat_runs` | int | `1` | Number of repeat runs when verifier fails. |

### EscalationStep fields

| Field | Type | Required | Meaning |
|-------|------|----------|---------|
| `axis` | `"harness"` \| `"model_tier"` \| `"thinking_effort"` \| `"repeat_runs"` | yes | Which config dimension to change. |
| `value` | any | yes | New value for the axis (type must match the RoutingConfig field). |
| `reason` | string | yes | Human-readable reason recorded in the `RoutingRecord`. |

## Task classes

Seven coarse task classes are recognised, drawn from the SWE-bench++ empirical
distribution and SWE Atlas professional-workflow categories:

| Task class | Empirical frequency | Built-in initial config |
|------------|--------------------|-----------------------|
| `bug-fix` | ~61 % | rank-2 model, medium effort, 1 run |
| `feature` | ~31 % | rank-2 model, medium effort, 1 run |
| `architecture` | ~4 % | rank-1 model, high effort, 1 run |
| `refactor` | ~2 % | rank-3 model, low effort, 1 run |
| `test` | ~1 % | rank-3 model, low effort, 1 run |
| `analysis` | ~1 % | rank-3 model, low effort, 1 run |
| `default` | fallback | pass through to orchestrator defaults |

`None` / missing task class is normalised to `"default"`.

## Escalation ladder

The ladder fires after a verifier failure. Before committing to the next step:

1. **Budget check** — halt if `budget_remaining < 1.5 × record.cost_usd`
   (i.e., the remaining budget must cover at least 1.5× what the previous
   attempt cost). If the check fails, `fallback_reason = "budget_exhausted"`
   is recorded.
2. **Deadline check** — `deadline - now() > step_latency_estimate`. Latency
   estimate uses the previous step's wall-clock time. If the check fails,
   escalation halts and `fallback_reason = "deadline_exhausted"` is recorded.
3. When both checks pass, the next `EscalationStep` is applied and
   `run_agentic_task` is called again with the updated config.

Escalation never wraps around: the step index is bounded by
`len(escalation_steps)`. Both checks can fire simultaneously; the
`fallback_reason` records whichever fired first.

## RoutingRecord telemetry

Every `run_agentic_task` call **when `routing_policy` is non-`None`** emits at
least one JSON line to `.pdd/agentic-logs/routing-{timestamp}.jsonl`; bounded
escalation emits one additional line per escalated config attempt:

```json
{
  "timestamp_utc": "2026-06-15T12:34:56Z",
  "job_id": "TfR92mpMXvT6OtjjUCOM",
  "policy_version": "1",
  "task_class": "bug-fix",
  "selected_config": {"harness": "anthropic", "model_tier": 2, "thinking_effort": "medium", "repeat_runs": 1},
  "escalation_step": 0,
  "fallback_reason": null,
  "cost_usd": 0.42,
  "latency_seconds": 47.3,
  "verifier_result": "pass"
}
```

| Field | Meaning |
|-------|---------|
| `policy_version` | `version` field from the loaded policy. |
| `task_class` | Resolved task class (post-normalisation). |
| `selected_config` | Config actually used for this invocation. |
| `escalation_step` | 0 = initial config, 1–N = escalation step index (N = number of steps in the policy row). |
| `fallback_reason` | `null` on success; `"no_policy_row"`, `"budget_exhausted"`, `"deadline_exhausted"`, or a structured string on halt. |
| `cost_usd` | Cumulative cost for this invocation. |
| `latency_seconds` | Wall-clock time for this invocation. |
| `verifier_result` | `"pass"` or `"fail"` from `AgenticTaskResult.success`. |

The file follows the same `.pdd/agentic-logs/` convention as
`session_YYYYMMDD_HHMMSS.jsonl` (see `_log_agentic_interaction` in
`pdd/agentic_common.py`).

## Fallback to orchestrator defaults

When no policy row matches the task class — either because the task class is
`"default"` or because the supplied class is not in the policy file — the
router passes through to the existing orchestrator defaults unchanged and
records `fallback_reason = "no_policy_row"` in the `RoutingRecord`. All
existing callers of `run_agentic_task` that omit `routing_policy` are
unaffected.

## Integration

Pass a loaded `RoutingPolicy` to `run_agentic_task` via the optional
`routing_policy` keyword argument (opt-in, `None` by default):

```python
from pdd.routing_policy import load_policy

policy = load_policy(Path(".pdd/routing_policy.yaml"))  # or None for defaults
result = run_agentic_task(
    instruction=...,
    cwd=worktree,
    routing_policy=policy,
    task_class="bug-fix",  # derive from issue labels or workflow context
)
```

## Environment variable

- **`PDD_ROUTING_POLICY`**: Path to a YAML file that overrides the built-in
  agentic routing policy used by `run_agentic_task`. When set,
  `routing_policy.load_policy()` loads task-class rows from this file and
  merges them with the built-in defaults; absent keys fall back to defaults.
  Unset by default.

## Related documents

- `docs/grounding_policy.md` — `.pdd/grounding_policy.yaml` schema for
  critical-module grounding requirements.
- `docs/evidence_manifest.md` — schema for generation evidence; routing records
  are separate JSONL under `.pdd/agentic-logs/`.
- `pdd/data/deepswe_manifest.json` — DeepSWE leaderboard snapshot used to
  resolve `model_tier` integers to concrete model IDs.
