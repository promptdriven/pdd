# Issue #1431: Task-Based Routing v1 Plan

## Objective

Route each PDD task to the cheapest configuration that is likely to pass the
hidden verifier, rather than using one global `strength` value for every task.
The v1 objective is:

```text
maximize E[hidden_pass] - lambda * expected_cost
subject to a caller-selected cost and latency budget
```

The routed configuration has four dimensions:

- `model`: a concrete row from `pdd/data/llm_model.csv`, selected by capability,
  provider availability, cost, structured-output support, and interaction
  constraints.
- `harness`: direct `llm_invoke` generation or an agentic harness such as the
  existing `pdd/agentic_*` orchestrators.
- `reasoning`: the current `--time`/reasoning-effort surface, including
  `reasoning_effort`, `max_reasoning_tokens`, and provider-specific
  `reasoning_type` handling.
- `shots`: one or more candidates plus verifier-backed selection.

The v1 router should be transparent and benchmark-driven: a static lookup keyed
by task class, with an escalation ladder fallback. Learned routing and bandit
exploration are explicitly out of scope until v1 beats the fixed-`strength`
baseline on the benchmark.

## Current Touchpoints

- `pdd/llm_invoke.py` chooses a model from `pdd/data/llm_model.csv` using
  `strength`, provider credentials, structured-output support, cost, and model
  fallback behavior.
- `pdd/reasoning.py` maps `--time` to `low` / `medium` / `high` reasoning
  effort. `llm_invoke.py` turns that into provider-specific budget or effort
  parameters using CSV fields such as `max_reasoning_tokens` and
  `reasoning_type`.
- `pdd/agentic_common.py` and `pdd/agentic_*` orchestrators are the existing
  harness surface for Codex, Claude Code, Gemini, and direct subprocess-backed
  agentic workflows.
- `research/repo-bloat-benchmark/design.md` defines the hidden-verifier
  benchmark methodology, run record schema, instrumentation, and fixed-task
  comparison discipline needed for routing data.
- `research/repo-bloat-benchmark/agentic_cli_search.md` explains why harness
  and retrieval family are real routing dimensions, not just implementation
  details.

## Likely Architecture

Add routing as a narrow layer above existing invocation surfaces:

1. **Task classification.** Extract coarse task features before invocation:
   command family (`generate`, `fix`, `change`, `sync`, `checkup`), language,
   prompt size, repo size, estimated context pressure, visible-test presence,
   structured-output requirement, and whether the task is single-file or
   multi-file.
2. **Config schema.** Represent candidate configs as data, not code branches:
   `{model_selector, harness, reasoning_effort_or_time, shots, temperature,
   budget_cap, feasibility_constraints}`.
3. **Policy lookup.** Load a versioned static lookup table produced from offline
   benchmark results. Missing task classes use the current fixed-`strength`
   behavior.
4. **Escalation ladder.** On verifier failure, escalate through a small ordered
   sequence: stronger model, more reasoning, more shots, then heavier agentic
   harness, stopping at the budget cap.
5. **Telemetry.** Record task class, chosen config, cost, latency, verifier
   result, and fallback/escalation step so later PRs can compare policy quality
   and decide whether learned routing is justified.

## Expected Affected Files

- `pdd/llm_invoke.py`: consume an explicit routed model/config only after the
  policy exists; keep existing `strength` selection as fallback.
- `pdd/reasoning.py`: keep the shared time-to-effort mapping as the canonical
  reasoning budget adapter.
- `pdd/agentic_common.py` and `pdd/agentic_*`: expose harness capability and cost
  metadata without changing agent behavior.
- `pdd/data/llm_model.csv`: remain the model inventory and cost/capability
  source; do not encode task policy directly into this CSV.
- `research/repo-bloat-benchmark/`: add routing benchmark axes and reports while
  preserving hidden-verifier isolation.
- Tests under `tests/`: cover config parsing, policy fallback, escalation order,
  feasibility filtering, and telemetry shape once implementation begins.

## PR Breakdown

1. **Analysis/design: decide which LLM/config is best for a task.**
   Define the config space, benchmark objective, task classes, and data needed
   for a static v1 policy. No runtime routing.
2. **Benchmark axis extension.**
   Extend the repo-bloat benchmark run schema and harness design so
   `(model, harness, reasoning, shots)` can vary while task fixtures remain
   fixed.
3. **Routing config schema and feasibility filter.**
   Add typed config objects and validation for model availability,
   structured-output support, provider constraints, and budget caps.
4. **Static lookup policy behind a flag.**
   Load a checked-in policy artifact, classify tasks coarsely, choose a config,
   and fall back to current `strength` behavior when no policy applies.
5. **Escalation ladder behind the same flag.**
   Retry failed verifier-backed runs through a bounded ladder and record each
   escalation.
6. **Benchmark report and go/no-go decision.**
   Compare v1 routing with fixed `strength` on the benchmark task classes and
   decide whether learned or bandit routing has enough measured headroom.

## v1 Non-Goals

- No learned router, bandit policy, or online exploration.
- No full model sweep at runtime.
- No provider-specific rewrite beyond existing capability/feasibility checks.
- No new hidden-verifier semantics; reuse the #1209 benchmark methodology.
- No removal of `strength`; it remains the compatibility fallback and control
  baseline.

## Implementation Guardrails

- Keep the policy auditable: every routed decision should point to a task class,
  config id, policy version, and fallback reason if routing is skipped.
- Keep task classes coarse until benchmark data proves finer splits matter.
- Version-pin benchmark data, model CSV rows, CLI/tool versions, and run dates;
  model and harness behavior are nonstationary.
- Optimize for hidden-verifier pass rate under cost, not visible-test pass or
  model self-report.
