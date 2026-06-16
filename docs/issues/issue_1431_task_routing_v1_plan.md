# Issue #1431: Task-Based Routing v1 Plan

## Objective

Route each PDD task to the cheapest configuration that is likely to pass the
hidden verifier, rather than using one global `strength` value for every task.
The v1 objective is:

```text
maximize E[hidden_pass] - lambda * expected_cost
subject to a caller-selected cost and latency budget
```

The routed configuration splits into two execution columns:

- **PDD direct generation (#1584):** route model, temperature, thinking budget,
  and multi-shot count through native `llm_invoke` controls.
- **Agentic CLI harnesses (#1585):** route harness choice, model, thinking
  budget, and repeat-run count through per-CLI flags and orchestrator behavior.
  Temperature is not a first-class dimension here because external CLIs usually
  do not expose it uniformly.

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

Add routing as a narrow layer above the two invocation surfaces:

1. **Task classification.** Extract coarse task features before invocation:
   command family (`generate`, `fix`, `change`, `sync`, `checkup`), language,
   prompt size, repo size, estimated context pressure, visible-test presence,
   structured-output requirement, and whether the task is single-file or
   multi-file.
2. **PDD direct config schema.** Represent native `llm_invoke` candidates as
   data: `{model_selector, temperature, reasoning_effort_or_time, shots,
   budget_cap, feasibility_constraints}`.
3. **Agentic CLI config schema.** Represent external harness candidates as
   data: `{harness, cli_model, cli_reasoning_flag, repeat_runs, budget_cap,
   feasibility_constraints}`.
4. **Policy lookup.** Load versioned static lookup tables produced from offline
   benchmark results. Missing task classes use the current fixed-`strength`
   behavior for direct generation or the current orchestrator defaults for
   agentic CLI paths.
5. **Escalation ladder.** On verifier failure, escalate within the active
   column through a small ordered sequence: stronger model, more reasoning, more
   shots or repeat-runs, then heavier harness where applicable, stopping at the
   budget cap.
6. **Telemetry.** Record task class, chosen config, cost, latency, verifier
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

## Child Issues

1. **#1584: PDD direct generation.** Route model, temperature, thinking tokens,
   and multi-shot count through `llm_invoke`. This is the cheapest place to
   prove the routing thesis against fixed `strength` because all four knobs are
   natively settable.
2. **#1585: Agentic CLI harnesses.** Route harness choice, model, thinking
   effort, and repeat-run count through `pdd/agentic_*` and per-CLI flags.
   Cross-CLI usage/cost instrumentation from #1430 §6 is part of this column
   because reward is not directly comparable until the harnesses report usage
   consistently.

Each child folds in its own share of the #1209 benchmark-axis extension and the
`E[pass] - lambda * cost` static-lookup plus escalation-ladder router. The
benchmark-axis extension is genuinely shared infrastructure; if implementation
starts duplicating harness work across #1584 and #1585, split that foundation
back out into a third issue.

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
