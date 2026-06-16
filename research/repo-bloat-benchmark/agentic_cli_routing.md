# Agentic CLI Routing Design

**Issue:** [#1585](https://github.com/promptdriven/pdd/issues/1585)  
**Parent:** [#1431](https://github.com/promptdriven/pdd/issues/1431), epic PR
[#1582](https://github.com/promptdriven/pdd/pull/1582)  
**Scope:** route external agentic CLI harness configuration by task class.

## Goal

Define the v1 routing plan for tasks that leave direct `llm_invoke` generation
and run through an external agentic harness under `pdd/agentic_*`. In this
column, PDD chooses:

```text
(harness, cli_model, cli_thinking_effort, repeat_runs)
```

Temperature is not part of the v1 config space because the CLIs do not expose a
uniform temperature knob.

## Config Space

| Dimension | Agentic surface | v1 values |
|---|---|---|
| Harness | which orchestrator / CLI runs the task | Codex-style, Claude-style, Gemini-style where available |
| Model | CLI-specific model flag or config | cheap/default/strong tiers per CLI, only when exposed |
| Thinking | CLI-specific reasoning/effort flag | low, medium, high where supported |
| Shots | repeat the full CLI run and select by verifier | 1, 2, or bounded N repeat-runs |

Feasibility filtering is per harness: installed CLI, auth, sandbox support,
model availability, rate limits, transcript availability, and hidden-verifier
compatibility. PDD should not pretend every CLI supports the same controls.

## Cost and Usage Instrumentation

This column cannot route responsibly until usage is comparable across harnesses.
The #1430 §6 caveat becomes implementation work here:

- capture token/cost/usage from each CLI when exposed directly;
- record when a CLI only exposes partial usage and mark cost as estimated;
- include repeat-run cost, not just the winning run;
- pin CLI versions and model identifiers in every run record;
- keep transcript/tool-boundary taps separate from filesystem taps, because
  retrieval mechanisms differ by agent.

If cost cannot be normalized for a harness, that harness can still be benchmarked
for pass rate, but it should not be used in an `E[pass] - lambda * cost` policy
row until the reward signal is comparable.

## Evaluation Objective

Use the same parent objective after cost normalization:

```text
utility = hidden_pass_rate - lambda * mean_cost
```

Report latency, timeout rate, wrong-file edit rate, localization misses,
hidden-contract misses, files read before first edit, and distractor context
share where the transcript tap supports it.

## Benchmark Extension

For the CLI column, extend the #1209/#1419 benchmark axis so task fixtures stay
fixed while `(harness, model, thinking, repeat_runs)` varies. Each run record
needs the agentic config identity:

- harness id and CLI version
- requested CLI model and resolved model where observable
- requested thinking/effort flag and whether the CLI accepted it
- repeat-run count and candidate-selection rule
- normalized cost and usage source
- sandbox/capability fingerprint
- verifier result and failure class

The baseline is the current default agentic harness behavior for the task type,
with one run and no router-selected escalation.

## Task Classes

Start with coarse classes where harness choice plausibly matters:

| Task class | Agentic-CLI hypothesis |
|---|---|
| Multi-file bug fix | harness and search behavior may dominate model choice |
| Repo-scale sync/change | stronger CLI harness or higher effort may beat direct generation |
| E2E fix/verification loop | repeat-runs are expensive; escalate only after verifier failure |
| Large-context localization | tool/search strategy is part of the config, not incidental |
| Benchmark/research task | keep config fixed unless the benchmark is explicitly comparing harnesses |

Do not add learned harness selection until static classes show repeated,
measurable utility differences.

## v1 Policy Shape

The implementation PR should produce reviewable static policy rows:

```json
{
  "task_class": "multi_file_bug_fix",
  "column": "agentic_cli",
  "policy_version": "2026-06-v1",
  "primary_config_id": "codex.default.medium.runs1",
  "escalation_config_ids": [
    "codex.strong.medium.runs1",
    "claude.strong.high.runs1",
    "codex.strong.high.runs2"
  ],
  "budget_cap_usd": 5.0,
  "usage_source": "normalized_cli_usage",
  "evidence_report": "research/repo-bloat-benchmark/reports/<run_id>/summary.md"
}
```

Missing task classes fall back to current orchestrator defaults.

## Non-Goals

- No direct `llm_invoke` temperature/model/thinking/multi-shot routing; that
  belongs to #1584.
- No learned router or bandit policy.
- No assumption that all CLIs expose the same knobs.
- No routing on cost until cost/usage instrumentation is comparable.
