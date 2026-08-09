# PDD Direct-Generation Routing Design

**Issue:** [#1584](https://github.com/promptdriven/pdd/issues/1584)
**Parent:** [#1431](https://github.com/promptdriven/pdd/issues/1431), epic PR
[#1582](https://github.com/promptdriven/pdd/pull/1582)
**Scope:** route native `llm_invoke` configuration by task class.

## Goal

Prove the routing thesis in the cheapest controllable column first: PDD direct
generation. In this path PDD owns the relevant knobs directly, so a v1 policy can
choose:

```text
(model, temperature, thinking_budget, shots)
```

for a task class and compare the result against today's fixed `strength`
baseline.

## Config Space

| Dimension | Native surface | v1 values |
|---|---|---|
| Model | `strength` selects a row from `pdd/data/llm_model.csv` by rank/cost | cheap, default, strong tiers represented by explicit model selectors |
| Temperature | `temperature` passed to `llm_invoke` where the provider supports it | deterministic/low plus one exploratory sampling value for multi-shot |
| Thinking | `--time` -> `pdd/reasoning.py` -> provider effort/budget handling in `llm_invoke.py` | low, medium, high |
| Shots | repeated direct generations plus verifier-backed selection | 1, 2, or 4 candidates under a budget cap |

Feasibility filtering must happen before a cell is benchmarked: provider
credentials, `interactive_only`, structured-output support, context limit,
provider temperature constraints, `reasoning_type`, `max_reasoning_tokens`, and
estimated cost all constrain the usable grid.

## Evaluation Objective

Use the same objective as the parent epic:

```text
utility = hidden_pass_rate - lambda * mean_cost
```

Report latency, timeout rate, visible pass rate, hidden-contract misses,
structured-output failures, and total shot cost separately. Hidden-verifier pass
is the verdict; visible tests and model self-report are diagnostics.

## Benchmark Extension

For the PDD column, extend the #1209/#1419 benchmark axis so task fixtures stay
fixed while `(model, temperature, thinking, shots)` varies. Each run record needs
the direct-generation config identity:

- model selector and resolved CSV row
- temperature requested and effective temperature after provider adjustments
- reasoning level and provider-specific reasoning payload
- shot count and candidate-selection rule
- cost and token totals across all shots
- verifier result and failure class

The fixed baseline is today's direct generation behavior: current `strength`,
current `temperature`, current `--time` mapping, and one shot.

## Task Classes

Start with coarse classes that PDD can derive without learned routing:

| Task class | Direct-generation hypothesis |
|---|---|
| Small single-file generation | cheap/default model, low or medium thinking, one shot |
| Structured-output generation | require structured-output-capable models; keep temperature low |
| Unit-test repair from visible error | default/strong model, medium thinking, two-shot if verifier is cheap |
| Prompt/code transformation | default model, low temperature, one or two shots |
| Benchmark/research task | keep config fixed to preserve experimental control |

Defer fine-grained splits until these coarse classes show repeated utility
differences.

## v1 Policy Shape

The implementation PR should produce a reviewable static policy row per task
class:

```json
{
  "task_class": "unit_test_repair",
  "column": "pdd_direct_generation",
  "policy_version": "2026-06-v1",
  "primary_config_id": "direct.default.medium.temp0.shots1",
  "escalation_config_ids": [
    "direct.strong.medium.temp0.shots1",
    "direct.strong.high.temp0_2.shots2"
  ],
  "budget_cap_usd": 2.0,
  "evidence_report": "research/repo-bloat-benchmark/reports/<run_id>/summary.md"
}
```

Missing task classes fall back to existing fixed-`strength` behavior.

## Non-Goals

- No external CLI harness routing; that belongs to #1585.
- No learned router or bandit policy.
- No exhaustive model sweep at runtime.
- No change to hidden-verifier semantics.
