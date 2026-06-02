# A0 vs A1 — primary benchmark comparison (PR #1280)

This document is the **headline** for [PR #1280](https://github.com/promptdriven/pdd/pull/1280).  
Epic [#833](https://github.com/promptdriven/pdd/issues/833) tracks the wider product vision; **this PR** ships a runnable A0 vs A1 benchmark.

## Question

> Does the PDD formalized workflow (A1) produce more **reviewable**, **verifiable**, and **implementation-ready** prompt artifacts than an ad-hoc A0 baseline on the **same** product requirement?

The benchmark compares **prompt quality**, not “did both arms eventually produce code.” Code/oracle economics are measured in **M2**; regeneration stability in **M3**.

## Arms (same task, different prompt authoring)

| | **A0** | **A1** |
|---|--------|--------|
| **Input** | Handwritten `corpus/tasks/<task>/A0.prompt` — prose `<requirements>` only | Same requirement, formalized to `experiments/<run>/<task>/A1.prompt` |
| **Represents** | What a developer might paste into an LLM without PDD structure | PDD SoT: `<vocabulary>`, `<contract_rules>`, `<acceptance_tests>`, optional `<formalization>`, coverage |
| **Not** | Artificially broken English | A0 prose **plus** more words — structure and machine checks |
| **Corpus path** | `corpus/tasks/*/A0.prompt` | `experiments/latest/<task>/A1.prompt` (from `formalize_a1.py` or checkup replay) |

**A2 (code baseline)** — reference pytest / hand-written implementation — remains in `run_benchmark.py` for schema compatibility only. **Do not use A2 for the formalization story.**

## What each arm produces (M1)

| Artifact | A0 | A1 |
|----------|----|----|
| Prompt file | `A0.prompt` | `A1.prompt` |
| `pdd checkup lint` | yes | yes |
| `pdd checkup contract check` | yes (often 0 rules) | yes |
| `pdd checkup coverage` | N/A if no rules | rule status: checked / test-only / … |
| Story seed (#820) | optional `stories_from_a0/` | `stories_from_a1/` with `## Covers` |
| Command log | — | `commands.jsonl` + formalize manifest |
| Economics | `null` placeholders until M2 | same |

## Metrics (deterministic, M1)

Computed in `pipelines/a0_vs_a1_metrics.py` from real checkup output (no LLM):

| Metric | What it measures | Better |
|--------|------------------|--------|
| `implementation_readiness_score` | Rubric: vocabulary, rules, traceability, lint, formalization | Higher |
| `contract_completeness_score` | `<contract_rules>` presence and count | Higher |
| `traceability_score` | Rules linked in coverage matrix | Higher |
| `ambiguity_count` | Lint warnings (`VAGUE_TERM_*`, etc.) | Lower |
| `acceptance_criteria_count` | Bullets under `<acceptance_tests>` | Higher |
| `formal_candidate_rules` | Rules marked for Z3 / formal tests | Higher (when applicable) |

Each task `result.json` includes an **`a0_vs_a1`** block with scores, deltas, and `metric_definitions`.

**Requires LLM:** only when running `run_experiment.py --allow-llm` to *produce* A1. **Scoring** A0 and A1 is deterministic.

## Tasks in this PR

| Task | A0 | A1 | Notes |
|------|----|----|-------|
| `email_validator` | corpus `A0.prompt` | formalized + Z3 candidates | Reference tier-B task |
| `refund_payment` | `tasks/refund_payment/prompts/adhoc.prompt` | `formalized.prompt` | Full contract/story fixture |
| `hello_fn`, `pi_digits`, `token_bucket`, `refund_handler` | corpus | M1 batch + M2/M3 experiments | See `corpus/manifest.yaml` |

Same **underlying requirement** per task; only the prompt authoring model differs.

## How to run (human-verifiable)

```bash
# Full PR smoke (no API keys)
bash benchmarks/formalization/scripts/touchpoint_pr1280.sh
```

**A0 vs A1 only (M1, deterministic formalize):**

```bash
pip install -e .
python benchmarks/formalization/pipelines/run_experiment.py \
  --output-dir /tmp/m1_a0_a1 \
  --tasks hello_fn \
  --dry-run
jq '.a0_vs_a1' /tmp/m1_a0_a1/hello_fn/result.json
```

**Static harness (hand-curated A0/A1 prompts, no formalize step):**

```bash
python benchmarks/formalization/run_benchmark.py \
  --tasks email_validator \
  --arms A0 A1 \
  --report
```

**Live formalization + M2 (API keys):**

```bash
python benchmarks/formalization/pipelines/run_experiment.py --allow-llm
python benchmarks/formalization/pipelines/run_generation_benchmark.py --allow-llm
```

## Milestones and A0 vs A1

| Milestone | A0 vs A1 role |
|-----------|----------------|
| **M1** | **Primary** — prompt checkability and `a0_vs_a1` scores |
| **M2** | Same tasks/arms; adds cost, oracle vs non-oracle pass rates |
| **M3** | Drift on M2 code; prompt arm (A0/A1) affects regen stability |

## Out of scope for this PR

- Beating hand-written reference code (A2) on every metric
- Full epic #833 Connect UI
- Mandatory live LLM in CI (use `--dry-run` / `--replay-fixtures`)

## Related docs

- [README.md](README.md) — quick start  
- [EXPERIMENT_DESIGN.md](EXPERIMENT_DESIGN.md) — M1/M2/M3 phases  
- [BUSINESS_VALUE.md](BUSINESS_VALUE.md) — economics narrative (M2+)  
- [COMMANDS.md](COMMANDS.md) — literal CLI commands  
