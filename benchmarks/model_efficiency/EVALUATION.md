# Evaluation runbook — Experiment 2 (M4)

Technical reference for the model efficiency benchmark. For business framing see
[BUSINESS_VALUE.md](BUSINESS_VALUE.md). For Experiment 1 see
[../formalization/EVALUATION.md](../formalization/EVALUATION.md).

---

## Prerequisites

Same as Experiment 1:

```bash
pip install -e ".[dev]"
pdd setup                   # PDD Cloud auth (paid runs)
```

Experiment 2 reuses the formalization **corpus** (`formalization/corpus/`). Task metadata
comes from [`manifest.yaml`](manifest.yaml) → `formalization_corpus` path.

---

## Design

| Dimension | Default |
|-----------|---------|
| Smart tier | PDD Cloud, `--strength 1.0` → Opus class |
| Budget tier | PDD Cloud, `--strength 0.0` → cheapest / Gemini Flash class |
| Prompt arms | A0 (corpus), A1 (formalized once per task on smart tier) |
| Tasks | `email_validator`, `token_bucket`, `refund_handler` |
| Runs per cell | 3 |
| Total cells | 2 tiers × 2 arms × 3 tasks × 3 runs = **36** |

Both tiers use **PDD Cloud only** (`PDD_CLOUD_ONLY=1` from `experiment.cloud_only`).

The CLI sends **strength**, not a fixed model id. Verify actual models in
`economics.resolved_model` after the first paid run.

---

## CI smoke (no API keys)

```bash
bash benchmarks/model_efficiency/scripts/run_eval.sh
```

Or:

```bash
python benchmarks/model_efficiency/pipelines/run_model_efficiency.py \
  --harness-only \
  --tasks email_validator \
  --runs 1 \
  --output-dir benchmarks/model_efficiency/experiments/ci_smoke \
  --json
```

Harness mode:

- Replays `corpus/tier_gold/*/pdd_generated/` for code/tests
- Replays recorded `A1.prompt` via `cloud_formalize.replay_a1`
- Does **not** compare real cloud model routing or cost

---

## Paid experiment

```bash
python benchmarks/model_efficiency/pipelines/run_model_efficiency.py \
  --allow-llm \
  --output-dir benchmarks/model_efficiency/experiments/$(date +%Y%m%d) \
  --max-cost-usd 50
```

Subset / cheaper probe:

```bash
python benchmarks/model_efficiency/pipelines/run_model_efficiency.py \
  --allow-llm \
  --tasks email_validator \
  --runs 1 \
  --max-cost-usd 10
```

---

## Per-run flow

For each task:

1. **Formalize A1 once** (smart tier) unless `A1.prompt` already exists or `--harness-only`
2. For each `run_index` × `tier` × `arm`:
   - `run_generation_loop` with tier `pdd_strength` and cloud env
   - Oracle pytest from tier gold
   - Append economics to cell record

---

## Outputs

```
experiments/<run>/
  run_manifest.json       # full matrix + aggregate + core_comparison
  summary.json            # headline + core_comparison excerpt
  <task>/
    A1.prompt
    a1_provenance.json
    run_<n>/<tier>_<arm>/
      commands.jsonl
      generated/src/
      generated/tests/
    result.json           # per-task cell rollup
```

Inspect:

```bash
jq -r '.headline' benchmarks/model_efficiency/experiments/ci_smoke/summary.json

jq '.core_comparison.budget_A1_minus_smart_A0' \
  benchmarks/model_efficiency/experiments/ci_smoke/summary.json

jq '.cells[0].economics' \
  benchmarks/model_efficiency/experiments/ci_smoke/run_manifest.json
```

---

## Metrics reference

See [BUSINESS_VALUE.md](BUSINESS_VALUE.md). Key aggregates in `run_manifest.json`:

| Key | Meaning |
|-----|---------|
| `aggregate` | All cells combined |
| `core_comparison.budget_A1` | Budget tier, A1 arm stats |
| `core_comparison.smart_A0` | Smart tier, A0 arm stats |
| `core_comparison.budget_A1_minus_smart_A0` | Primary business deltas |

---

## Troubleshooting

| Symptom | Fix |
|---------|-----|
| `Unknown formalization tasks` | Restore `formalization/corpus/manifest.yaml` |
| Import error `generation_loop` | Ensure formalization pipeline sources are on branch |
| Cloud 402 | Top up credits or use `--harness-only` |
| Budget tier resolves to unexpected model | Check `commands.jsonl` `model_name`; tune strength in manifest |
| A1 missing in harness | Ensure `tier_gold/*/pdd_generated/A1.prompt` exists |

---

## Related

- [README.md](README.md)
- [../formalization/EVALUATION.md](../formalization/EVALUATION.md)
- [../PR.md](../PR.md)
