# Model Efficiency Benchmark (M4) — Experiment 2

**Overview:** [../README.md](../README.md) · **Business value:** [BUSINESS_VALUE.md](BUSINESS_VALUE.md) · **Runbook:** [EVALUATION.md](EVALUATION.md) · **PR:** [../PR.md](../PR.md)

**Core question:** Can PDD formalization reduce **cost-to-correct-code** by making budget cloud models more reliable?

This is a **separate experiment** from the core formalization benchmark (`../formalization/`). Run M1–M3 first; use M4 when you want the business story around model tier and token spend.

## Hypothesis

| Prompt | Model tier | Expected |
|--------|------------|----------|
| A0 vague | Smart | Good but costly |
| A1 formalized | Smart | Best quality, highest cost |
| A0 vague | Budget | Weak / unstable |
| A1 formalized | Budget | Better quality, lower cost-per-success |

**Primary comparison:** `budget + A1` vs `smart + A0`.

**Claim (realistic):** Formalization **narrows the gap** between budget and smart models — not that cheap models beat expensive ones outright.

## Models compared (default manifest)

Both tiers use **PDD Cloud** (`pdd generate`, `pdd test` — no `--local`). The open-source CLI sends **`--strength` only** to cloud endpoints; the cloud backend picks the model.

| Tier | PDD Cloud strength | Expected cloud model |
|------|-------------------|----------------------|
| **smart** | `1.0` | Opus class (`claude-opus-4-8`) |
| **budget** | `0.0` | Cheapest tier / Gemini Flash class (`gemini-2.5-flash`) |

Live runs set `PDD_CLOUD_ONLY=1` (see `experiment.cloud_only` in [`manifest.yaml`](manifest.yaml)) so cells fail instead of silently falling back to local API keys.

The **actual** model name returned by cloud is recorded in each cell’s `commands.jsonl` and `economics.resolved_model` — verify it matches expectations after your first paid run.

A1 formalization uses the **smart** tier (cloud + strength `1.0`) once per task before the tier × arm matrix.

## Artifact policy

| Artifact | Source |
|----------|--------|
| A0 prompt | Handcrafted `formalization/corpus/tasks/*/A0.prompt` |
| A1 prompt | `pdd generate` via `cloud_formalize` (or replay from `tier_gold/*/pdd_generated/A1.prompt` in CI) |
| Code | `pdd generate` |
| Tests | `pdd test` (+ optional `pdd fix` rounds) |
| Oracle tests | Hand-written `tier_gold/*/oracle_tests/` (evaluation only) |

## Design (default manifest)

- **2 cloud model tiers:** smart (strength 1.0), budget (strength 0.0)
- **2 prompt arms:** A0, A1
- **3 tasks:** `email_validator`, `token_bucket`, `refund_handler`
- **3 runs per cell** → 36 generations total

## Metrics

Per cell and aggregated:

- `generation_success`, `rounds_to_green`, `oracle_test_pass_rate`
- `cost_usd`, `cost_per_success`
- `oracle_pass_per_dollar`
- Core comparison block: `budget_A1` vs `smart_A0`

## Commands

### CI / smoke (no API keys)

```bash
python benchmarks/model_efficiency/pipelines/run_model_efficiency.py \
  --harness-only \
  --tasks email_validator \
  --runs 1 \
  --json
```

Or:

```bash
bash benchmarks/model_efficiency/scripts/run_eval.sh
```

### Paid experiment (PDD Cloud only)

Requires PDD Cloud auth/credits (`pdd setup`). No local `GEMINI_API_KEY` needed for the default manifest.

```bash
python benchmarks/model_efficiency/pipelines/run_model_efficiency.py \
  --allow-llm \
  --output-dir benchmarks/model_efficiency/experiments/$(date +%Y%m%d) \
  --max-cost-usd 50
```

## Outputs

```
experiments/<run>/
  run_manifest.json
  summary.json          # headline + core_comparison
  email_validator/
    A1.prompt             # pdd generate (or replay)
    a1_provenance.json
    run_0/smart_A0/ ...
    result.json
```

## Related

| Doc | Contents |
|-----|----------|
| [BUSINESS_VALUE.md](BUSINESS_VALUE.md) | Hypothesis, KPIs, honest claims |
| [EVALUATION.md](EVALUATION.md) | Commands, outputs, troubleshooting |
| [../formalization/README.md](../formalization/README.md) | Experiment 1 (M1–M3) |
| [../formalization/WORKFLOW.md](../formalization/WORKFLOW.md) | Product PR → command mapping |
| [../PR.md](../PR.md) | Pull request description |
