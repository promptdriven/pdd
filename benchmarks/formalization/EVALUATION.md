# Step-by-step evaluation guide

**Design (phases, diagrams, rationale):** [EXPERIMENT_DESIGN.md](EXPERIMENT_DESIGN.md)

```
Phase 1 (M1)  →  Phase 2 (M2)  →  Phase 3 (M3)
prompt quality    generate+record    drift stability
```

| Phase | Milestone | LLM? | What it proves |
|-------|-----------|------|----------------|
| **1 — Prompt quality** | M1 | No (default) | A0→A1 improves lint/contract/coverage |
| **2 — Generate + record** | M2 | `--replay-fixtures` in CI; `--allow-llm` live | Oracle vs non-oracle pass rates; economics |
| **3 — Ship + stability** | M3 | `--dry-run` / `--replay-fixtures` in CI; `--allow-llm` live | `pdd checkup drift` on M2 code |
| Story template (#820) | M1 | Seeded in M1 | `## Oracle` / `## Non-Oracle` in stories |
| v0.3 static harness | — | No | Legacy epic #833 scorecard |

**Time:** ~3 minutes for full CI smoke (`scripts/run_eval.sh`).

---

## 0. Prerequisites

```bash
cd /path/to/pdd
pip install -e ".[dev]"
pdd setup   # only for --allow-llm live runs
```

---

## 1. Smoke tests

```bash
pytest -vv tests/test_formalization_benchmark.py tests/test_formalization_pipeline.py
```

---

## Phase 1 — M1 prompt checkability

### 2. Batch experiment (deterministic)

```bash
python benchmarks/formalization/pipelines/run_experiment.py \
  --output-dir benchmarks/formalization/experiments/ci_smoke
```

Outputs: `REPORT.md`, `EVALUATION_RESULT.md`, `summary.json`, per-task `A1.prompt`.

### 3. Optional LLM formalization

```bash
python benchmarks/formalization/pipelines/run_experiment.py \
  --allow-llm --max-cost-usd 25 \
  --output-dir benchmarks/formalization/experiments/latest
```

### 4. Single-task paths

```bash
# Benchmark formalizer
python benchmarks/formalization/pipelines/formalize_a1.py \
  --input benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --output /tmp/email_A1.prompt --json

# Product checkup loop (lint → contract → coverage writeback)
python benchmarks/formalization/pipelines/checkup_formalize.py \
  --input benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --output /tmp/email_A1.prompt \
  --stories-dir benchmarks/formalization/corpus/tasks/email_validator/stories
```

### Product read-only checks (no benchmark script)

```bash
pdd checkup lint     path/to/prompt.prompt [--stories dir] [--json]
pdd checkup contract check path/to/prompt.prompt [--stories dir] [--json]
pdd checkup coverage path/to/prompt.prompt [--stories-dir dir] [--json]
```

---

## Phase 2 — M2 generation economics

Each arm runs **`pdd generate` on A0 and A1**. M2 reports:

| Mode | Source | What it measures |
|------|--------|------------------|
| **oracle** | `corpus/tier_gold/*/oracle_tests/` | Independent hand-written pytest |
| **non_oracle** | `pdd test` output | Self-consistency from the same prompt |

### CI replay (no API keys)

```bash
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --replay-fixtures \
  --skip-formalize \
  --m1-dir benchmarks/formalization/experiments/ci_smoke \
  --output-dir benchmarks/formalization/experiments/ci_m2_smoke \
  --tasks email_validator,token_bucket,refund_handler
```

### Live run (API keys)

```bash
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --allow-llm \
  --max-rounds 3 \
  --max-cost-usd 50 \
  --m1-dir benchmarks/formalization/experiments/latest \
  --output-dir benchmarks/formalization/experiments/m2_live \
  --tasks email_validator,token_bucket,refund_handler
```

Optional: `--save-fixtures` persists outputs to `corpus/tier_gold/*/pdd_generated/`.

---

## Phase 3 — M3 drift (requires M2 code)

M3 reads code from `m2_dir/<task>/{A0,A1}/generated/src/` and runs `pdd checkup drift`.

### Combined M2 → M3

```bash
# CI-safe
python benchmarks/formalization/pipelines/run_m3_pipeline.py \
  --replay-fixtures \
  --m1-dir benchmarks/formalization/experiments/ci_smoke \
  --tasks email_validator

# Live
bash benchmarks/formalization/scripts/run_live_m3.sh
```

Or explicitly:

```bash
python benchmarks/formalization/pipelines/run_m3_pipeline.py \
  --allow-llm \
  --save-fixtures \
  --m1-dir benchmarks/formalization/experiments/latest \
  --m2-dir benchmarks/formalization/experiments/m2_live \
  --m3-dir benchmarks/formalization/experiments/m3_live \
  --tasks email_validator,token_bucket,refund_handler \
  --runs 2 \
  --max-cost-usd-m2 50 \
  --max-cost-usd-m3 20
```

Drift-only (existing M2):

```bash
python benchmarks/formalization/pipelines/run_drift_benchmark.py \
  --allow-llm --runs 3 \
  --m2-dir benchmarks/formalization/experiments/m2_live \
  --m1-dir benchmarks/formalization/experiments/latest
```

---

## Full CI smoke (all phases)

```bash
bash benchmarks/formalization/scripts/run_eval.sh
```

Opens: `experiments/ci_smoke/REPORT.md`, `experiments/ci_m3_smoke/PIPELINE_RESULT.md`

---

## What each phase does NOT prove alone

| Phase | Does not prove |
|-------|----------------|
| **M1** | Lower token cost; correct generated code |
| **M2 (harness replay)** | Live cloud economics (use `--allow-llm`) |
| **M3 (dry-run)** | Regen variance (use `--allow-llm --runs N`) |

See [BUSINESS_VALUE.md](BUSINESS_VALUE.md) for honest reporting templates.
