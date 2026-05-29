# Step-by-step evaluation guide

| Path | Section | LLM? | What it proves |
|------|---------|------|----------------|
| **M1** — Prompt checkability | §2–§4 | No (default) | A0→A1 improves lint/contract structure |
| **M2** — Generation economics | §6 | Harness-only in CI; `--allow-llm` for real runs | Oracle (tier_gold) vs non-oracle (pdd test) pass rates |
| **M3** — Regen drift | §7 | `--dry-run` in CI; `--allow-llm` for regen | `pdd checkup drift` stability on gold tasks |
| **Story template (#820)** | §6–§7 | Deterministic seed in M1 | `## Oracle` / `## Non-Oracle` blocks in stories |
| **v0.3 static harness** | §8 | No | Hand-curated fixtures + epic #833 scorecard |

**Time:** ~3 minutes for M1+M2+M3 CI smoke (`scripts/run_eval.sh`).

---

## 0. Prerequisites

```bash
cd /path/to/pdd
pip install -e ".[dev]"
```

---

## 1. Smoke tests

```bash
pytest -vv tests/test_formalization_benchmark.py tests/test_formalization_pipeline.py
```

---

## 2. Milestone 1 — run experiment (deterministic)

```bash
python benchmarks/formalization/pipelines/run_experiment.py
```

Outputs under `benchmarks/formalization/experiments/latest/` (gitignored).

```bash
jq -r '.headline' benchmarks/formalization/experiments/latest/summary.json
```

---

## 3. Optional LLM experiment

```bash
python benchmarks/formalization/pipelines/run_experiment.py \
  --allow-llm --max-cost-usd 25 \
  --output-dir benchmarks/formalization/experiments/llm_run
```

---

## 4. Single-task formalize

```bash
python benchmarks/formalization/pipelines/formalize_a1.py \
  --input  benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --output /tmp/email_A1.prompt --json
```

---

## 6. Milestone 2 — generation economics (oracle vs non-oracle)

Each M2 arm reports two evaluation modes:

| Mode | Source | What it measures |
|------|--------|------------------|
| **oracle** | `corpus/tier_gold/*/oracle_tests/` | Independent hand-written pytest (ground truth) |
| **non_oracle** | `pdd test` output | Self-consistency tests generated from the same prompt |

```bash
# CI-safe harness (copies tier_gold baseline, runs oracle pytest)
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --harness-only --skip-formalize \
  --m1-dir benchmarks/formalization/experiments/latest \
  --output-dir benchmarks/formalization/experiments/m2_latest \
  --tasks email_validator,token_bucket,refund_handler
```

Paid run (requires API keys):

```bash
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --allow-llm --max-rounds 3 --max-cost-usd 50
```

---

## 7. Milestone 3 — drift

```bash
python benchmarks/formalization/pipelines/run_drift_benchmark.py \
  --dry-run \
  --m2-dir benchmarks/formalization/experiments/m2_latest \
  --tasks email_validator
```

Regeneration (paid):

```bash
python benchmarks/formalization/pipelines/run_drift_benchmark.py \
  --allow-llm --runs 3 --max-cost-usd 20
```

---

## 8. v0.3 static harness

```bash
bash benchmarks/formalization/scripts/run_eval.sh
```

---

## What M1 does NOT prove

- Generated code correctness → **M2** (+ oracle tests)
- Same behavior each generation → **M3** (regen + drift)
