# Step-by-step evaluation guide

| Path | Section | LLM? | What it proves |
|------|---------|------|----------------|
| **M1** — Prompt checkability | §2–§4 | No (default) | A0→A1 improves lint/contract structure |
| **v0.3 static harness** | §5 | No | Hand-curated fixtures + epic #833 scorecard |

**Time:** ~2 minutes for M1 deterministic run.

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

## 5. v0.3 static harness

```bash
bash benchmarks/formalization/scripts/run_eval.sh
```

---

## What M1 does NOT prove

- Generated code correctness → **M2** (+ oracle tests)
- Same behavior each generation → **M3** (regen + drift)
