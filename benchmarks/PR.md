# Pull request — PDD formalization & model efficiency benchmarks

Use this document as the **PR description** when opening the benchmark branch.

---

## Title (suggested)

```text
feat(benchmarks): A0→A1 formalization (M1–M3) and model efficiency (M4) experiments
```

---

## Summary

Adds two related benchmarks under `benchmarks/` that measure PDD formalization value for
[issue #1273](https://github.com/promptdriven/pdd/issues/1273) / epic
[#833](https://github.com/promptdriven/pdd/issues/833):

**Design doc:** [formalization/EXPERIMENT_DESIGN.md](formalization/EXPERIMENT_DESIGN.md)

### Experiment 1 — `benchmarks/formalization/` (M1–M3)

Three product phases: **prompt quality → generate + record → ship + stability**.

Compares **handcrafted A0** vs **formalized A1** on a versioned corpus:

| Milestone | Question |
|-----------|----------|
| **M1** | Does formalization improve prompt checkability (lint, contract, coverage, stories)? |
| **M2** | Does A1 reduce generate/fix rounds and improve oracle pass rate vs A0? |
| **M3** | Is A1 at least as stable as A0 under `pdd checkup drift` regen? |

**Artifact policy:** Only A0 and oracle tests are hand-written. A1 prompts, generated code,
and generated tests come from **PDD Cloud** (`pdd generate`, `pdd test`) or committed replay
fixtures under `corpus/tier_gold/*/pdd_generated/`.

### Experiment 2 — `benchmarks/model_efficiency/` (M4)

Separate follow-on experiment:

> Can formalization reduce **cost-to-correct-code** by making **budget cloud models** more
> reliable?

Compares **smart (strength 1.0)** vs **budget (strength 0.0)** on PDD Cloud, crossed with
A0 vs A1. Primary business comparison: **budget + A1** vs **smart + A0**.

---

## Why two experiments?

| Experiment | Audience question |
|------------|-------------------|
| M1–M3 | “Does formalization improve prompts and generation outcomes?” |
| M4 | “Can formalization reduce dependence on premium models / lower cost-per-success?” |

M4 is intentionally **later** — run M1–M3 first; M4 adds the cost-saving narrative without
overloading the core checkability benchmark.

---

## Key files

```
benchmarks/
├── README.md                           # Overview of both experiments
├── PR.md                               # This file
├── formalization/
│   ├── README.md, BUSINESS_VALUE.md, EVALUATION.md, PLAN.md
│   ├── WORKFLOW.md, SHOWCASE.md, EPIC833.md
│   ├── corpus/                         # A0 + manifest + tier_gold
│   ├── pipelines/                      # M1–M3 runners
│   └── scripts/run_eval.sh             # CI smoke
└── model_efficiency/
    ├── README.md, BUSINESS_VALUE.md
    ├── manifest.yaml
    ├── pipelines/run_model_efficiency.py
    └── scripts/run_eval.sh
```

---

## Business value (short)

**Experiment 1**

- M1: Audit prompts **before** generation spend
- M2: Fewer rounds / lower cost to passing **oracle** tests
- M3: More trustworthy regen behavior

**Experiment 2**

- Formalization **narrows the gap** between budget and smart cloud tiers (not “cheap beats expensive”)
- KPIs: `cost_per_success`, `rounds_to_green`, `oracle_pass_per_dollar`

Full framing: [formalization/BUSINESS_VALUE.md](formalization/BUSINESS_VALUE.md),
[model_efficiency/BUSINESS_VALUE.md](model_efficiency/BUSINESS_VALUE.md).

---

## Test plan

- [ ] `pytest -vv tests/test_formalization_benchmark.py tests/test_formalization_pipeline.py`
- [ ] `pytest -vv tests/test_model_efficiency_benchmark.py`
- [ ] `bash benchmarks/formalization/scripts/run_eval.sh` (M1 replay → M2 harness → M3 dry-run)
- [ ] `bash benchmarks/model_efficiency/scripts/run_eval.sh` (M4 harness smoke)
- [ ] Optional paid smoke: M1 `--allow-llm` on one task; M2/M3 via `run_live_m3.sh`
- [ ] Optional paid M4: one task × 1 run; verify `economics.resolved_model` for both tiers

---

## CI vs paid runs

| Script | API keys | What it proves |
|--------|----------|----------------|
| `formalization/scripts/run_eval.sh` | No | Harness wiring + oracle pytest on replay fixtures |
| `model_efficiency/scripts/run_eval.sh` | No | M4 matrix shape + fixture replay |
| `--allow-llm` pipelines | Yes (PDD Cloud) | Real economics, drift regen, model tiers |

---

## Honest scope notes

- M1 alone does **not** prove token savings — cite M2 for dollars.
- M4 smoke uses **recorded fixtures** — cost and model-tier claims need a paid run.
- `pdd checkup gate` is documented in [WORKFLOW.md](formalization/WORKFLOW.md) but not wired into CI yet.
- v0.3 static harness (`formalization/tasks/`) remains for epic scorecard; **not** the source of A1/code/test claims.

---

## Related issues / PRs

| Item | Link |
|------|------|
| Benchmark issue | [#1273](https://github.com/promptdriven/pdd/issues/1273) |
| Epic | [#833](https://github.com/promptdriven/pdd/issues/833) |
| Checkup lint | [#1154](https://github.com/promptdriven/pdd/pull/1154) |
| Contract | [#1155](https://github.com/promptdriven/pdd/pull/1155) |
| Coverage | [#1157](https://github.com/promptdriven/pdd/pull/1157) |
| Stories | [#1271](https://github.com/promptdriven/pdd/pull/1271) / #820 |
| Evidence | [#1256](https://github.com/promptdriven/pdd/pull/1256) |
| Gate | [#1260](https://github.com/promptdriven/pdd/pull/1260) |
| Drift | [#1261](https://github.com/promptdriven/pdd/pull/1261) |
| Simplify | [#1255](https://github.com/promptdriven/pdd/pull/1255) |

---

## Reviewer guide

1. Read [benchmarks/README.md](README.md) (5 min) — two experiments + artifact policy
2. Skim [formalization/BUSINESS_VALUE.md](formalization/BUSINESS_VALUE.md) — what we claim
3. Run `bash benchmarks/formalization/scripts/run_eval.sh` — CI path
4. Optional: [formalization/SHOWCASE.md](formalization/SHOWCASE.md) for demo narrative
