# Formalization Checkability Benchmark — feasibility plan (M1)

**Official name (M1):** A0→A1 Prompt Formalization Benchmark  
**M2:** Formalized Prompt Generation Benchmark  
**M3:** Formalized Prompt Regeneration Stability Benchmark  

Branch: **`feat/issue-1273-formalization-benchmark`** (DianaTao fork)  
Issue: [#1273](https://github.com/promptdriven/pdd/issues/1273) · Epic [#833](https://github.com/promptdriven/pdd/issues/833)

---

## Milestone claims

| Milestone | Proves |
|-----------|--------|
| **M1** | Formalization improves **prompt checkability** |
| **M2** | Better prompts produce **better generated code** (oracle tests) |
| **M3** | Better prompts produce **more stable regeneration** (drift) |

M1 does **not** claim code correctness or same-behavior-each-generation.

See **[BUSINESS_VALUE.md](BUSINESS_VALUE.md)** for the full business case and hypothesis.

---

## Business value

This benchmark makes PDD's business value measurable: better prompts should reduce wasted
generation loops, lower token spend, and make AI-generated software easier to trust.

**Core hypothesis:**

> A structured A1 prompt should need fewer PDD generate / fix / verify rounds than a vague
> A0 prompt to reach acceptable behavior.

| Milestone | Business lever |
|-----------|----------------|
| **M1** | Prompt checkability before generation (lint, vocabulary, contract rules, audit log) |
| **M2** | Generation economics: rounds, tokens, cost, wall-clock, oracle vs generated pass rate |
| **M3** | Regeneration drift and behavioral stability vs oracle |

Pipeline placeholders for M2/M3 live in `pipelines/economics.py` and are emitted as
`null` in M1 `result.json` until `run_generation_benchmark.py` (M2) lands.

---

## Quick start

```bash
python benchmarks/formalization/pipelines/run_experiment.py
pytest -vv tests/test_formalization_pipeline.py
```

See [EVALUATION.md](EVALUATION.md) for full workflow.

---

## Architecture

- **`corpus/`** — versioned handwritten A0 prompts only
- **`pipelines/`** — benchmark-local `formalize_a1.py` (`formalize_script_v1`)
- **`experiments/`** — gitignored run outputs
- **`tasks/`** — v0.3 static harness (unchanged for CI smoke)

Formalization is **not** native `pdd checkup formalize --apply` yet; the script is
pinned, hashed, and logged to collect evidence before productizing.

---

## Implementation checklist (M1)

- [x] `corpus/manifest.yaml` + 5 × `A0.prompt`
- [x] `pipelines/writeback.py`, `formalize_a1.py`, `run_experiment.py`
- [x] `pipelines/templates/formalize_a1.prompt`
- [x] `experiments/.gitignore`
- [x] `schemas/experiment.schema.json`
- [x] `tests/test_formalization_pipeline.py`
- [x] Updated `EVALUATION.md`, `README.md`, `run_eval.sh`

---

## CI vs experiment

| Mode | LLM | Network | `pdd generate` |
|------|-----|---------|----------------|
| CI | No | No | No |
| Experiment | `--allow-llm` only | Yes if LLM | M2+ |

---

## Gate / drift merge (M2/M3)

Cherry-pick from `feat/issue-825-gate` and `feat/issue-831-drift` — do **not**
full-merge into M1 (conflicts with benchmark tests).
