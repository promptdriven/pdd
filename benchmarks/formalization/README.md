# A0→A1 Prompt Formalization Benchmark

Benchmark for [issue #1273](https://github.com/promptdriven/pdd/issues/1273) — [PR #1280](https://github.com/promptdriven/pdd/pull/1280).

**Start here:** [A0_VS_A1.md](A0_VS_A1.md) — what we compare, metrics, and how to run.  
**Design:** [EXPERIMENT_DESIGN.md](EXPERIMENT_DESIGN.md) — M1/M2/M3 phases.

## Primary question (A0 vs A1)

Does **A1** (PDD formalized prompt: vocabulary, contracts, coverage, acceptance tests) produce more **reviewable** and **implementation-ready** artifacts than **A0** (ad-hoc prose) on the **same** task?

```text
Same requirement → A0.prompt (handwritten)  vs  A1.prompt (formalized)
                         ↓                           ↓
                  checkup lint / contract / coverage (deterministic)
                         ↓                           ↓
                  a0_vs_a1 scores in result.json
```

**A2** (reference code pytest) exists only for legacy schema compatibility in `run_benchmark.py` — not the headline comparison.

## Three phases → three milestones

```
┌─────────────────────────────────────────────────────────────┐
│ 1. PROMPT QUALITY (M1) — A0 vs A1 before generate spend      │
│    lint → contract check → coverage (+ stories #820)         │
└───────────────────────────┬─────────────────────────────────┘
                            ▼
┌─────────────────────────────────────────────────────────────┐
│ 2. GENERATE + RECORD (M2) — same A0/A1 arms, add economics  │
│    pdd generate / test / sync --evidence                     │
└───────────────────────────┬─────────────────────────────────┘
                            ▼
┌─────────────────────────────────────────────────────────────┐
│ 3. SHIP + STABILITY (M3) — drift on M2 artifacts            │
│    checkup gate → checkup drift                             │
└─────────────────────────────────────────────────────────────┘
```

| Milestone | Status | Primary script |
|-----------|--------|----------------|
| **M1** — A0 vs A1 checkability | Implemented | `pipelines/run_experiment.py` |
| **M2** — Generation economics | Implemented | `pipelines/run_generation_benchmark.py` |
| **M3** — Regeneration drift | Implemented | `pipelines/run_m3_pipeline.py` |

---

## Quick start

```bash
# PR smoke — A0 vs A1 tests + M1/M2/M3 replay (no API keys)
bash benchmarks/formalization/scripts/touchpoint_pr1280.sh

# M1 A0 vs A1 only (deterministic formalize, one task)
python benchmarks/formalization/pipelines/run_experiment.py \
  --output-dir /tmp/m1_smoke --tasks hello_fn --dry-run
jq '.a0_vs_a1' /tmp/m1_smoke/hello_fn/result.json

# Static harness — curated adhoc vs formalized prompts (A0 + A1 arms)
python benchmarks/formalization/run_benchmark.py --tasks email_validator --arms A0 A1 --report

# Live M2 + M3 (requires pdd setup + API keys)
bash benchmarks/formalization/scripts/run_live_m3.sh
```

```bash
pytest -vv tests/test_formalization_benchmark.py tests/test_formalization_pipeline.py
```

---

## Documentation map

| Doc | Audience |
|-----|----------|
| [A0_VS_A1.md](A0_VS_A1.md) | **PR reviewers** — arms, metrics, runnable proof |
| [EXPERIMENT_DESIGN.md](EXPERIMENT_DESIGN.md) | Design — phases, diagrams |
| [EVALUATION.md](EVALUATION.md) | Runbook — flags and outputs |
| [BUSINESS_VALUE.md](BUSINESS_VALUE.md) | M2+ economics |
| [pipelines/README.md](pipelines/README.md) | Script index |
| [corpus/README.md](corpus/README.md) | Task registry |

---

## Arms

| Arm | Corpus path | Role |
|-----|-------------|------|
| **A0** | `corpus/tasks/*/A0.prompt` | Ad-hoc baseline (realistic dev prose) |
| **A1** | `experiments/<run>/<task>/A1.prompt` | PDD formalized SoT |
| **A2** | (optional) reference tests only | Compatibility only |

---

## v0.3 static harness (`tasks/`)

Hand-curated `adhoc.prompt` / `formalized.prompt` under `tasks/email_validator`, etc.:

```bash
python benchmarks/formalization/run_benchmark.py --tasks email_validator --arms A0 A1 --report
```

Complements the **corpus M1** experiment; see [tasks/README.md](tasks/README.md).
