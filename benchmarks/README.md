# PDD benchmarks — formalization and model efficiency

Two related experiments under `benchmarks/` measure whether **PDD formalization** improves
prompt quality, generation economics, stability, and **model-tier efficiency**.

| Experiment | Folder | Core question | Milestones |
|------------|--------|---------------|------------|
| **A0→A1 formalization** | [`formalization/`](formalization/) | Does a formalized prompt perform better than a vague prompt? | M1 checkability · M2 economics · M3 drift |
| **Model efficiency** | [`model_efficiency/`](model_efficiency/) | Can formalization let cheaper cloud models approach expensive ones? | M4 smart vs budget × A0 vs A1 |

**Tracking:** [issue #1273](https://github.com/promptdriven/pdd/issues/1273) · epic [#833](https://github.com/promptdriven/pdd/issues/833)

---

## How the two experiments relate

See [formalization/EXPERIMENT_DESIGN.md](formalization/EXPERIMENT_DESIGN.md) for the full
three-phase diagram. Summary:

```
┌─────────────────────────────────────────────────────────────┐
│ 1. PROMPT QUALITY (M1)                                      │
└───────────────────────────┬─────────────────────────────────┘
                            ▼
┌─────────────────────────────────────────────────────────────┐
│ 2. GENERATE + RECORD (M2) — pdd generate on A0 and A1       │
└───────────────────────────┬─────────────────────────────────┘
                            ▼
┌─────────────────────────────────────────────────────────────┐
│ 3. SHIP + STABILITY (M3) — checkup drift on M2 code         │
└─────────────────────────────────────────────────────────────┘
         │
         └──► Experiment 2 (M4): model tier × arm matrix
```

Run **Experiment 1 (M1–M3)** first. Use **Experiment 2 (M4)** for the cost-saving story.

---

## Artifact policy (both experiments)

| Artifact | Source |
|----------|--------|
| **A0 prompt** | Handcrafted — only versioned prompt input |
| **A1 prompt** | PDD Cloud (`pdd checkup lint --llm` + `pdd generate`, or CI replay) |
| **Generated code** | PDD Cloud `pdd generate` (or recorded fixtures) |
| **Generated tests** | PDD Cloud `pdd test` (or recorded fixtures) |
| **Oracle tests** | Hand-written independent pytest (evaluation only) |

Do **not** use hand-curated baselines for published A1/code/test results. The v0.3 static
harness under `formalization/tasks/` is a legacy epic #833 scorecard — separate from these
experiments.

---

## Quick start (CI, no API keys)

```bash
# Experiment 1 — M1 → M2 → M3 smoke
bash benchmarks/formalization/scripts/run_eval.sh

# Experiment 2 — M4 harness smoke
bash benchmarks/model_efficiency/scripts/run_eval.sh
```

---

## Documentation map

### Experiment 1 — formalization (M1–M3)

| Doc | Audience | Contents |
|-----|----------|----------|
| [formalization/EXPERIMENT_DESIGN.md](formalization/EXPERIMENT_DESIGN.md) | Everyone | **Three phases, diagrams, command map** |
| [formalization/README.md](formalization/README.md) | Everyone | Entry point, quick start |
| [formalization/BUSINESS_VALUE.md](formalization/BUSINESS_VALUE.md) | PM / leadership | Hypothesis, metrics, honest claims |
| [formalization/EVALUATION.md](formalization/EVALUATION.md) | Engineers | Runbook, flags, outputs |
| [formalization/PLAN.md](formalization/PLAN.md) | Architects | Milestones, layout, status |
| [formalization/WORKFLOW.md](formalization/WORKFLOW.md) | Authors | PR phases → product commands |
| [formalization/SHOWCASE.md](formalization/SHOWCASE.md) | Demos | 3 / 10 / 30 minute scripts |
| [formalization/EPIC833.md](formalization/EPIC833.md) | Issue triage | Epic sub-issue mapping |
| [formalization/corpus/README.md](formalization/corpus/README.md) | Corpus editors | Task registry, scaling |
| [formalization/pipelines/README.md](formalization/pipelines/README.md) | Pipeline devs | Script index |

### Experiment 2 — model efficiency (M4)

| Doc | Audience | Contents |
|-----|----------|----------|
| [model_efficiency/README.md](model_efficiency/README.md) | Everyone | Design, cloud tiers, commands |
| [model_efficiency/BUSINESS_VALUE.md](model_efficiency/BUSINESS_VALUE.md) | PM / leadership | Cost-per-success story |

### Pull request

| Doc | Contents |
|-----|----------|
| [PR.md](PR.md) | Suggested PR title, summary, test plan for this branch |

---

## Business headlines (what to say)

**Experiment 1:** PDD formalization improves prompt **checkability** before generation spend
(M1), reduces **rounds and cost to acceptable code** when comparing A0 vs A1 (M2), and
improves **regeneration stability** vs oracle behavior (M3).

**Experiment 2:** Formalized prompts can improve **budget-model reliability** and reduce
**cost-per-success** — the key comparison is **budget + A1** vs **smart + A0**. We do **not**
claim cheap models beat expensive ones outright.

See [formalization/BUSINESS_VALUE.md](formalization/BUSINESS_VALUE.md) and
[model_efficiency/BUSINESS_VALUE.md](model_efficiency/BUSINESS_VALUE.md) for detail.
