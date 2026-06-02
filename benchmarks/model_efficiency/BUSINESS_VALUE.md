# Business value — Experiment 2 (model efficiency, M4)

**Core question:** Can PDD formalization reduce **cost-to-correct-code** by making budget cloud
models more reliable?

**Prerequisite:** Understand Experiment 1 (M1–M3) in
[../formalization/BUSINESS_VALUE.md](../formalization/BUSINESS_VALUE.md).

---

## Problem statement

Without formalization, teams often compensate for vague prompts with **premium models and retries**:

```text
vague prompt → Opus-class model → failure → retry → fix → retry  ($$$)
```

PDD formalization shifts intelligence into the **spec layer**:

```text
formalized prompt → budget cloud tier → fewer retries → lower total cost
```

Experiment 2 measures whether that shift is real on a fixed task corpus.

---

## Hypothesis matrix

| Prompt | Model tier | Expected |
|--------|------------|----------|
| A0 vague | Smart (cloud strength 1.0) | Good but costly |
| A1 formalized | Smart | Best quality, highest cost |
| A0 vague | Budget (cloud strength 0.0) | Weak / unstable |
| A1 formalized | Budget | Better quality, **lower cost-per-success** |

### Primary comparison

```text
budget model + A1   vs   smart model + A0
```

If budget+A1 approaches smart+A0 on oracle pass rate at **lower cost**, that is the product
story for model efficiency.

---

## Honest claims

### Say this

✅ “Formalized prompts **narrow the quality gap** between budget and smart cloud tiers.”

✅ “A1 on a budget tier can reduce **cost-per-success** vs A0 on a smart tier.”

✅ “PDD shifts some intelligence from the model into the prompt/spec layer.”

### Do not say this

❌ “Formalized prompts make cheap models **as good as** expensive models.” (Too strong.)

❌ “One smoke task proves production savings.” (Need full 36-cell run + variance.)

---

## Metrics

Per cell (tier × arm × run) and aggregated:

| Metric | Business meaning |
|--------|------------------|
| `generation_success` | Did we reach passing tests? |
| `rounds_to_green` | Generate/fix rounds before pass |
| `oracle_test_pass_rate` | Independent requirement satisfaction |
| `cost_usd` | PDD Cloud spend for the cell |
| `cost_per_success` | `total_cost / successful_tasks` |
| `oracle_pass_per_dollar` | Quality per dollar |
| `resolved_model` | Actual cloud model name (verify tier routing) |

### Core comparison block

`run_manifest.json` → `core_comparison.budget_A1_minus_smart_A0`:

- `delta_success_rate`
- `delta_cost_per_success`
- `delta_mean_oracle_pass_rate`
- `delta_mean_rounds_to_green`

Headline example (harness smoke):

```text
M4: budget+A1 oracle 100% vs smart+A0 67% (+33.3 pp)
```

Harness replays fixtures — **paid runs** are required for cost and model-name evidence.

---

## Experimental design (default)

From [`manifest.yaml`](manifest.yaml):

| Dimension | Value |
|-----------|-------|
| Model tiers | smart (strength 1.0), budget (strength 0.0) |
| Routing | **Both PDD Cloud** (`PDD_CLOUD_ONLY=1`) |
| Prompt arms | A0, A1 |
| Tasks | `email_validator`, `token_bucket`, `refund_handler` |
| Runs per cell | 3 |
| Total generations | 2 × 2 × 3 × 3 = **36** |

A1 is formalized **once per task** on the smart tier before the matrix.

---

## Artifact policy

Same as Experiment 1:

| Artifact | Source |
|----------|--------|
| A0 | Handcrafted corpus |
| A1 | PDD Cloud `cloud_formalize` (or CI replay) |
| Code + tests | `pdd generate` + `pdd test` (+ optional `pdd fix`) |
| Oracle | Hand-written tier gold tests |

---

## When to run M4

| Stage | Run |
|-------|-----|
| Early / CI | `--harness-only` smoke (shape only) |
| After M1–M3 stable | Paid `--allow-llm` 36-cell run |
| Executive readout | `summary.json` headline + `core_comparison` |

---

## Suggested executive one-liner

> PDD formalization lets teams use **budget cloud models** more effectively — improving
> cost-per-success versus relying on **premium models with vague prompts**.

---

## Related

- [README.md](README.md) — commands and outputs
- [../formalization/BUSINESS_VALUE.md](../formalization/BUSINESS_VALUE.md) — M1–M3
- [../PR.md](../PR.md) — pull request summary
