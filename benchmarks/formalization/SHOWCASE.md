# Showcase guide — running the formalization experiment for an audience

Use this guide when you need to **demonstrate** the A0→A1 benchmark live (stand-up, PR review,
investor demo, or issue #1273 walkthrough). For day-to-day development, see
[EVALUATION.md](EVALUATION.md).

---

## What you are showing

The benchmark compares two prompt arms on the same task:

| Arm | Name | Typical content |
|-----|------|-----------------|
| **A0** | Ad-hoc | Handwritten requirements prose |
| **A1** | Formalized | A0 plus checkup-driven `<vocabulary>`, `<contract_rules>`, `<coverage>` |

Three milestones map to **three product phases** (see [EXPERIMENT_DESIGN.md](EXPERIMENT_DESIGN.md)):

```
Phase 1 (M1)  →  Phase 2 (M2)  →  Phase 3 (M3)
prompt quality    generate+record    drift stability
```

1. **M1 — Checkability:** Formalization makes the prompt easier to lint, cover, and audit
   *before* any code is generated.
2. **M2 — Generation economics:** **`pdd generate` on A0 and A1**; scored with **oracle**
   (independent gold tests) and **non-oracle** (`pdd test`).
3. **M3 — Drift:** `pdd checkup drift` on M2 code for regen stability.

**Honest scope:** M1 alone does not prove lower token cost. Say that out loud, then show M2/M3
when you want dollars and stability.

---

## Choose your demo length

| Duration | Script | API keys? |
|----------|--------|-----------|
| **~3 min** | [Quick demo (CI-safe)](#quick-demo-3-minutes-no-api-keys) | No |
| **~10 min** | [Single-task deep dive](#single-task-deep-dive-email_validator) | No |
| **~30 min** | [Full pipeline + optional LLM](#full-experiment-with-llm-paid) | Yes (M2/M3 regen) |

---

## Prerequisites (once per machine)

```bash
cd /path/to/pdd
conda activate pdd          # or your venv
pip install -e ".[dev]"
```

Optional but helpful for live JSON snippets:

```bash
brew install jq    # macOS
```

---

## Quick demo (~3 minutes, no API keys)

This is the recommended live demo. It runs the same path as CI.

```bash
bash benchmarks/formalization/scripts/run_eval.sh
```

### What happens (narrate while it runs)

| Step | Command (inside script) | What to say |
|------|-------------------------|-------------|
| 1 | pytest smoke tests | “We verify the harness before any experiment output.” |
| 2 | M1 `run_experiment.py` (deterministic) | “Handcrafted A0 → formalized A1; we measure lint, rules, and coverage **before** generate spend.” |
| 3 | M2 `--replay-fixtures` | “We replay recorded `pdd generate`/`pdd test` outputs and score **oracle** gold tests.” |
| 4 | M3 `run_m3_pipeline --replay-fixtures` | “Drift checks stability of M2 code against the prompt.” |
| 5 | v0.3 static harness | “Legacy scorecard maps results to epic #833 issues.” |

### What to open when it finishes

```bash
# M1 human report
cat benchmarks/formalization/experiments/ci_smoke/REPORT.md

# M1 one-line headline per task
jq -r '.headline' benchmarks/formalization/experiments/ci_smoke/summary.json

# M2 oracle vs non-oracle (email_validator example)
jq '.tasks[0].evaluation_summary' \
  benchmarks/formalization/experiments/ci_m2_smoke/run_manifest.json

# M3 drift status
jq '.tasks[0].arms.A1.drift.status' \
  benchmarks/formalization/experiments/ci_m3_smoke/run_manifest.json
```

**Closing line for a 3-minute demo:**

> “Formalization improved prompt checkability on N tasks; on gold tasks we can already
> compare oracle pass rates between A0 and A1 arms. Paid runs add real generation cost and
> regen drift numbers.”

---

## Single-task deep dive (`email_validator`)

Use one task when someone asks “show me the actual diff.”

### 1. Show the corpus (A0 only is versioned)

```bash
cat benchmarks/formalization/corpus/tasks/email_validator/A0.prompt
ls benchmarks/formalization/corpus/tier_gold/email_validator/oracle_tests/
cat benchmarks/formalization/corpus/tasks/email_validator/stories/story__email_validation.md
```

Point out the story’s **`## Oracle`** (what must matter for pass/fail) and **`## Non-Oracle`**
(what must not).

### 2. Formalize one prompt (PDD Cloud path)

Default product path — [`cloud_formalize.py`](pipelines/cloud_formalize.py):

```bash
python benchmarks/formalization/pipelines/cloud_formalize.py \
  --input  benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --output /tmp/email_A1.prompt \
  --stories-dir benchmarks/formalization/corpus/tasks/email_validator/stories \
  --json
```

Dev fallback (local checkup write-back, no cloud):

```bash
python benchmarks/formalization/pipelines/checkup_formalize.py \
  --input  benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --output /tmp/email_A1.prompt \
  --stories-dir benchmarks/formalization/corpus/tasks/email_validator/stories \
  --json
```

You can also run the underlying checkup commands directly (read-only) for narration:

```bash
pdd checkup lint benchmarks/formalization/corpus/tasks/email_validator/A0.prompt --json
pdd checkup contract check /tmp/email_A1.prompt --json
pdd checkup coverage /tmp/email_A1.prompt \
  --stories-dir benchmarks/formalization/corpus/tasks/email_validator/stories --json
```

Open `/tmp/email_A1.prompt` side-by-side with A0. Highlight new `<vocabulary>`,
`<contract_rules>`, and `<coverage>` sections. The manifest JSON reports
`summary.checkup_pass`.

### 3. Run M1 for that task only

```bash
python benchmarks/formalization/pipelines/run_experiment.py \
  --tasks email_validator \
  --output-dir benchmarks/formalization/experiments/demo_m1
```

```bash
jq '.tasks[0].delta' benchmarks/formalization/experiments/demo_m1/email_validator/result.json
jq '.tasks[0].story_template.delta' \
  benchmarks/formalization/experiments/demo_m1/run_manifest.json
```

### 4. Run M2 harness (oracle score)

```bash
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --replay-fixtures --skip-formalize \
  --m1-dir benchmarks/formalization/experiments/demo_m1 \
  --output-dir benchmarks/formalization/experiments/demo_m2 \
  --tasks email_validator --json
```

Explain the two evaluation modes in the output:

| Mode | Field | Meaning |
|------|-------|---------|
| **Oracle** | `evaluation_modes.oracle` | Hand-written tests under `corpus/tier_gold/` — ground truth |
| **Non-oracle** | `evaluation_modes.non_oracle` | Tests that would come from `pdd test` on the same prompt — self-consistency |

In replay mode, non-oracle may be empty if fixture tests are missing; **oracle still runs**
against the tier_gold baseline copied into the work dir.

### 5. Run M3 drift (dry-run)

```bash
python benchmarks/formalization/pipelines/run_drift_benchmark.py \
  --dry-run \
  --m2-dir benchmarks/formalization/experiments/demo_m2 \
  --m1-dir benchmarks/formalization/experiments/demo_m1 \
  --output-dir benchmarks/formalization/experiments/demo_m3 \
  --tasks email_validator --json
```

---

## Full experiment with LLM (paid)

Use when you need real generation economics, not just structure.

```bash
# M1 with optional LLM formalization stages
python benchmarks/formalization/pipelines/run_experiment.py \
  --allow-llm --max-cost-usd 25 \
  --output-dir benchmarks/formalization/experiments/llm_m1

# M2 real generate / test / fix loops
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --allow-llm --max-rounds 3 --max-cost-usd 50 \
  --m1-dir benchmarks/formalization/experiments/llm_m1 \
  --output-dir benchmarks/formalization/experiments/llm_m2 \
  --tasks email_validator,token_bucket,refund_handler

# M3 regen drift (multi-run)
python benchmarks/formalization/pipelines/run_drift_benchmark.py \
  --allow-llm --runs 3 --max-cost-usd 20 \
  --m2-dir benchmarks/formalization/experiments/llm_m2 \
  --m1-dir benchmarks/formalization/experiments/llm_m1 \
  --output-dir benchmarks/formalization/experiments/llm_m3
```

Report template (fill from `run_manifest.json`):

> Formalized prompts (A1) required **{delta_rounds}** fewer generate/fix rounds than ad-hoc
> (A0) on **{n}** gold tasks, with oracle pass rate **{a1_oracle}%** vs **{a0_oracle}%**
> at **${delta_cost}** total generation cost.

---

## Suggested talking script (5 minutes)

1. **Problem (30 s):** Vague prompts waste generation budget because the model guesses intent.
2. **Setup (30 s):** Five corpus tasks; three gold tasks with independent oracle tests and
   #820 stories (`Oracle` / `Non-Oracle` blocks).
3. **M1 live (1 min):** Run `run_experiment.py --tasks email_validator`; show A0→A1 delta
   in lint and contract rules.
4. **Oracle vs non-oracle (1 min):** Oracle = “did we meet real requirements?” Non-oracle =
   “does the code pass tests we generated from the same prompt?” Both appear in M2 output.
5. **M2/M3 smoke (1 min):** Run `run_eval.sh` tail or pre-baked `experiments/ci_*` artifacts.
6. **Close (30 s):** M1 is the cheap gate; M2/M3 connect to dollars and trust. **Experiment 2 (M4)** adds the model-tier cost story — see [../model_efficiency/README.md](../model_efficiency/README.md).

---

## Experiment 2 teaser (M4, optional add-on)

If the audience asks about **cost vs model tier**:

```bash
bash benchmarks/model_efficiency/scripts/run_eval.sh
jq -r '.headline' benchmarks/model_efficiency/experiments/ci_smoke/summary.json
```

Say: “Formalization can narrow the gap between budget and smart **PDD Cloud** models — we
compare **budget+A1** vs **smart+A0**, not claim cheap beats expensive outright.”

See [../model_efficiency/BUSINESS_VALUE.md](../model_efficiency/BUSINESS_VALUE.md).

---

## Artifact map (where outputs live)

All experiment outputs are gitignored under `benchmarks/formalization/experiments/`.

| Path | Contents |
|------|----------|
| `experiments/<run>/run_manifest.json` | Full run metadata + per-task results |
| `experiments/<run>/summary.json` | M1 aggregates + headline |
| `experiments/<run>/REPORT.md` | M1 narrative report |
| `experiments/<run>/<task>/A1.prompt` | Formalized prompt for that task |
| `experiments/<run>/<task>/commands.jsonl` | Command audit log |
| `experiments/m2_*/<task>/A0\|A1/` | Per-arm code, tests, economics |
| `experiments/m3_*/<task>/result.json` | Drift report per arm |

---

## Troubleshooting

| Symptom | Fix |
|---------|-----|
| `fatal: branch already checked out at …/pdd-manual-821` | Use one checkout only; remove stale worktree: `git worktree list` |
| M2 non-oracle pass rate is `null` in harness mode | Expected — no `pdd test` run; oracle still validates gold baseline |
| M3 hangs when calling `pdd` subprocess | Use `run_drift_benchmark.py` (in-process drift); avoid raw CLI in scripts |
| `jq` not found | Install jq or read `run_manifest.json` in an editor |

---

## Related docs

| Doc | Use when |
|-----|----------|
| [README.md](README.md) | Repo entry point and links |
| [EVALUATION.md](EVALUATION.md) | Step-by-step technical reference |
| [BUSINESS_VALUE.md](BUSINESS_VALUE.md) | Hypothesis and stakeholder framing |
| [PLAN.md](PLAN.md) | Architecture and milestone scope |
| [EPIC833.md](EPIC833.md) | Mapping to epic sub-issues |
| [../PR.md](../PR.md) | Pull request description |
| [../model_efficiency/README.md](../model_efficiency/README.md) | Experiment 2 (M4) |
