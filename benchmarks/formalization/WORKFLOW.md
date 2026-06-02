# PDD checkup workflow — what the PRs enable

This document maps the **product commands** merged across
[#1154](https://github.com/promptdriven/pdd/pull/1154) … to the **formalization benchmark**.

**Canonical design (diagrams + command map):** [EXPERIMENT_DESIGN.md](EXPERIMENT_DESIGN.md)

**Important:** None of these steps auto-rewrite your prompt for you.
`pdd checkup lint` is **read-only** ([#1154](https://github.com/promptdriven/pdd/pull/1154)).
The value is **actionable feedback + evidence** so a human (or a separate edit /
formalize step) improves the prompt; then generation runs against a clearer spec.

---

## Three phases (product mental model)

```
┌─────────────────────────────────────────────────────────────┐
│ 1. PROMPT QUALITY (before spend on generate)                │
│    lint → contract check → coverage (+ stories #820)         │
└───────────────────────────┬─────────────────────────────────┘
                            ▼
┌─────────────────────────────────────────────────────────────┐
│ 2. GENERATE + RECORD                                        │
│    pdd generate / test / sync --evidence                    │
└───────────────────────────┬─────────────────────────────────┘
                            ▼
┌─────────────────────────────────────────────────────────────┐
│ 3. SHIP + STABILITY (after code exists)                     │
│    checkup gate → checkup drift (+ optional simplify)       │
└─────────────────────────────────────────────────────────────┘
```

| Phase | Benchmark milestone | Primary scripts |
|-------|---------------------|-----------------|
| 1 — Prompt quality | **M1** | `run_experiment.py`, `cloud_formalize.py`, `checkup_formalize.py` |
| 2 — Generate + record | **M2** | `run_generation_benchmark.py`, `record_pdd_fixtures.py` |
| 3 — Ship + stability | **M3** | `run_drift_benchmark.py`, `run_m3_pipeline.py` |
| 4 — Model efficiency | **M4** ([Experiment 2](../model_efficiency/)) | `run_model_efficiency.py` |

---

## Phase 1 — Better prompts (checkability)

| PR | Command / feature | What it improves | Effect on generation |
|----|-------------------|------------------|----------------------|
| [#1154](https://github.com/promptdriven/pdd/pull/1154) | `pdd checkup lint` | Vague terms, missing vocabulary, weak observable verbs | Fewer ambiguous requirements → model guesses less |
| [#1155](https://github.com/promptdriven/pdd/pull/1155) | `pdd checkup contract check` | `<contract_rules>`, modal structure, MUST-NOT coverage | Machine-checkable obligations, not prose |
| [#1157](https://github.com/promptdriven/pdd/pull/1157) | `pdd checkup coverage` | Rule ID → story `## Covers` → test `test_R*` | Gaps visible before generate |
| [#1271](https://github.com/promptdriven/pdd/pull/1271) / #820 | User story template + `generate_user_story` | Covers, Oracle, Non-Oracle, negative cases | Reviewers and tests agree on pass/fail |

**Together:** Ad-hoc A0 (“validate emails somehow”) becomes formalized A1 when the prompt
**passes lint + contract + coverage** and stories document Oracle vs Non-Oracle. That is
the business lever **M1** measures.

### Read-only checkup loop (no `--apply`)

```bash
pdd checkup lint     path/to/prompt.prompt [--stories dir] [--llm] [--json]
pdd checkup contract check path/to/prompt.prompt [--stories dir] [--json]
pdd checkup coverage path/to/prompt.prompt [--stories-dir dir] [--json]
```

Fix the prompt (or run a **separate** formalize step), then re-run until clean.

Optional advisory pass:

```bash
pdd checkup lint path/to/prompt.prompt --llm --json   # PDD Cloud when not --local
```

### How the benchmark runs Phase 1

| Path | Script | Notes |
|------|--------|-------|
| **Batch corpus (default CI)** | `run_experiment.py` | Uses `formalize_a1.py` (deterministic + optional `--allow-llm`) |
| **Product checkup loop** | `checkup_formalize.py` | Same engines as `pdd checkup lint/contract/coverage` with writeback |
| **PDD Cloud meta-prompt** | `cloud_formalize.py` | `pdd generate` on formalizer template (WIP; not default batch entry) |
| **CI A1 replay** | Copy from `tier_gold/*/pdd_generated/A1.prompt` | Used when re-running M2 without re-formalizing |

M1 **scores** checkability (lint, rules, coverage, #820 story stats); it does **not**
prove lower token cost until M2.

---

## Phase 2 — Better generation economics (evidence + sync)

| PR | Command / feature | What it improves | Effect on generation |
|----|-------------------|------------------|----------------------|
| [#1256](https://github.com/promptdriven/pdd/pull/1256) | `--evidence` on generate/test/sync; `pdd sync --evidence` | Receipt per run: prompt hash, outputs, model/cost, validation | Auditable “what prompt produced what code” |

Without evidence you cannot tell whether a failure was a bad prompt, a bad model call,
or stale artifacts. `pdd sync --evidence` writes
`.pdd/evidence/devunits/*.latest.json` for gate and drift.

### Benchmark M2 wiring

| Mode | Behavior |
|------|----------|
| **`--allow-llm`** | `generation_loop.py` runs `pdd generate` and `pdd test` with `--evidence` (PDD Cloud by default) |
| **`--replay-fixtures`** | Replays `pdd_generated/{A0,A1}/generated/`; no live LLM |
| **`--harness-only`** | Legacy alias path; prefer `--replay-fixtures` |
| **`record_pdd_fixtures.py`** | Records live cloud outputs for CI replay |

Oracle tests under `corpus/tier_gold/*/oracle_tests/` stay **hand-written** (independent
ground truth). Non-oracle tests come from **`pdd test`**.

---

## Phase 3 — Ship gate and regen stability

| PR | Command / feature | What it improves | Effect on generation |
|----|-------------------|------------------|----------------------|
| [#1260](https://github.com/promptdriven/pdd/pull/1260) | `pdd checkup gate` | Policy on evidence: stale outputs, missing tests/verify/stories, unchecked rules | Blocks “vague prompt + stale code” merges |
| [#1261](https://github.com/promptdriven/pdd/pull/1261) | `pdd checkup drift` | Re-generate in temp dirs; compare API/behavior; cost cap | Same prompt must not silently change behavior |
| [#1255](https://github.com/promptdriven/pdd/pull/1255) | `pdd checkup simplify` | Post-gen cleanup in isolated worktrees with verify | Code quality after generate, not prompt writing |

Gate and drift consume **#1256 evidence**. Drift re-runs tests (and optionally
stories/verify/policy) on regenerated candidates.

### Benchmark M3 wiring

```bash
python benchmarks/formalization/pipelines/run_drift_benchmark.py \
  --dry-run          # CI: structural check only
  --allow-llm        # paid: real regen + drift compare
```

`pdd checkup gate` is on the benchmark branch but **not** yet wired into
`run_eval.sh`. Manual follow-up:

```bash
pdd checkup gate --policy .pdd/policy.yml
```

---

## Adhoc vs formalized pairs (without `--apply`)

There is **no** `pdd checkup formalize --apply`. Formalized means **the shape you
get after the checkup stack is satisfied**, not output of one magic command.

| Arm | v0.3 harness (`tasks/*/prompts/`) | M1 corpus (`corpus/tasks/`) |
|-----|-----------------------------------|-----------------------------|
| **Adhoc (A0)** | Hand-curated `adhoc.prompt` | Handcrafted `A0.prompt` (only versioned prompt input) |
| **Formalized (A1)** | Hand-curated `formalized.prompt` (target shape) | **Target:** pass `checkup lint` + `contract check` + `coverage`; produced via PDD Cloud (`pdd generate`) or human edit + checkup loop |

v0.3 fixtures are **static scorecard** arms for epic #833. The scalable experiment
uses the **corpus + M1/M2/M3 pipelines**.

---

## Recommended author loop — M2 (generate + record)

This is the **M2 workflow** the benchmark implements. Run it only after Phase 1
prompt quality is acceptable (formalized A1 or equivalent).

### Prerequisites

```bash
pip install -e ".[dev]"
pdd setup                    # PDD Cloud credentials
# Do NOT pass --local on pdd if you want cloud routing
```

### 1. Ensure M1 A1 exists

```bash
# Deterministic (CI)
python benchmarks/formalization/pipelines/run_experiment.py \
  --output-dir benchmarks/formalization/experiments/ci_smoke

# LLM stages (paid)
python benchmarks/formalization/pipelines/run_experiment.py \
  --allow-llm \
  --output-dir benchmarks/formalization/experiments/latest
```

For CI M2 without re-formalizing, point `--m1-dir` at a directory that already contains
`<task>/A1.prompt` (e.g. `experiments/ci_smoke`).

### 2. Generate and test both arms (A0 vs A1 economics)

```bash
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --allow-llm \
  --max-rounds 3 \
  --max-cost-usd 50 \
  --m1-dir benchmarks/formalization/experiments/latest \
  --output-dir benchmarks/formalization/experiments/m2_latest \
  --tasks email_validator,token_bucket,refund_handler
```

What runs per arm (inside `generation_loop.py`):

1. `pdd generate <prompt> --output generated/src/<module>.py --evidence --force`
2. `pdd test <prompt> <code> --output generated/tests/test_<module>.py --force --evidence`
3. `pytest` on generated tests (non-oracle pass rate)
4. `pytest` on `corpus/tier_gold/*/oracle_tests/` (oracle pass rate)
5. Optional `pdd fix` rounds up to `--max-rounds`

Every command appends to `<task>/<arm>/commands.jsonl` with cost and timing.

### 3. Sync with evidence (product path, optional in benchmark)

After code and tests exist for a dev unit:

```bash
pdd sync <basename>_<language> --evidence
```

This records validation status into `.pdd/evidence/devunits/` for gate/drift.
The benchmark M2 runner does not call `sync` automatically today; add this step
when demonstrating the full #1256 → #1260 chain.

### 4. Record fixtures for CI replay

```bash
python benchmarks/formalization/pipelines/record_pdd_fixtures.py \
  --m1-dir benchmarks/formalization/experiments/latest \
  --tasks email_validator,token_bucket,refund_handler
```

Commits under `corpus/tier_gold/*/pdd_generated/`:

- `A1.prompt` — recorded formalized prompt
- `{A0,A1}/generated/src/` — `pdd generate` output
- `{A0,A1}/generated/tests/` — `pdd test` output

### 5. CI-safe replay (no API keys)

```bash
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --replay-fixtures \
  --skip-formalize \
  --m1-dir benchmarks/formalization/experiments/ci_smoke \
  --output-dir benchmarks/formalization/experiments/ci_m2_smoke \
  --tasks email_validator
```

Or run the full M2→M3 pipeline:

```bash
python benchmarks/formalization/pipelines/run_m3_pipeline.py \
  --replay-fixtures \
  --m1-dir benchmarks/formalization/experiments/ci_smoke \
  --tasks email_validator
```

### 6. Read results

```bash
jq '.tasks[0].evaluation_summary' \
  benchmarks/formalization/experiments/m2_latest/run_manifest.json
```

Compare **oracle** (tier gold, independent) vs **non-oracle** (`pdd test` self-consistency)
and **economics** (rounds, cost, pass rates) between A0 and A1 arms.

---

## PR → benchmark quick map

| PR | Product command | Benchmark touchpoint |
|----|-----------------|----------------------|
| #1154 | `pdd checkup lint` | M1 metrics; `checkup_formalize.py`; cloud lint `--llm` |
| #1155 | `pdd checkup contract check` | M1 metrics; formalize validation |
| #1157 | `pdd checkup coverage` | M1 metrics; corpus stories + `<coverage>` |
| #1271 / #820 | Story template | `corpus/tasks/*/stories/`, `story_metrics.py` |
| #1256 | `--evidence`, `sync --evidence` | M2 `generation_loop.py`; manual sync step above |
| #1260 | `pdd checkup gate` | Manual / future CI; not in `run_eval.sh` yet |
| #1261 | `pdd checkup drift` | M3 `run_drift_benchmark.py` |
| #1255 | `pdd checkup simplify` | Post-M2 optional; not in benchmark harness |

---

## Experiment 2 — Model efficiency (M4)

After M1–M3, run the **separate** benchmark at `benchmarks/model_efficiency/` when you need
the business story: formalization narrows the gap between **budget** and **smart** PDD Cloud
model tiers.

| Comparison | Meaning |
|------------|---------|
| **budget + A1** vs **smart + A0** | Can formalized prompts + cheaper cloud tier approach vague prompts + premium tier? |
| Full matrix | 2 tiers × 2 arms × 3 gold tasks × 3 runs |

Both tiers use **PDD Cloud** (`--strength` 1.0 vs 0.0). A1 formalization uses the smart tier
once per task.

```bash
# CI smoke
bash benchmarks/model_efficiency/scripts/run_eval.sh

# Paid
python benchmarks/model_efficiency/pipelines/run_model_efficiency.py --allow-llm
```

Docs: [../model_efficiency/README.md](../model_efficiency/README.md) ·
[../model_efficiency/BUSINESS_VALUE.md](../model_efficiency/BUSINESS_VALUE.md) ·
[../model_efficiency/EVALUATION.md](../model_efficiency/EVALUATION.md)

---

## Related docs

- [EXPERIMENT_DESIGN.md](EXPERIMENT_DESIGN.md) — three phases, diagrams, command map
- [README.md](README.md) — entry point and artifact policy
- [EVALUATION.md](EVALUATION.md) — step-by-step commands
- [SHOWCASE.md](SHOWCASE.md) — live demo script
- [BUSINESS_VALUE.md](BUSINESS_VALUE.md) — what M1/M2/M3 prove
- [../README.md](../README.md) — both experiments overview
- [../PR.md](../PR.md) — pull request description
- [corpus/README.md](corpus/README.md) — A0 vs replay fixtures
- [corpus/tier_gold/README.md](corpus/tier_gold/README.md) — oracle vs pdd_generated
