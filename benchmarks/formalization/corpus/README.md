# Formalization benchmark — artifact sources

**Design:** [../EXPERIMENT_DESIGN.md](../EXPERIMENT_DESIGN.md) · **Overview:** [../../README.md](../../README.md)

| Artifact | Source | Versioned in git? |
|----------|--------|-------------------|
| **A0 prompt** | Handcrafted by humans | Yes — `corpus/tasks/*/A0.prompt` |
| **A1 prompt** | M1 formalize output | Experiments (gitignored); replay — `tier_gold/*/pdd_generated/A1.prompt` |
| **Generated code** | `pdd generate` (M2) | Replay — `pdd_generated/{A0,A1}/generated/src/` |
| **Generated tests** | `pdd test` (M2) | Replay — `pdd_generated/{A0,A1}/generated/tests/` |
| **Oracle tests** | Hand-written ground truth | Yes — `tier_gold/*/oracle_tests/` |

## Phase 1 — formalize A0 → A1

```bash
# Batch (default CI — deterministic)
python benchmarks/formalization/pipelines/run_experiment.py \
  --output-dir benchmarks/formalization/experiments/ci_smoke

# LLM stages (requires credentials)
python benchmarks/formalization/pipelines/run_experiment.py \
  --allow-llm --output-dir benchmarks/formalization/experiments/latest

# Product checkup loop (single task)
python benchmarks/formalization/pipelines/checkup_formalize.py \
  --input corpus/tasks/email_validator/A0.prompt \
  --output /tmp/A1.prompt \
  --stories-dir corpus/tasks/email_validator/stories
```

## Phase 2 — generate + record (A0 and A1 arms)

```bash
# Live
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --allow-llm --m1-dir benchmarks/formalization/experiments/latest

# Record for CI replay
python benchmarks/formalization/pipelines/record_pdd_fixtures.py \
  --m1-dir benchmarks/formalization/experiments/latest \
  --tasks email_validator,token_bucket,refund_handler
```

## Phase 3 — drift (consumes M2 code)

```bash
bash benchmarks/formalization/scripts/run_live_m3.sh
# or: run_m3_pipeline.py --allow-llm / --replay-fixtures
```

## CI without API keys

```bash
bash benchmarks/formalization/scripts/run_eval.sh
```

Replays `pdd_generated/` fixtures for M2 and dry-run drift for M3.

Do **not** pass `--local` on `pdd` when you intend PDD Cloud routing.

## Layout

```
corpus/
├── manifest.yaml           # Task registry (single source of truth)
├── tasks/<id>/A0.prompt    # Versioned handwritten input only
├── tasks/<id>/stories/     # Optional #820 user stories (tier B gold)
└── tier_gold/<id>/         # Oracle pytest + pdd_generated replay (tier B gold)
```

## Task registry

Edit [`manifest.yaml`](manifest.yaml) to add tasks.

| Field | Purpose |
|-------|---------|
| `id` | Stable task name (used in `--tasks`) |
| `tier` | `A` (no stories) or `B` (stories + oracle) |
| `a0` | Path to A0 prompt relative to `corpus/` |
| `stories_dir` | Optional; coverage linking in checkup formalize |
| `oracle_tests` / `baseline_src` | M2 oracle scoring; baseline fallback if no fixtures |
| `m2` / `m3` | Include in generation / drift batches |

## Scaling

```bash
python benchmarks/formalization/pipelines/run_experiment.py --tasks hello_fn,email_validator
python benchmarks/formalization/pipelines/run_m3_pipeline.py --replay-fixtures --tasks email_validator
```

## v0.3 static harness

Hand-curated fixtures under [`../tasks/`](../tasks/README.md) — separate from this corpus.
