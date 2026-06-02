# Tier gold artifacts (M2)

**Overview:** [../../../README.md](../../../README.md) · **Corpus:** [../README.md](../README.md) · **PR:** [../../../PR.md](../../../PR.md)

Three artifact types live under each gold task directory:

| Path | Produced by | Purpose |
|------|-------------|---------|
| `pdd_generated/{A0,A1}/generated/` | **`pdd generate`** + **`pdd test`** (recorded) | Code + non-oracle tests replayed in CI |
| `oracle_tests/` | Hand-written (intentional) | Independent ground-truth pytest |
| `baseline_src/` | Deprecated fallback | Used only when `pdd_generated` fixtures are missing |

## PDD-generated fixtures (canonical for code + tests)

Live M2 runs:

```bash
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --allow-llm --m1-dir benchmarks/formalization/experiments/latest
```

Record outputs for CI replay (requires API keys):

```bash
python benchmarks/formalization/pipelines/record_pdd_fixtures.py \
  --m1-dir benchmarks/formalization/experiments/latest \
  --tasks email_validator,token_bucket,refund_handler
```

CI harness mode replays committed fixtures instead of calling the LLM:

```bash
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --replay-fixtures --skip-formalize --m1-dir experiments/ci_smoke
```

Each `fixture_manifest.json` tracks prompt hashes and provenance (`pdd_cli_record` vs
`bootstrap_pending_pdd_record`).

## Oracle tests (not pdd-generated)

Oracle tests stay **hand-written** by design — they measure whether code meets requirements
*independently* of the prompt and of `pdd test` output.

## v0.3 `tasks/*/baseline/` (separate harness)

The static epic #833 harness under `benchmarks/formalization/tasks/` uses hand-curated
A2 reference code for TEF scoring. That path does **not** run `pdd generate` today; use
the M1–M3 corpus + M2 pipeline for PDD-generated artifacts.
