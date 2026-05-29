# M2 pipeline roadmap — generation economics

Implemented (M2/M3):

```bash
python benchmarks/formalization/pipelines/run_generation_benchmark.py --harness-only ...
python benchmarks/formalization/pipelines/run_drift_benchmark.py --dry-run ...
```

Original planned command:

```bash
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --tasks email_validator,token_bucket \
  --max-rounds 5 \
  --oracle-dir corpus/tier_gold/email_validator/oracle_tests \
  --output-dir experiments/m2_run_001
```

## Per task, per arm (A0 and A1)

For the same model and temperature:

1. `pdd generate` from prompt → `generated/src/<module>.py` (log tokens, cost, time)
2. `pdd test` from prompt + code → `generated/tests/` (log tokens, cost, time)
3. `pytest` generated tests → `generated_test_pass_rate`
4. `pytest` oracle tests (gold subset) → `oracle_test_pass_rate`
5. On failure: `pdd fix` or `pdd crash` up to `--max-rounds` → count **rounds_to_acceptable**
6. Append every command to `commands.jsonl` with cost tracker fields

## Success criteria (business)

| Metric | Expected direction (A1 vs A0) |
|--------|-------------------------------|
| `rounds_to_acceptable` | A1 ≤ A0 (fewer repair loops) |
| `cost_usd` | A1 ≤ A0 or justified by higher oracle pass rate |
| `oracle_test_pass_rate` | A1 > A0 |
| `generated_test_pass_rate` | Informative only (self-consistency) |

## Oracle tests (required)

Hand-written tests under `corpus/tier_gold/<task>/oracle_tests/` — not generated from
the same prompt. Minimum three gold tasks: `email_validator`, `token_bucket`,
`refund_handler`.

## Report line template

```text
Formalized prompts (A1) required {delta_rounds} fewer generate/fix rounds than ad-hoc (A0)
on {task_count} tasks, with oracle pass rate {a1_oracle}% vs {a0_oracle}% at +${delta_cost}
formalization overhead.
```
