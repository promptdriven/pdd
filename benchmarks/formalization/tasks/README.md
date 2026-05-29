# v0.3 static harness tasks

These directories hold **hand-curated** A0 / A1 / A2 fixtures for the legacy epic #833
**scorecard** (`run_benchmark.py`). They are **not** the scalable M1–M3 corpus experiment.

For the cloud-first experiment (A1/code/tests via PDD CLI), use [`../corpus/`](../corpus/README.md)
and M1–M3 pipelines instead.

**Overview:** [../README.md](../README.md) · **Epic mapping:** [../EPIC833.md](../EPIC833.md)

| Task | Purpose |
|------|---------|
| `email_validator` | Full A0→A1→A2 with baseline code + Z3 tests |
| `refund_payment` | Contract coverage + stories without generated service |
| `payment_api_lint` | Lint delta when vocabulary defines vague terms |

## Run

```bash
python benchmarks/formalization/run_benchmark.py --report
pytest -vv tests/test_formalization_benchmark.py
```

## Adding a v0 task

1. Create `tasks/<task_id>/task.yaml` (see existing tasks).
2. Add `prompts/adhoc.prompt` and `prompts/formalized.prompt`.
3. Optionally add `stories/`, `tests/`, `baseline/`.
4. Run `python benchmarks/formalization/run_benchmark.py --tasks <task_id>`.

For scalable M1–M3 experiments, add tasks to [`../corpus/manifest.yaml`](../corpus/manifest.yaml)
instead.
