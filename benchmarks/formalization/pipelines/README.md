# M1–M3 pipeline scripts

**Design:** [../EXPERIMENT_DESIGN.md](../EXPERIMENT_DESIGN.md) · **Runbook:** [../EVALUATION.md](../EVALUATION.md)

| Phase | Script | Role |
|-------|--------|------|
| **M1** | [`run_experiment.py`](run_experiment.py) | Batch A0→A1 + `REPORT.md` / `EVALUATION_RESULT.md` |
| **M1** | [`formalize_a1.py`](formalize_a1.py) | Default batch formalizer (deterministic + optional LLM) |
| **M1** | [`checkup_formalize.py`](checkup_formalize.py) | Product checkup loop with writeback |
| **M1** | [`cloud_formalize.py`](cloud_formalize.py) | PDD Cloud meta-prompt A1 (WIP integration) |
| **M2** | [`run_generation_benchmark.py`](run_generation_benchmark.py) | **`pdd generate` on A0 and A1** + oracle scoring |
| **M2** | [`run_m3_pipeline.py`](run_m3_pipeline.py) | **M2 → M3** one command (live or replay) |
| **M3** | [`run_drift_benchmark.py`](run_drift_benchmark.py) | `pdd checkup drift` on M2 code |
| **M2** | [`record_pdd_fixtures.py`](record_pdd_fixtures.py) | Record live outputs → `pdd_generated/` |
| **M2** | [`pdd_fixture_store.py`](pdd_fixture_store.py) | Replay fixtures in CI (`--replay-fixtures`) |

| Helper | Used by |
|--------|---------|
| [`generation_loop.py`](generation_loop.py) | M2 — generate / test / fix + `--evidence` |
| [`checkup_apply.py`](checkup_apply.py) | M1 — parse checkup JSON → prompt writeback |
| [`writeback.py`](writeback.py) | M1 — deterministic section mutations |
| [`command_log.py`](command_log.py) | M2/M3 — JSONL audit log, cost parse |
| [`economics.py`](economics.py) | M2/M3 — business blocks, deltas |
| [`prompt_metrics.py`](prompt_metrics.py) | M1 — lint / contract / coverage metrics |
| [`story_metrics.py`](story_metrics.py) | M1 — #820 Oracle / Non-Oracle stats |
| [`pytest_metrics.py`](pytest_metrics.py) | M2 — oracle pytest scoring |

**Shell scripts:**

| Script | Role |
|--------|------|
| [`../scripts/run_eval.sh`](../scripts/run_eval.sh) | CI smoke — M1 + M2 replay + M3 dry-run |
| [`../scripts/run_live_m3.sh`](../scripts/run_live_m3.sh) | Live M2 generate + M3 drift |

Demo: [../SHOWCASE.md](../SHOWCASE.md) · PR: [../../PR.md](../../PR.md)
