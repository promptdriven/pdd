# Formalization benchmark — runnable steps

**Design:** [../EXPERIMENT_DESIGN.md](../EXPERIMENT_DESIGN.md)

## Granularity ladder

```
scripts/cmd/*.sh     ONE pdd (or pytest) command each  ← smallest
scripts/run_m2_arm.sh     one STEP wrapper
scripts/run_m2_task.sh    one task, both arms
scripts/run_m2.sh         all gold tasks
```

**One command each:** [cmd/README.md](cmd/README.md)

```
Phase 1   run_m1.sh              all corpus tasks
          run_m1_task.sh         one task

Phase 2   run_m2.sh              all gold tasks × both arms
          run_m2_task.sh         one task × both arms
          run_m2_arm.sh          one task × one arm × one STEP

Phase 3   run_m3.sh              all gold tasks
          run_m3_arm.sh          one task; one pdd checkup drift per arm
```

### M2 micro-steps (`STEP=`)

| STEP | Cloud? | Typical time | Needs |
|------|--------|--------------|-------|
| `generate` | Yes | **2–15 min** | prompt |
| `test` | Yes | **2–10 min** | code from generate |
| `fix` | Yes | **2–10 min** | code + generated tests (one round) |
| `score` | No | **~1–5 s** | code (+ optional tests) |
| `replay` | No | **~2 s** | tier_gold fixtures |
| `all` | Yes | sum of above + fix loop | same as full arm |

---

## Phase 1

```bash
# One task only (~5–30s deterministic; ~30–90s with ALLOW_LLM=1)
TASK=email_validator bash benchmarks/formalization/scripts/run_m1_task.sh
```

---

## Phase 2 — smallest live unit (recommended)

Run **one cloud call at a time** for `email_validator` / A0:

```bash
export M1_DIR=benchmarks/formalization/experiments/latest
export M2_DIR=benchmarks/formalization/experiments/m2_latest
export TASK=email_validator
export ARM=A0

# 1) Generate code (~2–15 min)
STEP=generate bash benchmarks/formalization/scripts/run_m2_arm.sh

# 2) Generate tests (~2–10 min)
STEP=test bash benchmarks/formalization/scripts/run_m2_arm.sh

# 3) Score without cloud (~seconds)
STEP=score bash benchmarks/formalization/scripts/run_m2_arm.sh

# 4) If tests fail, one fix round at a time
STEP=fix bash benchmarks/formalization/scripts/run_m2_arm.sh
STEP=score bash benchmarks/formalization/scripts/run_m2_arm.sh

# Repeat fix+score until green or give up
```

Then repeat for **`ARM=A1`**.

Full arm in one command (same as before):

```bash
TASK=email_validator ARM=A0 STEP=all \
  bash benchmarks/formalization/scripts/run_m2_arm.sh
```

Both arms for one task:

```bash
TASK=email_validator bash benchmarks/formalization/scripts/run_m2_task.sh
```

---

## Phase 3 — per task

Runs **one `pdd checkup drift` command per arm** (see `cmd/pdd_drift.sh`). For aggregated
`result.json` / `REPORT.md`, use `run_m3.sh` instead.

```bash
TASK=email_validator MODE=dry-run bash benchmarks/formalization/scripts/run_m3_arm.sh
TASK=email_validator ARM=A0 MODE=live bash benchmarks/formalization/scripts/run_m3_arm.sh
```

---

## CI (no API keys)

```bash
TASK=email_validator ARM=A0 STEP=replay MODE=replay \
  bash benchmarks/formalization/scripts/run_m2_arm.sh
STEP=score bash benchmarks/formalization/scripts/run_m2_arm.sh
```

---

## Monitor one step

```bash
tail -1 benchmarks/formalization/experiments/m2_latest/email_validator/A0/commands.jsonl | jq .
ls -la benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/src/
```

---

## Composed runs

| Script | Scope |
|--------|--------|
| `run_eval.sh` | Full CI smoke |
| `run_m1.sh` / `run_m2.sh` / `run_m3.sh` | Whole phase |
| `run_m2_task.sh` | 1 task, 2 arms |
| `run_m2_arm.sh` | 1 task, 1 arm, 1 step |

Python equivalent for micro-steps:

```bash
python benchmarks/formalization/pipelines/run_m2_step.py \
  --task email_validator --arm A0 --step generate --allow-llm \
  --m1-dir benchmarks/formalization/experiments/latest
```

---

## Typical paid timeline (3 gold tasks, micro-steps)

| Unit | Count | Est. time each | Total |
|------|-------|----------------|-------|
| `generate` | 6 (3 tasks × 2 arms) | 5–10 min | **30–60 min** |
| `test` | 6 | 3–8 min | **18–48 min** |
| `fix` | 0–12+ | 3–8 min | variable |
| `score` | 6 | seconds | negligible |
| M3 live | 6 arms × 2 runs | 5–15 min | **60–180 min** |

Running **one STEP at a time** lets you stop/resume without losing progress.
