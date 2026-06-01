# One `pdd` command per script

**Full literal command reference (all tasks, all phases):** [../COMMANDS.md](../COMMANDS.md)

Each script runs **exactly one** CLI invocation, prints the full quoted command line, and
appends it to `commands.jsonl` when `COMMANDS_LOG` is set. Set `TASK` (and `ARM` for M2/M3) first.

```bash
export TASK=email_validator
export ARM=A0
export M1_DIR=benchmarks/formalization/experiments/latest
export M2_DIR=benchmarks/formalization/experiments/m2_latest
```

## Phase 1 — checkup (prompt quality)

| Script | Single command |
|--------|----------------|
| [`pdd_checkup_lint.sh`](pdd_checkup_lint.sh) | `pdd checkup lint` |
| [`pdd_checkup_contract.sh`](pdd_checkup_contract.sh) | `pdd checkup contract check` |
| [`pdd_checkup_coverage.sh`](pdd_checkup_coverage.sh) | `pdd checkup coverage` |

```bash
TASK=email_validator bash benchmarks/formalization/scripts/cmd/pdd_checkup_lint.sh
PROMPT_ARM=A1 TASK=email_validator bash .../pdd_checkup_lint.sh   # check A1
```

## Phase 2 — generate + record

Run **in order** for one arm:

```bash
TASK=email_validator ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_generate.sh
TASK=email_validator ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_test.sh
TASK=email_validator ARM=A0 bash benchmarks/formalization/scripts/cmd/pytest_generated.sh
TASK=email_validator ARM=A0 bash benchmarks/formalization/scripts/cmd/pytest_oracle.sh

# if generated tests fail:
TASK=email_validator ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_fix.sh
# then re-run pytest scripts
```

| Script | Single command |
|--------|----------------|
| [`pdd_generate.sh`](pdd_generate.sh) | `pdd --force generate … --evidence` |
| [`pdd_test.sh`](pdd_test.sh) | `pdd --force test … --evidence` |
| [`pdd_fix.sh`](pdd_fix.sh) | `pdd fix …` |
| [`pytest_generated.sh`](pytest_generated.sh) | `pytest` on `pdd test` output |
| [`pytest_oracle.sh`](pytest_oracle.sh) | `pytest` on tier_gold oracle |

## Phase 3 — drift

| Script | Single command |
|--------|----------------|
| [`pdd_drift.sh`](pdd_drift.sh) | `pdd checkup drift …` |

```bash
TASK=email_validator ARM=A0 MODE=dry-run bash .../pdd_drift.sh
TASK=email_validator ARM=A1 MODE=live     bash .../pdd_drift.sh
```

## Print resolved paths (debug)

```bash
python benchmarks/formalization/scripts/cmd/_resolve_paths.py m2 \
  --task email_validator --arm A0 \
  --m1-dir benchmarks/formalization/experiments/latest
```

## Typical timeline per arm (live)

| Command | Est. time |
|---------|-----------|
| `pdd generate` | 2–15 min |
| `pdd test` | 2–10 min |
| `pytest_*` | ~1–5 s |
| `pdd fix` | 2–10 min (repeat as needed) |
| `pdd checkup drift` | 1–15 min |

Parent wrappers: [../README.md](../README.md)
