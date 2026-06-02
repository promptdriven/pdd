# Formalization benchmark — all commands (pdd-level)

Single reference for **literal CLI invocations** and thin wrapper scripts under
`benchmarks/formalization/scripts/cmd/`. Run everything from the **repo root**.

**Design context:** [EXPERIMENT_DESIGN.md](EXPERIMENT_DESIGN.md) · **Runbook:** [EVALUATION.md](EVALUATION.md)

Path prefix used below:

```text
BF=benchmarks/formalization
M1=$BF/experiments/latest
M2=$BF/experiments/m2_latest
M3=$BF/experiments/m3_latest
CORPUS=$BF/corpus
```

---

## 0. Prerequisites

```bash
cd /path/to/pdd
pip install -e ".[dev]"    # editable install for --language on generate
pdd setup                    # only for live cloud runs
```

### Environment (set once per shell)

```bash
export M1_DIR=benchmarks/formalization/experiments/latest
export M2_DIR=benchmarks/formalization/experiments/m2_latest
export M3_DIR=benchmarks/formalization/experiments/m3_latest
export TASK=email_validator   # change per task
export ARM=A0                 # A0 or A1 for M2/M3
```

### Resolve paths (debug)

```bash
python benchmarks/formalization/scripts/cmd/_resolve_paths.py m1 \
  --task "$TASK" --m1-dir "$M1_DIR"

python benchmarks/formalization/scripts/cmd/_resolve_paths.py m2 \
  --task "$TASK" --arm "$ARM" --m1-dir "$M1_DIR" --m2-dir "$M2_DIR"

python benchmarks/formalization/scripts/cmd/_resolve_paths.py m3 \
  --task "$TASK" --arm "$ARM" --m1-dir "$M1_DIR" --m2-dir "$M2_DIR" --m3-dir "$M3_DIR"
```

### CLI rules (important)

| Rule | Correct | Wrong |
|------|---------|-------|
| Global `--force` | `pdd --force generate …` | `pdd generate … --force` |
| Language on `A0.prompt` | add `--language python` | omit (fails path construction) |
| `pdd fix` (non-loop) | **4 args:** prompt, code, test, **error file** | 3 args only → usage error |
| Upgrade prompt | answer `n` or use non-interactive env | blocks automation |

---

## 1. Milestone 1 — batch formalization (optional)

```bash
# Deterministic (CI)
python benchmarks/formalization/pipelines/run_experiment.py \
  --output-dir benchmarks/formalization/experiments/ci_smoke

# Live LLM formalization
python benchmarks/formalization/pipelines/run_experiment.py \
  --allow-llm --max-cost-usd 25 \
  --output-dir benchmarks/formalization/experiments/latest
```

Single-task formalize (benchmark script, not `pdd`):

```bash
python benchmarks/formalization/pipelines/formalize_a1.py \
  --input benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --output benchmarks/formalization/experiments/latest/email_validator/A1.prompt \
  --json
```

---

## 2. Phase 1 — checkup (prompt quality)

### Generic pattern

**A0 prompt (corpus):**

```bash
pdd checkup lint     <A0.prompt> [--stories <stories_dir>] --json
pdd checkup contract check <A0.prompt> [--stories <stories_dir>] --json
pdd checkup coverage <A0.prompt> [--stories-dir <stories_dir>] --json
```

**A1 prompt (M1 output):**

```bash
pdd checkup lint     <M1>/<task>/A1.prompt [--stories <stories_dir>] --json
pdd checkup contract check <M1>/<task>/A1.prompt [--stories <stories_dir>] --json
pdd checkup coverage <M1>/<task>/A1.prompt [--stories-dir <stories_dir>] --json
```

**Wrappers:**

```bash
TASK=<task> PROMPT_ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_checkup_lint.sh
TASK=<task> PROMPT_ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_checkup_contract.sh
TASK=<task> PROMPT_ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_checkup_coverage.sh

TASK=<task> PROMPT_ARM=A1 M1_DIR="$M1_DIR" bash benchmarks/formalization/scripts/cmd/pdd_checkup_lint.sh
```

---

### 2.1 `hello_fn` (tier A — no stories, no oracle, no M3)

```bash
# A0 checkup
pdd checkup lint benchmarks/formalization/corpus/tasks/hello_fn/A0.prompt --json
pdd checkup contract check benchmarks/formalization/corpus/tasks/hello_fn/A0.prompt --json
pdd checkup coverage benchmarks/formalization/corpus/tasks/hello_fn/A0.prompt --json

# A1 checkup
pdd checkup lint benchmarks/formalization/experiments/latest/hello_fn/A1.prompt --json
pdd checkup contract check benchmarks/formalization/experiments/latest/hello_fn/A1.prompt --json
pdd checkup coverage benchmarks/formalization/experiments/latest/hello_fn/A1.prompt --json
```

---

### 2.2 `pi_digits` (tier A — no stories, no oracle, no M3)

```bash
pdd checkup lint benchmarks/formalization/corpus/tasks/pi_digits/A0.prompt --json
pdd checkup contract check benchmarks/formalization/corpus/tasks/pi_digits/A0.prompt --json
pdd checkup coverage benchmarks/formalization/corpus/tasks/pi_digits/A0.prompt --json

pdd checkup lint benchmarks/formalization/experiments/latest/pi_digits/A1.prompt --json
pdd checkup contract check benchmarks/formalization/experiments/latest/pi_digits/A1.prompt --json
pdd checkup coverage benchmarks/formalization/experiments/latest/pi_digits/A1.prompt --json
```

---

### 2.3 `email_validator` (tier B — stories + oracle + M3)

```bash
STORIES=benchmarks/formalization/corpus/tasks/email_validator/stories

pdd checkup lint benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --stories "$STORIES" --json
pdd checkup contract check benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --stories "$STORIES" --json
pdd checkup coverage benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --stories-dir "$STORIES" --json

pdd checkup lint benchmarks/formalization/experiments/latest/email_validator/A1.prompt \
  --stories "$STORIES" --json
pdd checkup contract check benchmarks/formalization/experiments/latest/email_validator/A1.prompt \
  --stories "$STORIES" --json
pdd checkup coverage benchmarks/formalization/experiments/latest/email_validator/A1.prompt \
  --stories-dir "$STORIES" --json
```

---

### 2.4 `token_bucket` (tier B)

```bash
STORIES=benchmarks/formalization/corpus/tasks/token_bucket/stories

pdd checkup lint benchmarks/formalization/corpus/tasks/token_bucket/A0.prompt \
  --stories "$STORIES" --json
pdd checkup contract check benchmarks/formalization/corpus/tasks/token_bucket/A0.prompt \
  --stories "$STORIES" --json
pdd checkup coverage benchmarks/formalization/corpus/tasks/token_bucket/A0.prompt \
  --stories-dir "$STORIES" --json

pdd checkup lint benchmarks/formalization/experiments/latest/token_bucket/A1.prompt \
  --stories "$STORIES" --json
pdd checkup contract check benchmarks/formalization/experiments/latest/token_bucket/A1.prompt \
  --stories "$STORIES" --json
pdd checkup coverage benchmarks/formalization/experiments/latest/token_bucket/A1.prompt \
  --stories-dir "$STORIES" --json
```

---

### 2.5 `refund_handler` (tier B)

```bash
STORIES=benchmarks/formalization/corpus/tasks/refund_handler/stories

pdd checkup lint benchmarks/formalization/corpus/tasks/refund_handler/A0.prompt \
  --stories "$STORIES" --json
pdd checkup contract check benchmarks/formalization/corpus/tasks/refund_handler/A0.prompt \
  --stories "$STORIES" --json
pdd checkup coverage benchmarks/formalization/corpus/tasks/refund_handler/A0.prompt \
  --stories-dir "$STORIES" --json

pdd checkup lint benchmarks/formalization/experiments/latest/refund_handler/A1.prompt \
  --stories "$STORIES" --json
pdd checkup contract check benchmarks/formalization/experiments/latest/refund_handler/A1.prompt \
  --stories "$STORIES" --json
pdd checkup coverage benchmarks/formalization/experiments/latest/refund_handler/A1.prompt \
  --stories-dir "$STORIES" --json
```

---

## 3. Phase 2 — M2 generate + record (per task, per arm)

**Order:** `generate` → `test` → `pytest generated` → `pytest oracle` → (`fix` loop)

Substitute `<task>`, `<module>`, and `<arm>` (`A0` or `A1`).

| Arm | Prompt path |
|-----|-------------|
| **A0** | `benchmarks/formalization/corpus/tasks/<task>/A0.prompt` |
| **A1** | `benchmarks/formalization/experiments/latest/<task>/A1.prompt` |

| Artifact | Path |
|----------|------|
| Code | `benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/src/<module>.py` |
| Generated test | `…/generated/tests/test_<module>.py` |
| Command log | `…/<arm>/commands.jsonl` |
| Oracle tests | `benchmarks/formalization/corpus/tier_gold/<task>/oracle_tests/test_*.py` (tier B only) |

### 3.1 Generic M2 commands (copy template)

```bash
# --- generate ---
pdd --force generate \
  <PROMPT> \
  --output benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/src/<module>.py \
  --language python --evidence

# --- test ---
pdd --force test \
  <PROMPT> \
  benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/src/<module>.py \
  --output benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/tests/test_<module>.py \
  --language python --evidence

# --- pytest: non-oracle (pdd test output) ---
pytest benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/tests/test_<module>.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/src"

# --- pytest: oracle (tier B gold tasks only) ---
pytest benchmarks/formalization/corpus/tier_gold/<task>/oracle_tests/test_*.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/src"

# --- fix (non-loop: 4th arg = error file) ---
touch benchmarks/formalization/experiments/m2_latest/<task>/<arm>/pytest.err
pdd --force fix \
  <PROMPT> \
  benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/src/<module>.py \
  benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/tests/test_<module>.py \
  benchmarks/formalization/experiments/m2_latest/<task>/<arm>/pytest.err

# re-run both pytest blocks after fix
```

**Wrappers (same steps):**

```bash
export TASK=<task> ARM=<arm> M1_DIR="$M1_DIR" M2_DIR="$M2_DIR"
bash benchmarks/formalization/scripts/cmd/pdd_generate.sh
bash benchmarks/formalization/scripts/cmd/pdd_test.sh
bash benchmarks/formalization/scripts/cmd/pytest_generated.sh
bash benchmarks/formalization/scripts/cmd/pytest_oracle.sh   # skip hello_fn, pi_digits
# bash benchmarks/formalization/scripts/cmd/pdd_fix.sh       # needs error-file fix in script
```

---

### 3.2 `hello_fn` — A0 arm

```bash
pdd --force generate \
  benchmarks/formalization/corpus/tasks/hello_fn/A0.prompt \
  --output benchmarks/formalization/experiments/m2_latest/hello_fn/A0/generated/src/hello_fn.py \
  --language python --evidence

pdd --force test \
  benchmarks/formalization/corpus/tasks/hello_fn/A0.prompt \
  benchmarks/formalization/experiments/m2_latest/hello_fn/A0/generated/src/hello_fn.py \
  --output benchmarks/formalization/experiments/m2_latest/hello_fn/A0/generated/tests/test_hello_fn.py \
  --language python --evidence

pytest benchmarks/formalization/experiments/m2_latest/hello_fn/A0/generated/tests/test_hello_fn.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/hello_fn/A0/generated/src"
```

### 3.3 `hello_fn` — A1 arm

```bash
pdd --force generate \
  benchmarks/formalization/experiments/latest/hello_fn/A1.prompt \
  --output benchmarks/formalization/experiments/m2_latest/hello_fn/A1/generated/src/hello_fn.py \
  --language python --evidence

pdd --force test \
  benchmarks/formalization/experiments/latest/hello_fn/A1.prompt \
  benchmarks/formalization/experiments/m2_latest/hello_fn/A1/generated/src/hello_fn.py \
  --output benchmarks/formalization/experiments/m2_latest/hello_fn/A1/generated/tests/test_hello_fn.py \
  --language python --evidence

pytest benchmarks/formalization/experiments/m2_latest/hello_fn/A1/generated/tests/test_hello_fn.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/hello_fn/A1/generated/src"
```

---

### 3.4 `pi_digits` — A0 arm

```bash
pdd --force generate \
  benchmarks/formalization/corpus/tasks/pi_digits/A0.prompt \
  --output benchmarks/formalization/experiments/m2_latest/pi_digits/A0/generated/src/pi_digits.py \
  --language python --evidence

pdd --force test \
  benchmarks/formalization/corpus/tasks/pi_digits/A0.prompt \
  benchmarks/formalization/experiments/m2_latest/pi_digits/A0/generated/src/pi_digits.py \
  --output benchmarks/formalization/experiments/m2_latest/pi_digits/A0/generated/tests/test_pi_digits.py \
  --language python --evidence

pytest benchmarks/formalization/experiments/m2_latest/pi_digits/A0/generated/tests/test_pi_digits.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/pi_digits/A0/generated/src"
```

### 3.5 `pi_digits` — A1 arm

```bash
pdd --force generate \
  benchmarks/formalization/experiments/latest/pi_digits/A1.prompt \
  --output benchmarks/formalization/experiments/m2_latest/pi_digits/A1/generated/src/pi_digits.py \
  --language python --evidence

pdd --force test \
  benchmarks/formalization/experiments/latest/pi_digits/A1.prompt \
  benchmarks/formalization/experiments/m2_latest/pi_digits/A1/generated/src/pi_digits.py \
  --output benchmarks/formalization/experiments/m2_latest/pi_digits/A1/generated/tests/test_pi_digits.py \
  --language python --evidence

pytest benchmarks/formalization/experiments/m2_latest/pi_digits/A1/generated/tests/test_pi_digits.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/pi_digits/A1/generated/src"
```

---

### 3.6 `email_validator` — A0 arm

```bash
pdd --force generate \
  benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --output benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/src/email_validator.py \
  --language python --evidence

pdd --force test \
  benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/src/email_validator.py \
  --output benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/tests/test_email_validator.py \
  --language python --evidence

pytest benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/tests/test_email_validator.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/src"

pytest benchmarks/formalization/corpus/tier_gold/email_validator/oracle_tests/test_*.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/src"

touch benchmarks/formalization/experiments/m2_latest/email_validator/A0/pytest.err
pdd --force fix \
  benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/src/email_validator.py \
  benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/tests/test_email_validator.py \
  benchmarks/formalization/experiments/m2_latest/email_validator/A0/pytest.err
```

**Live result doc:** [experiments/m2_latest/email_validator/A0/EVALUATION_RESULT.md](experiments/m2_latest/email_validator/A0/EVALUATION_RESULT.md)

---

### 3.7 `email_validator` — A1 arm

```bash
pdd --force generate \
  benchmarks/formalization/experiments/latest/email_validator/A1.prompt \
  --output benchmarks/formalization/experiments/m2_latest/email_validator/A1/generated/src/email_validator.py \
  --language python --evidence

pdd --force test \
  benchmarks/formalization/experiments/latest/email_validator/A1.prompt \
  benchmarks/formalization/experiments/m2_latest/email_validator/A1/generated/src/email_validator.py \
  --output benchmarks/formalization/experiments/m2_latest/email_validator/A1/generated/tests/test_email_validator.py \
  --language python --evidence

pytest benchmarks/formalization/experiments/m2_latest/email_validator/A1/generated/tests/test_email_validator.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/email_validator/A1/generated/src"

pytest benchmarks/formalization/corpus/tier_gold/email_validator/oracle_tests/test_*.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/email_validator/A1/generated/src"
```

---

### 3.8 `token_bucket` — A0 arm

```bash
pdd --force generate \
  benchmarks/formalization/corpus/tasks/token_bucket/A0.prompt \
  --output benchmarks/formalization/experiments/m2_latest/token_bucket/A0/generated/src/token_bucket.py \
  --language python --evidence

pdd --force test \
  benchmarks/formalization/corpus/tasks/token_bucket/A0.prompt \
  benchmarks/formalization/experiments/m2_latest/token_bucket/A0/generated/src/token_bucket.py \
  --output benchmarks/formalization/experiments/m2_latest/token_bucket/A0/generated/tests/test_token_bucket.py \
  --language python --evidence

pytest benchmarks/formalization/experiments/m2_latest/token_bucket/A0/generated/tests/test_token_bucket.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/token_bucket/A0/generated/src"

pytest benchmarks/formalization/corpus/tier_gold/token_bucket/oracle_tests/test_*.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/token_bucket/A0/generated/src"
```

### 3.9 `token_bucket` — A1 arm

```bash
pdd --force generate \
  benchmarks/formalization/experiments/latest/token_bucket/A1.prompt \
  --output benchmarks/formalization/experiments/m2_latest/token_bucket/A1/generated/src/token_bucket.py \
  --language python --evidence

pdd --force test \
  benchmarks/formalization/experiments/latest/token_bucket/A1.prompt \
  benchmarks/formalization/experiments/m2_latest/token_bucket/A1/generated/src/token_bucket.py \
  --output benchmarks/formalization/experiments/m2_latest/token_bucket/A1/generated/tests/test_token_bucket.py \
  --language python --evidence

pytest benchmarks/formalization/experiments/m2_latest/token_bucket/A1/generated/tests/test_token_bucket.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/token_bucket/A1/generated/src"

pytest benchmarks/formalization/corpus/tier_gold/token_bucket/oracle_tests/test_*.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/token_bucket/A1/generated/src"
```

---

### 3.10 `refund_handler` — A0 arm

```bash
pdd --force generate \
  benchmarks/formalization/corpus/tasks/refund_handler/A0.prompt \
  --output benchmarks/formalization/experiments/m2_latest/refund_handler/A0/generated/src/refund_handler.py \
  --language python --evidence

pdd --force test \
  benchmarks/formalization/corpus/tasks/refund_handler/A0.prompt \
  benchmarks/formalization/experiments/m2_latest/refund_handler/A0/generated/src/refund_handler.py \
  --output benchmarks/formalization/experiments/m2_latest/refund_handler/A0/generated/tests/test_refund_handler.py \
  --language python --evidence

pytest benchmarks/formalization/experiments/m2_latest/refund_handler/A0/generated/tests/test_refund_handler.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/refund_handler/A0/generated/src"

pytest benchmarks/formalization/corpus/tier_gold/refund_handler/oracle_tests/test_*.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/refund_handler/A0/generated/src"
```

### 3.11 `refund_handler` — A1 arm

```bash
pdd --force generate \
  benchmarks/formalization/experiments/latest/refund_handler/A1.prompt \
  --output benchmarks/formalization/experiments/m2_latest/refund_handler/A1/generated/src/refund_handler.py \
  --language python --evidence

pdd --force test \
  benchmarks/formalization/experiments/latest/refund_handler/A1.prompt \
  benchmarks/formalization/experiments/m2_latest/refund_handler/A1/generated/src/refund_handler.py \
  --output benchmarks/formalization/experiments/m2_latest/refund_handler/A1/generated/tests/test_refund_handler.py \
  --language python --evidence

pytest benchmarks/formalization/experiments/m2_latest/refund_handler/A1/generated/tests/test_refund_handler.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/refund_handler/A1/generated/src"

pytest benchmarks/formalization/corpus/tier_gold/refund_handler/oracle_tests/test_*.py \
  --import-mode=importlib -q \
  --override-ini="pythonpath=benchmarks/formalization/experiments/m2_latest/refund_handler/A1/generated/src"
```

---

## 4. Phase 2 — M2 batch (pipeline, not one-command scripts)

```bash
# Live — all M2 tasks
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --allow-llm --m1-dir benchmarks/formalization/experiments/latest

# Live — subset
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --allow-llm --m1-dir benchmarks/formalization/experiments/latest \
  --tasks email_validator,token_bucket

# CI replay (fixtures)
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --replay-fixtures --skip-formalize \
  --m1-dir benchmarks/formalization/experiments/ci_smoke

# One step via pipeline
python benchmarks/formalization/pipelines/run_m2_step.py \
  --task email_validator --arm A0 --step generate --allow-llm \
  --m1-dir benchmarks/formalization/experiments/latest \
  --m2-dir benchmarks/formalization/experiments/m2_latest
```

---

## 5. Phase 3 — M3 drift (tier B gold tasks only)

Requires M2 code on disk. Evidence JSON is auto-created by `pdd_drift.sh` if missing.

### Generic pattern

```bash
# dry-run (smoke)
pdd checkup drift <module> \
  --from-evidence benchmarks/formalization/experiments/m3_latest/<task>/evidence_<arm>.json \
  --code-file benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/src/<module>.py \
  --dry-run --json

# live regen compare
pdd checkup drift <module> \
  --from-evidence benchmarks/formalization/experiments/m3_latest/<task>/evidence_<arm>.json \
  --code-file benchmarks/formalization/experiments/m2_latest/<task>/<arm>/generated/src/<module>.py \
  --json
```

**Wrappers:**

```bash
export M3_DIR=benchmarks/formalization/experiments/m3_latest
TASK=<task> ARM=<arm> MODE=dry-run bash benchmarks/formalization/scripts/cmd/pdd_drift.sh
TASK=<task> ARM=<arm> MODE=live   bash benchmarks/formalization/scripts/cmd/pdd_drift.sh
```

---

### 5.1 `email_validator`

```bash
# A0 dry-run
pdd checkup drift email_validator \
  --from-evidence benchmarks/formalization/experiments/m3_latest/email_validator/evidence_A0.json \
  --code-file benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/src/email_validator.py \
  --dry-run --json

# A0 live
pdd checkup drift email_validator \
  --from-evidence benchmarks/formalization/experiments/m3_latest/email_validator/evidence_A0.json \
  --code-file benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/src/email_validator.py \
  --json

# A1 dry-run
pdd checkup drift email_validator \
  --from-evidence benchmarks/formalization/experiments/m3_latest/email_validator/evidence_A1.json \
  --code-file benchmarks/formalization/experiments/m2_latest/email_validator/A1/generated/src/email_validator.py \
  --dry-run --json

# A1 live
pdd checkup drift email_validator \
  --from-evidence benchmarks/formalization/experiments/m3_latest/email_validator/evidence_A1.json \
  --code-file benchmarks/formalization/experiments/m2_latest/email_validator/A1/generated/src/email_validator.py \
  --json
```

---

### 5.2 `token_bucket`

```bash
pdd checkup drift token_bucket \
  --from-evidence benchmarks/formalization/experiments/m3_latest/token_bucket/evidence_A0.json \
  --code-file benchmarks/formalization/experiments/m2_latest/token_bucket/A0/generated/src/token_bucket.py \
  --dry-run --json

pdd checkup drift token_bucket \
  --from-evidence benchmarks/formalization/experiments/m3_latest/token_bucket/evidence_A1.json \
  --code-file benchmarks/formalization/experiments/m2_latest/token_bucket/A1/generated/src/token_bucket.py \
  --json
```

---

### 5.3 `refund_handler`

```bash
pdd checkup drift refund_handler \
  --from-evidence benchmarks/formalization/experiments/m3_latest/refund_handler/evidence_A0.json \
  --code-file benchmarks/formalization/experiments/m2_latest/refund_handler/A0/generated/src/refund_handler.py \
  --dry-run --json

pdd checkup drift refund_handler \
  --from-evidence benchmarks/formalization/experiments/m3_latest/refund_handler/evidence_A1.json \
  --code-file benchmarks/formalization/experiments/m2_latest/refund_handler/A1/generated/src/refund_handler.py \
  --json
```

---

## 6. Phase 3 — M2+M3 combined pipelines

```bash
# CI replay smoke
python benchmarks/formalization/pipelines/run_m3_pipeline.py \
  --replay-fixtures \
  --m1-dir benchmarks/formalization/experiments/ci_smoke \
  --tasks email_validator

# Live
python benchmarks/formalization/pipelines/run_m3_pipeline.py \
  --allow-llm \
  --m1-dir benchmarks/formalization/experiments/latest

bash benchmarks/formalization/scripts/run_live_m3.sh
```

---

## 7. Full CI smoke (all milestones)

```bash
bash benchmarks/formalization/scripts/run_eval.sh
pytest -q tests/test_formalization_benchmark.py tests/test_formalization_pipeline.py
```

---

## 8. Wrapper script index

| Script | Literal command |
|--------|-----------------|
| `pdd_checkup_lint.sh` | `pdd checkup lint … --json` |
| `pdd_checkup_contract.sh` | `pdd checkup contract check … --json` |
| `pdd_checkup_coverage.sh` | `pdd checkup coverage … --json` |
| `pdd_generate.sh` | `pdd --force generate … --language python --evidence` |
| `pdd_test.sh` | `pdd --force test … --language python --evidence` |
| `pdd_fix.sh` | `pdd fix …` (⚠ needs 4th error-file arg — use raw command in §3.1) |
| `pytest_generated.sh` | `pytest <generated test> …` |
| `pytest_oracle.sh` | `pytest <oracle>/test_*.py …` |
| `pdd_drift.sh` | `pdd checkup drift … [--dry-run] --json` |

All scripts: `benchmarks/formalization/scripts/cmd/`

---

## 9. Suggested live run order

1. M1 already done → `experiments/latest/` has all `A1.prompt`
2. Per task, **A0 then A1**: §3 generate → test → pytest ×2 → fix loop
3. Gold tasks only: §5 drift A0 + A1
4. Write `EVALUATION_RESULT.md` under each `m2_latest/<task>/<arm>/`

**Current progress:** `email_validator` A0 partial — see
[experiments/m2_latest/email_validator/A0/EVALUATION_RESULT.md](experiments/m2_latest/email_validator/A0/EVALUATION_RESULT.md)
