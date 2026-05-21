# Prompt lint + contracts E2E demo

This folder demonstrates the **PDD authoring → codegen → test** chain on one problem
domain (idempotent HTTP handler: JWT, active user, 24-hour idempotency store). It uses
**three hand-authored prompts** (vague, formalized, codegen) plus **live artifacts**
under `reports/` (gitignored).

| Mode | Command | API? | What it proves |
|------|---------|------|----------------|
| **Deterministic** | `bash demo.sh` | No | Vague vs formalized **prompt** quality (lint, contracts, coverage). |
| **Live** | `bash demo.sh --live --keep-artifacts` | Yes | Full chain: **before/after** generate + test + pytest around **clarify**. |

Install the CLI from the repo root before live runs: `pip install -e .` and
`export PDD_SKIP_UPDATE_CHECK=1`.

---

## Troubleshooting: `pdd test` still fails

### 1. Wrong `pdd` on PATH (most common)

`which pdd` must point at an **editable install of this repo**, not `~/.local/bin/pdd`
(PyPI / uv tool, e.g. `0.0.243`). The test syntax fix (`finalize_python_test_content`)
exists only in the repo you are developing.

```bash
cd /path/to/pdd
pip install -e .                    # run inside your (pdd-cli) conda env
export PDD_SKIP_UPDATE_CHECK=1
python -c "from pdd.generate_test import finalize_python_test_content; print('ok')"
which pdd
pdd --version                       # should show 0.0.218.dev* when editable
```

From the demo folder, you can force the repo venv CLI:

```bash
../../.venv/bin/pdd test --manual ...    # after pip install -e . in repo .venv
# or
bash lib/pdd_from_repo.sh test --manual ...
```

### 2. Output went to `test_foo_work_after_1.py`, not `test_foo_work_after.py`

`pdd test` **without `--force`** avoids overwriting an existing file and writes
`base_1.py`, `base_2.py`, … instead. You may still be `py_compile`’ing the **old**
broken `tests/test_foo_work_after.py`.

Use:

```bash
pdd --force test --manual prompts/foo_work_python.prompt src/foo_work_after.py \
  --output tests/test_foo_work_after.py
```

Or repair the file on disk:

```bash
python lib/repair_test_syntax.py tests/test_foo_work_after.py
python3.12 -m py_compile tests/test_foo_work_after.py
```

### 3. Syntax OK but pytest fails

That is normal: LLM tests can disagree with generated handler behavior (e.g. 401 vs
403 ordering). With the repo fix, expect **valid Python** and many passing tests; a few
assertion failures are separate from the empty-`if` syntax bug.

---

## Directory map

```
examples/prompt_lint_contract_e2e_demo/
├── README.md
├── demo.sh                      # deterministic | --live | --cleanup
├── .pddrc
├── prompts/
│   ├── foo_vague_python.prompt      # hand-authored (negative)
│   ├── foo_formalized_python.prompt # hand-authored (positive gold)
│   └── foo_codegen_python.prompt    # hand-authored (live workhorse)
├── user_stories/story__foo_*.md
├── lib/
│   ├── run_e2e.py               # deterministic (CliRunner)
│   ├── live_pipeline.sh         # live (real pdd + LLM)
│   └── artifacts.sh
├── prompts/foo_work_python.prompt   # ephemeral work copy (live)
├── src/foo_work_{before,after}.py   # ephemeral (live)
├── tests/test_foo_work_{before,after}.py
└── reports/                     # generated (gitignored)
    ├── vague.json, formalized.json, comparison.json
    ├── live.json, live_clarify.json, live_compile.json, live_coverage.json
    ├── artifacts/               # frozen snapshots
    └── diffs/                   # unified diffs
```

---

## Hand-authored inputs

| File | Role |
|------|------|
| `foo_vague_python.prompt` | **Negative** — vague rules; deterministic demo only. |
| `foo_formalized_python.prompt` | **Gold** — vocabulary, compilable rules, formalization; distance target after clarify. |
| `foo_codegen_python.prompt` | **Live workhorse** — detailed `<requirements>` + vague `<contract_rules>`; copied to `foo_work_python.prompt` for clarify. |

**Do not** run `pdd prompt lint --ambiguity --apply` on `foo_codegen_python.prompt` in git
unless you intend to overwrite it. Restore from `reports/artifacts/prompt_codegen_before.prompt`.

---

## Workflow A — Deterministic (CI, no LLM)

```bash
cd examples/prompt_lint_contract_e2e_demo
bash demo.sh
```

For each of `foo_vague` and `foo_formalized`, runs:

`pdd prompt lint` → `contracts check/compile` → `coverage --contracts` → formalization report.

**Outputs:** `reports/vague.json`, `reports/formalized.json`, `reports/comparison.json`,
`reports/diffs/prompt_vague_vs_formalized.diff`.

**Expected:** vague has many lint warns and compile errors; formalized has none.

```bash
pytest tests/test_prompt_lint_contract_e2e_demo.py -q
```

---

## Workflow B — Live (real LLM, before/after codegen)

```bash
cd examples/prompt_lint_contract_e2e_demo
export PDD_SKIP_UPDATE_CHECK=1
pdd auth status   # or set API keys / PDD_MODEL_DEFAULT
bash demo.sh --live --keep-artifacts
```

### Step-by-step (what the script does)

```text
⓪  LLM preflight (tiny llm_invoke “ok”)
①  cp foo_codegen → foo_work_python.prompt; snapshot reference prompts
②  Lint work copy (BEFORE) — warn baseline
③  BEFORE stack on unclarified work copy:
       pdd --force generate → src/foo_work_before.py
       pdd test --manual     → tests/test_foo_work_before.py
       py_compile + pytest
④  CLARIFY: pdd prompt lint --ambiguity --non-interactive --apply --contracts --json
⑤  Lint work copy (AFTER) — warn count should drop
⑥  contracts compile + coverage --contracts (on clarified prompt)
⑦  AFTER stack on clarified work copy:
       generate → src/foo_work_after.py
       test     → tests/test_foo_work_after.py
       py_compile + pytest
⑧  Write diffs (prompt, src, tests) and reports/live.json
⑨  Summary; cleanup unless --keep-artifacts
```

### What you compare (before vs after clarify)

| Dimension | Before | After |
|-----------|--------|-------|
| **Prompt** | `prompt_codegen_before.prompt` (79 lines) | `prompt_codegen_clarified.prompt` (~183 lines) |
| **Lint warns** | High (e.g. 33) | Low (e.g. 1) |
| **Implementation** | `src/foo_work_before.py` | `src/foo_work_after.py` |
| **Tests** | `tests/test_foo_work_before.py` | `tests/test_foo_work_after.py` |
| **Behavioral gate** | `py_compile` + `pytest` | same |

Clarify mutates **only** `foo_work_python.prompt` in place; originals in `prompts/` stay
unchanged if you only use the work copy.

### Artifacts to inspect after a run

| Path | Meaning |
|------|---------|
| `reports/live_clarify.json` | Raw clarify JSON (ambiguities, guidance, `formalization_rejected`) |
| `reports/live_compile.json` | Obligation IR after clarify |
| `reports/live.json` | Summary metrics (when write succeeds) |
| `reports/diffs/prompt_codegen_before_vs_clarified.diff` | What `--apply` added to the prompt |
| `reports/diffs/src_before_vs_after.diff` | Code delta |
| `reports/diffs/tests_before_vs_after.diff` | Test delta |

---

## Sample live run (interpretation)

The table below matches a real `bash demo.sh --live --keep-artifacts` run
(May 2026, preflight: Fireworks/Kimi; generate: Claude Opus 4.7).

| Step | Result | Interpretation |
|------|--------|----------------|
| Preflight | OK | LLM credentials and routing work. |
| Lint before | **33 warn**, 0 error | Vague contract language in `foo_codegen` is detected. |
| BEFORE generate | **11 610 B** → `foo_work_before.py` | `pdd generate` succeeds on unclarified prompt (requirements/deliverables are concrete). |
| BEFORE test | **18 713 B**, `Cloud Success` | `pdd test` returns content. |
| BEFORE py_compile | **FAIL** | Generated test file is **invalid Python** (see [issues](#issues-observed-in-live-runs)). |
| BEFORE pytest | **SKIP** | No tests run — collection blocked by syntax error. |
| Clarify | **15** ambiguities, **0** formalization rejected | Coach merged vocabulary/rules/acceptance; strict formalization gate passed. |
| Lint after | **1 warn**, 0 error | Clarify helped the **prompt** substantially. |
| Contracts compile | **0 errors** | Clarified prompt compiles to obligations. |
| AFTER generate | **11 099 B** → `foo_work_after.py` | Second implementation (may differ line-by-line from before). |
| AFTER test | **18 185 B**, `Cloud Success` | Test file regenerated from clarified prompt + new code. |
| AFTER py_compile | **FAIL** | Still invalid Python — clarify did **not** fix test **syntax**. |
| AFTER pytest | **SKIP** | Behavioral layer not exercised. |
| Diffs | 3 + 1 + 2 + 4 hunks | Prompt, distance-to-gold, src, tests all changed. |
| `live.json` | **Crash** (fixed in repo) | `write_live_json` argv off-by-one (`expected 18, got 17`) — summary missing until fixed. |

### What this run actually proved

**Succeeded (prompt / contracts path):**

- Clarify finds ambiguities and applies coach output.
- Lint warnings drop sharply (33 → 1).
- Contracts compile on the clarified prompt.
- Generate produces non-empty `src/` for both before and after.

**Did not succeed (behavioral path):**

- Neither before nor after test file passed `py_compile`.
- Pytest never collected tests — **no pass/fail counts for handler behavior**.

**Implication:** For this fixture and models, **prompt clarify works**; **`pdd test` output
quality is the bottleneck**, not clarify. Judging “E2E success” only by pytest green would
misread a run like this as “clarify failed” when clarify on the prompt clearly worked.

---

## Issues observed in live runs

### 1. Invalid Python in `pdd test` output (main blocker)

**Fix in PDD (not demo-only):** `finalize_python_test_content()` in `pdd/generate_test.py`
runs for **cloud and local** `pdd test` before writing the file: strips duplicate
`sys.path` blocks, removes empty `if … sys.path:` headers, injects a marked preamble
(after `from __future__`), and rejects output that fails `ast.parse`. Install from repo
root then re-run test generation:

```bash
cd /path/to/pdd && pip install -e .
pdd test --manual prompts/foo_work_python.prompt src/foo_work_after.py \
  --output tests/test_foo_work_after.py
python3.12 -m py_compile tests/test_foo_work_after.py
```

Typical broken pattern (older runs without that fix):

```python
# PDD-injected preamble (valid)
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

# LLM-added block — insert line stripped, empty if remains
_PROJECT_ROOT = Path(__file__).resolve().parent
if str(_PROJECT_ROOT) not in sys.path:

from src.foo_work_before import (   # IndentationError: expected indented block
    ...
)
```

**Cause:** `generate_test` strips `sys.path.insert(...)` inside an `if` but can leave the
`if` header; cloud/local test LLM also emits a second path block that fights the canonical
preamble.

**Effect:** `py_compile` fails → pytest skipped → pipeline cannot measure behavioral pass rate.

### 2. Wrong import path in generated tests

Tests may use `from src.foo_work_before import ...` while the module under test is
`foo_work` in `src/foo_work_before.py` (basename `foo_work`, not `foo_work_before`).
Even with valid syntax, imports can fail at collection time.

### 3. `live.json` not written (script bug)

If the pipeline crashes at `write_live_json` with `ValueError: not enough values to unpack`,
diffs and artifacts under `reports/artifacts/` are still valid; only the summary JSON is missing.
Fixed by using `sys.argv[1:19]` in `lib/live_pipeline.sh`.

### 4. “Cloud Success” ≠ tests runnable

`pdd test` reports success when the LLM returns bytes. The demo adds `py_compile` to separate
**generation success** from **runnable tests**.

### 5. High cost and variance

Live mode runs **four** LLM calls (generate×2, test×2). Models and costs differ per step;
before/after pytest comparison is noisy without pinned models or caching.

---

## Implications

| Area | Implication |
|------|-------------|
| **Product story** | Selling “clarify → green tests” on `foo_codegen` oversells; prompt/contract wins are real, pytest wins are not guaranteed. |
| **Metrics** | Report `py_compile_ok`, `pytest.passed`, and byte sizes separately in `live.json`; do not treat lint-only success as full E2E. |
| **CI** | Keep deterministic mode as the merge gate; live mode stays opt-in (`PDD_RUN_REAL_LLM_TESTS=1`). |
| **Test generator** | Harden `pdd/generate_test.py` postprocess (strip orphan `if`, add `src/` to preamble, validate with `ast.parse` before write). |
| **Demo prompt** | `foo_codegen` is tuned for lint/clarify drama, not stable pytest; consider a smaller smoke prompt for behavioral E2E. |
| **Contracts vs behavior** | `coverage --contracts` can look good while pytest never runs — three layers stay independent. |

### Live pass criteria (script)

- ≥1 ambiguity from clarify  
- Prompt warnings do not increase after clarify  
- Non-empty generate and test files (before and after)  
- `pytest_after >= pytest_before` (0→0 counts as “no regression”; both skip counts as pass)  

A run can satisfy clarify criteria yet skip pytest entirely — treat that as **partial E2E**.

---

## Diffs

| File | Compares |
|------|----------|
| `prompt_vague_vs_formalized.diff` | Hand vague → hand formalized (authoring lesson) |
| `prompt_codegen_before_vs_clarified.diff` | Codegen → after `--apply` |
| `prompt_codegen_clarified_vs_formalized.diff` | Clarified → gold formalized |
| `src_before_vs_after.diff` | Implementation delta |
| `tests_before_vs_after.diff` | Test file delta |

---

## Verification layers

| Layer | Tools | Executes code? |
|-------|-------|----------------|
| **Prompt quality** | `pdd prompt lint`, clarify `--apply` | No |
| **Contracts** | `compile`, `coverage --contracts` | No (IR / matrix only) |
| **Formalization** | lint `--report formalization` | No Z3 in this repo |
| **Behavioral** | `pdd test --manual`, `pytest` | Yes — if tests are valid Python |

---

## Commands

```bash
# Deterministic
bash demo.sh

# Live
bash demo.sh --live --keep-artifacts

# Remove ephemeral src/tests/work copy (keeps reports/)
bash demo.sh --cleanup

# CI tests
pytest tests/test_prompt_lint_contract_e2e_demo.py -q
PDD_RUN_REAL_LLM_TESTS=1 pytest tests/test_prompt_lint_contract_e2e_demo.py -q -m real
```

**Manual repair check on saved tests:**

```bash
python3.12 -m py_compile tests/test_foo_work_before.py tests/test_foo_work_after.py
python3.12 -m pytest tests/test_foo_work_after.py -q
```

---

## What this demo does not do

- No deployed HTTP server or real JWT signature verification  
- No `pdd contracts prove` / Z3 execution  
- No `pdd fix` loop after pytest failure  
- No guarantee that generated tests cover every compiled rule (R1–R6)  

---

## See also

- [`docs/prompt_lint.md`](../../docs/prompt_lint.md)  
- [`docs/contract_check.md`](../../docs/contract_check.md)  
- [`docs/coverage_contracts.md`](../../docs/coverage_contracts.md)  
