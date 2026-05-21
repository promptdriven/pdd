# Cost tracker strict A/B pipeline

Controlled evaluation of the contract-commands stack on
[`cost_tracker_utility_Python.prompt`](../contract_commands_cost_tracker_e2e_demo/prompts/cost_tracker_utility_Python.prompt).

This demo separates two questions that must not be collapsed into one score:

```text
Experiment A: Did contract metadata improve deterministic spec quality?
Experiment B: Did LLM clarify improve downstream generation/test outcomes?
```

**CI policy:** Experiment A is merge-blocking (no API). Experiment B is opt-in / nightly (`PDD_RUN_REAL_LLM_TESTS=1`).

---

## Testing strategy

### Three layers

| Layer | What runs | CI |
|-------|-----------|-----|
| **1. Unit / integration tests** | `pytest tests/test_cost_tracker_strict_ab.py` | Merge gate |
| **2. Experiment A** | `bash demo.sh --experiment-a` | Merge gate |
| **3. Experiment B** | `bash demo.sh --live-ab` | Opt-in only |

### Experiment A — spec instrumentation (not a clarify A/B)

Compares:

- **A0:** baseline prompt — no `<contract_rules>` (`rule_count == 0`)
- **A1:** hand-authored contracts prompt — rules **outside** `</prompt>`

**Valid for:** `pdd gate`, `pdd evidence emit/validate`, `pdd contracts compile`, `pdd coverage --contracts`, `pdd contracts drift`.

**Not valid for:** proving `pdd prompt lint --ambiguity` improved a prompt (that is Experiment B).

**A0 gate semantics:** If `rule_count == 0`, gate “pass” only means *nothing to check*, not “source of truth verified.”

### Experiment B — clarify sandwich (live, single run)

```text
copy baseline → prompts/cost_tracker_work_python.prompt
BEFORE:  generate → test → golden pytest → evidence
CLARIFY: pdd prompt lint --ambiguity --apply --contracts
AFTER:   same stack (same generate output path)
```

**Controls**

- Same canonical output: `src/edit_file_tool/cost_tracker_utility.py`
- Snapshots: `cost_tracker_utility_{before,after}.py` (under `src/`; gitignored ephemeral)
- Model recorded in `reports/ab_live.json`
- Diffs via `scripts/artifacts.sh` (not manual `tee`)

**Metric layers (do not merge)**

| Layer | Metric | Role |
|-------|--------|------|
| **Prompt** | `warn_after <= warn_before`, `rule_count`, `compile_errors` | Spec structure |
| **Codegen (primary)** | Shared golden tests on src snapshots | Code quality (low variance) |
| **Codegen (secondary)** | LLM-generated tests, `py_compile`, pytest counts | Smoke only (high variance) |
| **Process** | evidence validate, drift | Audit trail |

**Primary code quality:** [`test_cost_tracker_reference.py`](../contract_commands_cost_tracker_e2e_demo/tests/test_cost_tracker_reference.py) via `scripts/run_golden_pytest.py`.

**Verdict fields** (`reports/ab_live.json` — four separate booleans):

| Field | Meaning |
|-------|---------|
| `spec_instrumented` | `rule_count > 0` and `compile_errors == 0` after clarify |
| `prompt_improved` | Warnings flat/down, no formalization rejections, spec instrumented |
| `contract_linkage_improved` | Fewer missing R# markers or more coverage `checked` |
| `behavioral_regression` | Golden or syntax/pytest regression (golden is primary) |
| `behavioral_claim_strength` | Always `single_live_run` |

**What Experiment B can claim**

- OK: “No observed behavioral regression in this live run.”
- OK: “Clarify changed the prompt measurably (hash, rules, vocabulary).”
- OK (with golden pass): “After code satisfied shared contract tests in this run.”
- **Not OK:** “Clarify universally improves generated code.”

**Confounders avoided**

| Confounder | Mitigation |
|------------|------------|
| Different output modules | Same canonical generate path |
| Manual diffs | `scripts/artifacts.sh` |
| Lint warns vs coverage unchecked | Separate metrics (never compare across units) |
| Test-LLM variance | Golden tests on src snapshots |

**Known limitations**

- Clarify may append blocks **after** `</prompt>` (writeback fix pending in product).
- One live run cannot prove general LLM improvement; use repeated runs + pinned model for benchmarks.
- Generated pytest pass count is necessary but not sufficient.

Further methodology: [docs/TESTING_STRATEGY.md](docs/TESTING_STRATEGY.md).

---

## Documented run results (2026-05-21)

Environment: `pdd-cli 0.0.218.dev460`, editable install via repo `.venv`, `PDD_SKIP_UPDATE_CHECK=1`.  
Experiment B generate model: `claude-opus-4-7` (~$0.35 per `pdd generate`).

### Experiment A — deterministic (`bash demo.sh --experiment-a`)

| Arm | Prompt | `rule_count` | Notes |
|-----|--------|--------------|-------|
| A0 baseline | `cost_tracker_utility_Python.prompt` | 0 | Gate pass is vacuous |
| A1 contracts | `cost_tracker_with_contracts_python.prompt` | 3 | Rules outside `</prompt>` |

**Verdict:** `spec_instrumentation_improved: true`, drift detected (expected hash change).

**Conclusion:** Hand-authored contract metadata makes the spec measurable through gate, evidence, compile, and drift. The deterministic contract/evidence pipeline behaves as designed.

### Experiment B — live clarify sandwich (`bash demo.sh --live-ab --keep-artifacts`)

| Metric | Before clarify | After clarify |
|--------|----------------|---------------|
| Lint warnings | 0 | 0 |
| Ambiguities applied | — | 7 |
| Formalization rejections | — | 0 |
| Prompt SHA | `eff38395…` | `cbe3dd9c…` |
| Contract rules | 0 (in prompt) | 5 |
| Compile errors | — | 1 (R1 `NO_OBSERVABLE_OBLIGATION`) |
| Coverage unchecked | 0 | 1 |
| Generated src bytes | 12,931 | 12,153 |
| Generated test pytest | 61 passed | 62 passed |
| `py_compile` | OK | OK |

**Structured verdict** (`ab_live.json` at time of run — golden counts reflected harness bug; see corrected golden below):

| Field | Value |
|-------|-------|
| `spec_instrumented` | false (compile error on R1) |
| `prompt_improved` | false (requires clean compile) |
| `contract_linkage_improved` | false |
| `behavioral_regression` | false |

**Corrected golden pytest** (after fixing `run_golden_pytest.py` to create `src/edit_file_tool/`):

```bash
# From this directory (already in examples/cost_tracker_strict_ab):
../../.venv/bin/python scripts/run_golden_pytest.py \
  src/edit_file_tool/cost_tracker_utility_before.py \
  ../contract_commands_cost_tracker_e2e_demo/tests/test_cost_tracker_reference.py
# golden pytest: FAIL passed=2 failed=1  (test_R2_unknown_model_raises)

../../.venv/bin/python scripts/run_golden_pytest.py \
  src/edit_file_tool/cost_tracker_utility_after.py \
  ../contract_commands_cost_tracker_e2e_demo/tests/test_cost_tracker_reference.py
# golden pytest: PASS passed=3 failed=0
```

**Conclusion for this run**

1. **Prompt layer:** Clarify materially enriched the spec (vocabulary, R1–R5, acceptance tests, formalization). Lint was already clean so `warn_after <= warn_before` is uninformative.
2. **Contract IR:** Not fully clean — one compile error on R1; rules placed after `</prompt>`.
3. **Codegen (primary):** Golden tests improved **before → after** (2/3 → 3/3) on kept snapshots — supports “no regression; possible improvement on shared contract tests” for this single run only.
4. **Codegen (secondary):** LLM-generated tests passed both arms; not used as primary proof.
5. **Process:** Evidence and drift ran; prompt hash change recorded.

Re-run Experiment B updates `reports/` (gitignored); copy key numbers here if you publish a new benchmark.

---

## Prerequisites

```bash
cd /path/to/pdd && pip install -e .
export PDD_SKIP_UPDATE_CHECK=1
```

Experiment B also needs `export PDD_MODEL_DEFAULT=...` or `pdd auth login`.

## Commands

```bash
cd examples/cost_tracker_strict_ab

# Experiment A — deterministic (no LLM)
bash demo.sh --experiment-a

# Experiment B — clarify sandwich (~4 LLM calls + golden tests)
bash demo.sh --live-ab --keep-artifacts

# Golden only (no LLM) on kept snapshots
../../.venv/bin/python scripts/run_golden_pytest.py \
  src/edit_file_tool/cost_tracker_utility_before.py \
  ../contract_commands_cost_tracker_e2e_demo/tests/test_cost_tracker_reference.py
../../.venv/bin/python scripts/run_golden_pytest.py \
  src/edit_file_tool/cost_tracker_utility_after.py \
  ../contract_commands_cost_tracker_e2e_demo/tests/test_cost_tracker_reference.py

# Cleanup ephemeral files (keeps reports/)
bash demo.sh --cleanup

# CI
pytest ../../tests/test_cost_tracker_strict_ab.py -q
PDD_RUN_REAL_LLM_TESTS=1 pytest ../../tests/test_cost_tracker_strict_ab.py -q -m real
```

Prefer repo `.venv` when conda `pdd-cli` lacks editable `pdd`:

```bash
/path/to/pdd/.venv/bin/bash demo.sh --live-ab --keep-artifacts
```

## Layout

| Path | Purpose |
|------|---------|
| `demo.sh` | Entry: `--experiment-a`, `--live-ab`, `--cleanup` |
| `scripts/run_experiment_a.py` | Experiment A driver |
| `scripts/live_ab_pipeline.sh` | Experiment B driver |
| `scripts/run_golden_pytest.py` | Primary codegen metric (shared golden tests) |
| `scripts/write_ab_report.py` | Builds `reports/ab_live.json` |
| `scripts/artifacts.sh` | Snapshot + diff helpers |
| `reports/` | Generated JSON/diffs (gitignored) |

## Shared assets

Prompts, stories, and golden tests:
[`../contract_commands_cost_tracker_e2e_demo/`](../contract_commands_cost_tracker_e2e_demo/)
