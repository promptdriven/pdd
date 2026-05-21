# Testing strategy (cost_tracker strict A/B)

This pipeline implements a **valid** evaluation model by separating two questions:

```text
Experiment A: Did contract metadata improve deterministic spec quality?
Experiment B: Did LLM clarify improve downstream generation/test outcomes?
```

Do not collapse those into one “success” number.

## Three layers

| Layer | What runs | CI |
|-------|-----------|-----|
| **1. Unit tests** | `pytest tests/test_cost_tracker_strict_ab.py` (schema, gate, drift) | Merge gate |
| **2. Experiment A** | `bash demo.sh --experiment-a` — spec instrumentation, no LLM | Merge gate |
| **3. Experiment B** | `bash demo.sh --live-ab` — clarify sandwich | Opt-in / nightly |

## Experiment A — spec instrumentation (not clarify A/B)

Compares:

- **A0:** baseline prompt (no `<contract_rules>`)
- **A1:** hand-authored contracts prompt (rules outside `</prompt>`)

Valid for: `pdd gate`, `pdd evidence`, `pdd contracts drift`, compile, coverage.

**Not valid for:** proving `prompt lint --ambiguity` improved the prompt (that is Experiment B).

### A0 gate semantics

If A0 has `rule_count == 0`, gate “pass” only means **nothing to check**, not “source of truth verified.”

## Experiment B — clarify sandwich (live)

```text
copy baseline → work prompt
BEFORE: generate → test → golden pytest → evidence
CLARIFY: lint --ambiguity --apply --contracts
AFTER:  same stack (same generate output path)
```

### Controls

- Same `src/edit_file_tool/cost_tracker_utility.py` for both generates
- Snapshots: `cost_tracker_utility_{before,after}.py`
- Record `PDD_MODEL_DEFAULT` and preflight model in `ab_live.json`
- Diffs written by `scripts/artifacts.sh` (never manual `tee`)

### Metric layers (do not merge)

| Layer | Examples |
|-------|----------|
| **Prompt** | `warn_after <= warn_before`, `rule_count_after > 0`, `compile_errors == 0` |
| **Codegen (primary)** | Shared golden tests vs src snapshots |
| **Codegen (secondary)** | LLM-generated tests, `py_compile`, pytest pass count |
| **Process** | `evidence` validate, `drift` on prompt hash |

**Primary code quality:** `tests/test_cost_tracker_reference.py` run against before/after **src snapshots** via `scripts/run_golden_pytest.py`.

**Secondary:** generated test files (high LLM variance).

“Cloud Success” on `pdd test` is **not** sufficient — bytes returned ≠ valid Python.

### Verdict fields (`reports/ab_live.json`)

| Field | Meaning |
|-------|---------|
| `spec_instrumented` | `rule_count > 0` and `compile_errors == 0` after clarify |
| `prompt_improved` | Warnings flat/down, no formalization rejections, spec instrumented |
| `contract_linkage_improved` | Fewer missing R# markers or more coverage `checked` |
| `behavioral_regression` | Golden or syntax/pytest regression (primary: golden) |
| `behavioral_claim_strength` | Always `single_live_run` — not universal proof |

### What Experiment B can claim

- OK: “No observed behavioral regression in this live run.”
- OK: “Clarify changed the prompt measurably (hash, lint, rules).”
- Not OK: “Clarify universally improves generated code.”

## Confounders this design avoids

| Confounder | Mitigation |
|------------|------------|
| Different output modules | Same canonical generate path |
| Different prompts without labeling | Pre/post snapshots + drift |
| Manual diffs | `artifact_diff` in pipeline |
| Comparing unchecked rules to lint warns | Separate metrics in verdict logic |
| Test-LLM variance for code score | Golden tests on src snapshots |

## Future hardening (optional)

- Repeated live runs + aggregate report
- Mocked clarify fixture for deterministic CI
- Writeback inside `<prompt>` (not after `</prompt>`)
