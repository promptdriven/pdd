# Benchmark tasks (v0)

## `email_validator`

**Intent:** Small deterministic module with a real reference implementation and pytest suite.

| Arm | Artifact |
|-----|----------|
| A0 | `prompts/adhoc.prompt` — prose only |
| A1 | `prompts/formalized.prompt` — R1–R6 + `<coverage>` |
| A2 | `baseline/src/email_validator.py` + `baseline/tests/` |

**Expected v0 signals:**

- A0: higher `prompt_lint_warnings`, no `total_rules` (or zero contract rules)
- A1: non-zero `checked_rules`; `formal_candidate_rules` ≥ 4; `z3_test_count` ≥ 3;
  `test_pass_rate` ≈ 1.0 (unit + Z3 tests)
- A2: `test_pass_rate` ≈ 1.0; all prompt/contract metrics `null`

## `refund_payment`

**Intent:** Exercise contract coverage + story linking without a full generated service.

| Arm | Artifact |
|-----|----------|
| A0 | `prompts/adhoc.prompt` |
| A1 | `prompts/formalized.prompt` (from `tests/fixtures/coverage_contracts/`) + `stories/` + `tests/` |
| A2 | No implementation in v0 (`test_paths: []`) |

**Expected v0 signals:**

- A0: no `<contract_rules>` → coverage totals zero; lint may still run on prose
- A1: `total_rules` = 6; mix of `checked`, `story-only`, `waived` per fixture design
- A2: `test_pass_rate` null with note (no code baseline yet)

## `payment_api_lint` (v1)

**Intent:** Show lint improvement when vocabulary fully defines vague terms.

| Arm | Artifact |
|-----|----------|
| A0 | `prompts/vague.prompt` — partial vocabulary (expects lint warnings) |
| A1 | `prompts/formalized.prompt` — full vocabulary (expects fewer warnings) |

**Expected:** A1 `prompt_lint_warnings` < A0; both have 5 contract rules.

## Adding a task

1. Create `tasks/<task_id>/task.yaml` (see existing tasks).
2. Add `prompts/adhoc.prompt` and `prompts/formalized.prompt`.
3. Optionally add `stories/`, `tests/`, `baseline/` for A1/A2.
4. Run `python benchmarks/formalization/run_benchmark.py --tasks <task_id>`.
