# Runbook: Check Paths, AI Budgets, and Step Patterns

> Deep reference for [RUNBOOK.md](../RUNBOOK.md).

## 8. Check paths

| Target | JSON Pointer `path` | Notes |
|---|---|---|
| `result` | `/field`, `/items/0/name` | Returned JSON object field. Escape `/` as `~1`, `~` as `~0`. |
| `error` | `/code` (or shorthand `["error", "=", "code"]`) | Step must also set `"expected_error"` (auto-inferred in Short JSON). |
| `world` | `/kv/tasks/0/done` | Persisted simulated store state after the step. |
| `calls` | `store.save` or `internal:peer` | Call count. Assert `= 0` only when the op contract binds that port; on read-only ops, check unchanged `world` instead. |
| `html` | Selector + `exists` / `text` / `attr` / `labels_include` | Selector MUST start with a tag name (`button#go`, `span#score`). |

- **Operators:** exact (`equals`/`=`, `not_equals`/`!=`, `at_least`/`>=`, `at_most`/`<=`, `len>=`, `len<=`, `one_of`, `count`, `not_contains`, `all_in`, `equals_ignore_case`, `html_exists`) and supplemental (`contains`, `contains_all`—always pair with at least one exact check on the same criterion).
- **Exact integer conservation (`integer_relation`):** check exact integer equations or bounds (`"compare": "eq" | "le" | "ge"`) across `result`, `input`, and `world` using `{"criterion_id": "AC2", "target": "result", "path": "", "op": "integer_relation", "value": {"compare": "eq", "left": {"sum": [{"field": "/payout_cents"}, {"field": "/fee_cents"}]}, "right": {"ref_target": "input", "ref_path": "/gross_cents"}}}` (terms: `{"field": "<pointer>"}`, `{"ref_target": "result"|"input"|"world", "ref_path": "<pointer>"}`, `{"integer": "100"}`, `{"sum": [...]}`, `{"product": [...]}`).

## 9. Money and dates

- Represent money as **integer minor units** (e.g. `cents: 1099`), never floats; state rounding rule explicitly in `## Domain decisions` (e.g. half-up or half-to-even).
- Use ISO-8601 strings (`YYYY-MM-DD` or UTC `YYYY-MM-DDTHH:MM:SSZ`) and pass the current clock via an explicit input or `clock.now` port—never depend on wall-clock time.

## 10. AI calls

- Every step makes `>= 1` AI call (plus calls for peer prompts or tool loops). Keep scenarios compact: **1 focused step per Story criterion** (`5–8` steps typical, hard cap `15`).
- Omit optional step `"model"` so the runtime uses its fast default model. Override the default call budget only when genuinely needed with `pdd test --max-calls N`.
- Never write exhaustive permutation matrices in PDD scenarios—put exhaustive sweeps in native code tests (§17).

## 18. Patterns: a pure function and a state sequence

- **Pure / independent steps (default — runs in parallel):** declare shared fixtures under top-level `"seeds"` and give each step `"from": "seed_name"` + `"patch": {...}` so steps execute concurrently and isolate failures.
- **State sequence (persistence criteria only):** chain prior step outputs via `{"$step": "step-id#/field"}` or mutate shared `initial_world` across sequential steps (`<= 10` moves/rows/calls per step; split long replays across steps).
- Never label interactive UI/screen behavior `"browser-only"`—give screens a `render` operation returning `{"html": string}` and an `app-map.json` (§13) with exact checks.
