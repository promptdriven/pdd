# Runbook: Check Paths, AI Budgets, and Step Patterns

> Deep reference for [RUNBOOK.md](../RUNBOOK.md).

## 8. Check paths

The five core check targets are `result`, `error`, `world`, `calls`, and `input` (never `output`—use `result`), plus `html` selector checks on rendered HTML strings.

| Target | JSON Pointer `path` | Notes |
|---|---|---|
| `result` | `/field`, `/items/0/name` | Returned JSON object field. Escape `/` as `~1`, `~` as `~0`. |
| `error` | `/code` (or shorthand `["error", "=", "code"]`) | Step must also set `"expected_error"` (auto-inferred in Short JSON). Ops: `count`, `equals`, `exists`, `not_equals`, `one_of`. |
| `world` | `/kv/tasks/0/done` | Persisted simulated store state after the step. |
| `calls` | `store.save` or `internal:peer` | Call count. Assert `= 0` only when the op contract binds that port; on read-only ops, check unchanged `world` instead. Ops: `count`, `equals`, `not_equals`, `one_of`. |
| `input` | `/field`, `/amount_cents` | Step input object field (useful for `ref_target`/`ref_path` cross-checks and `integer_relation`). |
| `html` | Short JSON tuples: `["html_exists", "button#go"]`, `["html_text", "span#score", "=", "0"]`, `["html_attr", "button#go", "value", "=", "go"]`, `["html", "button", "labels_include", ["Go"]]` | Selector MUST start with a tag name (`button#go`, `span#score`). |

- **All 16 operators:**
  - **14 exact operators:** `equals` (`=`), `not_equals` (`!=`), `not_contains`, `count`, `one_of`, `all_in`, `equals_ignore_case`, `at_least` (`>=`), `at_most` (`<=`), `lt` (`<`), `lte`, `gt` (`>`), `gte`, `integer_relation` (plus HTML `exists`/`html_exists`, and Short JSON `len>=`/`len<=`).
  - **2 supplemental operators** (must pair with at least one exact check on the same criterion): `contains` (and Short JSON `contains_all`), non-HTML `exists`.
  - Cross-target value references support `ref_target`, `ref_path`, and `json_path` where applicable.
- **Exact integer conservation (`integer_relation`):** check exact integer equations or bounds (`"compare": "eq" | "le" | "ge"`) across `result`, `input`, and `world` using `{"criterion_id": "AC2", "target": "result", "path": "", "op": "integer_relation", "value": {"compare": "eq", "left": {"sum": [{"field": "/payout_cents"}, {"field": "/fee_cents"}]}, "right": {"ref_target": "input", "ref_path": "/gross_cents"}}}` (terms: `{"field": "<pointer>"}`, `{"ref_target": "result"|"input"|"world", "ref_path": "<pointer>"}`, `{"integer": "100"}`, `{"sum": [...]}`, `{"product": [...]}`).

## 9. Money and dates

- Represent money as **integer minor units** (e.g. `cents: 1099`), never floats; state rounding rule explicitly in `## Domain decisions` (e.g. half-up or half-to-even).
- Use ISO-8601 strings (`YYYY-MM-DD` or UTC `YYYY-MM-DDTHH:MM:SSZ`) and pass the current clock via an explicit input or `clock.now` port—never depend on wall-clock time.

## 10. AI calls

- Hybrid 1-pass execution runs plain-prose prompts directly without separate lazy-interface startup waits when no explicit interface synthesis is needed, while every step still makes `>= 1` AI call (plus calls for peer prompts or tool loops). Keep scenarios compact: **1 focused step per Story criterion** (`5–8` steps typical, hard cap `15`).
- Omit optional step `"model"` so the runtime uses its fast default model. Override the default call budget only when genuinely needed with `pdd test --max-calls N`.
- Never write exhaustive permutation matrices in PDD scenarios—put exhaustive sweeps in native code tests (§17).

## 18. Patterns: a pure function and a state sequence

- **Pure / independent steps (default — runs in parallel):** declare shared fixtures under top-level `"seeds"` and give each step `"from": "seed_name"` + `"patch": {...}` so steps execute concurrently and isolate failures.
- **`"patch"` vs `"set"` for `null` values:** `"patch"` applies RFC 7396 JSON Merge Patch, so explicit `null` deletes that key from the cloned seed (breaking required nullable fields). Use step-level or `$use`-level `"set": {"/a/b": null}` (RFC 6901 JSON Pointers, applied after `"patch"`) to assign literal `null` or replace array elements.
- **State sequence (persistence criteria only):** chain prior step outputs via `{"$step": "step-id#/field"}` or mutate shared `initial_world` across sequential steps (`<= 10` moves/rows/calls per step; split long replays across steps).
- Never label interactive UI/screen behavior `"browser-only"`—give screens `render({ state }) -> { state, html }` + `handle_event({ state, event }) -> { state, html }` (single-file plain-prose UI) or `render` + compact `app-map.json` (timers/routing/mockups, §13) with exact `result` and `html_*` checks.
