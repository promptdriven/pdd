# Runbook: Check Paths, AI Budgets, and Step Patterns

> Part of [RUNBOOK.md](../RUNBOOK.md) — see the router table in `../RUNBOOK.md` for other `§N` sections.

## 8. Check paths

| `target` | `path` | Real example |
|---|---|---|
| `result` | a JSON pointer into the answer | `/quote/totalCents` equals 3784 |
| `error` | `/code` | equals `"unknown-coupon"` |
| `world` | a JSON pointer into the saved data after the step (section 5) | `/stamps/sam` equals 11 |
| `calls` | `/resources/<node>-<resource>-<operation>`: uses of that resource operation in this step | `/resources/todo-store-save` equals 0 |
| `calls` | `/internal/<node>`: calls to that prompt in this step | `/internal/pricing` equals 1 |

**Check operations (`op`):**

| `op` | Allowed `target` | Required fields & meaning | Counts as exact coverage? |
|---|---|---|---|
| `equals` | `result`, `world`, `calls`, `error` | `"value"`: exact JSON match | Yes |
| `not_equals` | `result`, `world`, `calls`, `error` | `"value"`: value is present and not equal to `"value"` | Yes |
| `one_of` | `result`, `world`, `calls`, `error` | `"value"`: nonempty list of at most 32 distinct JSON scalars (`null`, string, boolean, int or finite float) | Yes |
| `count` | `result`, `world`, `calls`, `error` | `"value"`: nonnegative integer length of string, array or object (on `calls`, `/internal` or `/resources` counts distinct targets) | Yes |
| `at_least`, `at_most` | `result`, `world` | `"measure": "value"` with a finite number `"value"`, or `"measure": "length"` with a nonnegative integer `"value"` (string code points, array items or object keys) | Yes |
| `not_contains` | `result`, `world` | `"value"`: nonempty string that does not appear in the target string (no `"measure"`) | Yes |
| `all_in` | `result`, `world` | `"value"`: nonempty list of at most 32 distinct JSON scalars; every item of the target array must match one (empty array passes; no `"measure"`) | Yes |
| `equals_ignore_case` | `result`, `world` | `"value"`: string compared with Unicode case folding without trimming (no `"measure"`) | Yes |
| `exists` | `result`, `world`, `calls`, `error` | Optional boolean `"value"` (default `true`) | Only with `"html"` (section 20) |
| `contains` | `result`, `world` | `"value"`: nonempty substring in the target string | No (supplemental only) |

Example bounded length check (`at_most`) and set check (`all_in`), plus optional `"json_path"` (an RFC 6901 pointer into a JSON-text string at `"path"` on `result` or `world`):
```json
{"criterion_id": "AC1", "target": "result", "path": "/title", "op": "at_most", "measure": "length", "value": 20}
{"criterion_id": "AC2", "target": "result", "path": "/score", "op": "at_least", "measure": "value", "value": 10}
{"criterion_id": "AC3", "target": "result", "path": "/tags", "op": "all_in", "value": ["alpha", "beta", "gamma"]}
```

A **node** is one prompt operation in the program of the step. Its name is the prompt file name without `.prompt.md`
(`todo`, `pricing`, `orders_api`). But when the step reaches 2 or more operations of one prompt, each of them is the
node `<file>--op-<operation>--hex-<operation name in hex>`. `printf add | xxd -p` gives the hex: `616464`.
- Calls belong to the whole prompt: each operation reaches every target in its prompt's `calls`. Example: `app` calls
  `store` for `add` and for `list`, so every step on `app` reaches both. The save count under `add` is then
  `/resources/store--op-add--hex-616464-store-save`. `/resources/store-store-save` does not exist there.
  `/internal/store--op-add--hex-616464` counts the calls of `add`.
- Two prompt files with the same file name get other node names. Give each prompt its own file name.
- `got {"missing": true}` means that the path names no node. The path is wrong, not the prompt: fix only the path.
  For the `error` target, pdd prints `got no error (a normal result)` when the step returned a result and no error.
  Then the path is right, and the prompt did not refuse this input. If pdd still prints `got {"missing": true}` on
  `error`, an error came back without that field: compare the path with the prompt's declared errors.
  A declared operation that the step did not use counts `0`. pdd does not check paths before it sends, so work out
  each path with these rules before the first check.

**Check operations (`op`).** Exact checks satisfy criterion coverage; `exists` (without `html`) and `contains` are partial checks and must be paired with an exact check on the criterion.

| `op` | Meaning | Example fields |
|---|---|---|
| `equals`, `not_equals` | Exact JSON value match or inequality | `"value": 3784` |
| `one_of` | Actual value matches any listed candidate | `"value": ["pending", "queued"]` |
| `count` | Length of an array | `"value": 4` |
| `at_least` / `gte`, `at_most` / `lte`, `lt`, `gt` | Numeric or length bound (`"measure": "value"` default, or `"measure": "length"` for string code points or array items) | `"op": "at_most", "value": 500` |
| `not_contains`, `all_in`, `equals_ignore_case` | Substring/item exclusion, array subset check, or case-insensitive ASCII string match | `"op": "all_in", "value": ["read", "write"]` |
| `exists`, `contains` | Presence or substring/item containment (add `"html"` on `exists` for exact HTML selector checks) | `"op": "contains", "value": "Order #"` |

**Cross-path relational checks.** For `equals`, `not_equals`, `at_least` / `gte`, `at_most` / `lte`, `lt`, and `gt` on `result`, `world`, or `calls`, compare against another live field from `"result"`, `"input"`, or `"world"` instead of a literal `value` (or pass `{"ref_target", "ref_path"}` as `"value"`):
```json
{"criterion_id": "AC1", "target": "result", "path": "/fee_cents", "op": "at_most", "ref_target": "input", "ref_path": "/cap_cents"}
```
Add `"ref_json_path"` when the referenced field is a JSON-encoded string, and `"measure": "length"` when comparing string or array lengths across paths.

**Exact integer conservation (`integer_relation`).** Check exact integer equations or bounds (`"compare": "eq" | "le" | "ge"`) across `result`, `input`, and `world` without hardcoding components:
```json
{"criterion_id": "AC2", "target": "result", "path": "", "op": "integer_relation",
 "value": {"compare": "eq", "left": {"sum": [{"field": "/payout_cents"}, {"field": "/fee_cents"}]},
           "right": {"ref_target": "input", "ref_path": "/gross_cents"}}}
```
Terms use `{"field": "<pointer>"}` (relative to the check's `target`/`path`), `{"ref_target": "result" | "input" | "world", "ref_path": "<pointer>"}`, `{"integer": "100"}` (base-10 string), `{"sum": [...]}`, or `{"product": [...]}`.

## 9. Money and dates

- Do all money math in whole cents. Write the rounding rule in the prose, with an example:
  "Round half a cent up (215.5 becomes 216)." If the app shows dollars, check dollars: `/total` equals 10.65.
- Give a rate as a decimal string, not a number: `"taxRatePercent": "8.875"`.
- Give a date as a `YYYY-MM-DD` string with a `pattern`. Write the calendar rules in the prose
  ("closed every Monday", "a real calendar date"). Use real dates in the story: "Monday 2026-11-02", "2026-02-30".
- A `compute` resource does exact decimal and date math. Whole cents and a written rule were exact for a 14-item bill,
  so use `compute` only when a check shows a math error.

## 10. AI calls

- A step costs 1 AI call when the prompt only answers, 2 to 3 when it uses saved data or calls another prompt, and up
  to 4 when it calls a prompt that uses saved data. A 3-step Harbor test used 9. A 9-step test (`app` calls `store`) used 34.
- `pdd test` gives each test 12 calls for each step, at least 18 and at most 1000. Override it with `--max-calls N` from 1 through 1000, the interpreter maximum.
- For a failed check, the runtime can automatically run each of at most 3 failed steps up to 2 more times to diagnose stability: at most 6 additional AI calls, within the original `--max-calls` ceiling.
- **Choose a ceiling of at least 3 times your worst-case estimate** when setting `--max-calls` for a check or a simulation. Include child calls, saved-data operations, redraws, all the moves you plan to try and, for a check, the automatic rerun allowance above. The budget is a ceiling, not a charge: you are charged only for calls that run. If the estimate does not fit the server maximum, report that limit; do not silently reduce the margin or change expected values.
- A new `pdd simulate` requests a session budget of 400 calls. `pdd simulate STORY --max-calls 600` chooses a different ceiling when starting a new simulation. The CLI cannot raise an existing simulation’s ceiling; `--new` starts fresh saved data. The output shows the interpreter-confirmed total and remaining calls. Reusing a simulation without this option keeps its current budget.
- Too few calls left gives the refusal `repository-graph-catalog-error`. It is not a prompt error. The interface `limits` do not set this budget.
- **Worst case of a step:** 1, plus for each entry in its prompt's `calls`: `max_calls` × (worst case of the called
  prompt + 1). Calls belong to the whole prompt (section 8), so every operation of the prompt has this worst case.
  `checkout` → `pricing` with `max_calls: 1`: 1 + 1 × 2 = 3. `game` → `board` with `max_calls: 30`: 1 + 30 × 2 = 61.
  When one step's worst case is bigger than `--max-calls` (at most 1000), the interpreter refuses the whole test before it
  starts: `run-admission-failed`, 0 AI calls. So keep `max_calls` small (section 18).
- **The Simulator allows 40 AI calls for each tap.** A screen or key whose prompt's worst case is over 40 never
  opens: refused at 0 calls. A screen prompt that calls another prompt with a high `max_calls` hits this fast
  (`game` → `board` with `max_calls: 30` is 61 per tap). Keep the screen prompt's chain small: one call with a whole
  list (section 18), not many calls.
- **Check small first.** A schema refusal costs 0 AI calls. A wrong check path costs the full run: one cost 34 calls.
  - In a new project, check the story with the fewest steps first. Check the others only after it passes.
  - Start a new test with few steps: often one step for each criterion is enough. Add more cases after it passes.
  - After a failure, check only that story again (`pdd test <story>`), not all stories.
  - Before a check of more than 5 steps, tell the person the likely cost: about 4 AI calls for each step.

## 18. Patterns: a pure function and a state sequence

Test only the real operations of the program: functions, commands or routes that the code will have. Never add an
operation only for a check (for example `moveWithInputObservation`, `sequence` or `replay`). The interpreter sees results,
saved data and call counts. It cannot see CSS layout, sizes, animation or whether an input object changed.
A page or a screen is never "browser-only": what it shows and what each tap does are results. Give it an app map
(section 13). A page with no mockup gets a `render` operation that returns `{"html": …}` plus the facts it shows,
for example `{"html": "…", "emptyMessage": "No books yet", "rows": 3}`. Check the facts with `equals` or `count`
on those fields (`/emptyMessage`); use structured HTML checks for markup (section 20). For dense boards, grids, or large tables (such as a 20×20 game grid), keep simulated `render` HTML compact (summary markup and key controls) and check structured state fields (`score`, positions, counts, status) in `pdd test` instead of emitting hundreds of repeated HTML cell tags; verify full multi-hundred-cell DOM or canvas grids with `pdd test --screen URL --drawing SVG` or native browser tests in code space. Only what the interpreter truly cannot see (CSS layout, sizes,
animation) goes in a story with no PDD test (pdd only warns "has no test"), proved with the repo's tests in PR 2.
Keep the prompt short (500 prose lines or fewer excluding its Runtime interface block; `pdd lint` warns above 500 lines and gives elevated decomposition advice above 1,000 lines). A `calls` entry is enough: do not copy the called prompt's schemas. Put a big table or list in a
repo file and link it under `## Dependencies`. Test data goes in the test (`input`, `initial_world`), not in the prompt. Keep each Story scenario JSON focused on policy and authority boundaries (15 steps or fewer and 1,000 lines or fewer), and prove multi-step state-machine or wire-protocol sequences with native tests (section 17).

**A pure function:** one operation, input → result, no saved data, no `calls`. Each step costs 1 AI call.
`initial_world` and `simulation` are `{}`. One step for the 2048 `board` prompt:
```json
{"step_id": "merge-row-left", "entry_path": "prompts/board.prompt.md", "operation": "move",
 "input": {"board": [[2,2,2,2],[0,0,0,0],[0,0,0,0],[0,0,0,0]], "dir": "left"},
 "checks": [{"criterion_id": "AC1", "target": "result", "path": "/board/0", "op": "equals", "value": [4,4,0,0]},
            {"criterion_id": "AC1", "target": "result", "path": "/gained", "op": "equals", "value": 8}]}
```

**A state sequence** (N moves in a row): one test step for each move. Steps run in order. Use one of these ways:
- The app saves its state: declare a resource (section 5). `initial_world` holds the start, for example
  `{"kv": {"game": {"board": […], "score": 0}}}`. Each step makes one move. `world` checks read the state after it.
  Each step costs 2 to 3 AI calls.
- The state goes in and comes out (`step(state, dir)` returns the new state): give each step the result of the step
  before it. `"input": {"state": {"$step_result": {"step_id": "move-1", "path": ""}}, "dir": "up"}`. The path `""` is
  the whole result. Put the reference inside `input`, not as all of `input`. It cannot name an error step. 1 AI call for each step.
- If the app really accepts a list of moves, use short lists of about 10 per step. Check the expected state after
  each part and pass it to the next part; keep the same complete replay coverage. Link its rule prompt under
  `## Dependencies`. Do not invent a replay operation only for tests, or expand a short action into an unbounded
  chain of prompt calls. The server stops one step after 10 minutes, regardless of the remaining call budget.
