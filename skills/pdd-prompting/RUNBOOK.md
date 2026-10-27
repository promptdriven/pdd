# PDD runtime runbook

## 1. What the runtime is

The runtime runs a prompt as a program. There is no code: an AI reads the `*.prompt.md` file and acts as the program.
The runtime checks the **prompt**, not the code. The repo's own tests check the code.
You need a GitHub login (`gh auth status`). A check sends every file that Git shows (max 10 MiB and 10,000 files).
`pdd check --files` lists them. Never put secrets in the repo.

The order of work: story → prompt (`"status": "draft"`) → test → `pdd check --fill-hash` → `pdd check <story>` →
offer `pdd try <story>` → the person tries it and approves → PR 1 with the one-line result (section 15).
Read section 3 (schema rules) and section 8 (check paths) before the first check. Most failed first checks start there.

## 2. The files

| File | What it holds |
|---|---|
| `prompts/<job>.prompt.md` | The program in plain English, then `## Dependencies`, then one Runtime interface block. |
| `user_stories/<story>.md` | One story with a numbered `## Acceptance criteria` list. pdd skips index files: `PLAN.md`, `README.md` and any file with no `## Acceptance criteria` heading. |
| `tests/<story>.json` | The test for that story. pdd finds tests in any folder. If the repo's own tests are in `tests/` or `test/`, use `tests/runtime/` or `test/runtime/`. |

**1 story = 1 test file = many cases.** Each case is one step. Steps run in order and share the saved data.
Across its steps, the test file must check every criterion of its story.
Add a second file only for a case that needs a different starting world. That file also checks every criterion.

**One rule, one prompt.** Before you write a prompt, look in `prompts/` for a prompt that owns the rule. Change that
prompt. Two prompts must never state the same rule. A command-line program has one program prompt (section 6).
A helper module can have its own prompt. Then the program prompt calls it (section 7) and does not repeat its rules.

**The prompt** ends with `<details><summary>Runtime interface</summary>`, a ```` ```json ```` block and `</details>`.
The block of Harbor Coffee's `place_order` (schemas cut):
```json
{"status": "draft", "prose_sha256": "",
 "entries": [{"operation": "place_order", "input_schema": {...}, "result_schema": {...}, "errors": ["unknown-item"]}],
 "calls": [], "resources": [], "limits": {"max_steps": 4, "max_model_calls": 2}, "conventions": []}
```
- Every schema follows section 3. List every error that the prose can return in `errors`.
- Do not write `prose_sha256`: `pdd check --fill-hash` fills it.
- To approve a prompt, the person runs `pdd approve <path>` (agents never set approved). It shows the interface in
  plain words and asks y/n. An approved story at a workflow gate is not an approved prompt.
- To change an approved prompt (prose or interface), set `"status": "draft"`, run `pdd check --fill-hash` and ask the
  person to run `pdd approve <path>` again.

**The story** has one line for each criterion. Number from 1. Use straight quotes (`"`), not curly quotes. Text copied
from a GitHub issue often has curly quotes. Put real values in the text: "$10.65", "2026-11-02". Write what a user
types and sees, as AC1 below does. Do not name code ("`splitBill(2, 4)` returns …"): the person must read and approve it.

**The test** copies every criterion into `criteria`, word for word. From `todo-cli` (some checks cut):
```json
{"schema_version": "prompt-runtime.program-scenario.v1", "story_path": "user_stories/finish-task.md",
 "criteria": [{"id": "AC1", "text": "`todo done 4` prints \"Done #4: Call mom\", exits with code 0 and saves task #4 as done."},
              {"id": "AC2", "text": "Task #1 stays not done."},
              {"id": "AC3", "text": "`todo done 9` prints \"todo: no task #9\" to stderr, exits with code 1 and saves nothing."}],
 "initial_world": {"kv": {"todos": [{"id": 1, "text": "Buy milk", "done": false}, {"id": 4, "text": "Call mom", "done": false}]}},
 "simulation": {"store.load": {...}, "store.save": {...}}, "context": [],
 "steps": [
  {"step_id": "finish-task-4", "entry_path": "prompts/todo.prompt.md", "operation": "main", "input": {"argv": ["done", "4"]},
   "checks": [{"criterion_id": "AC1", "target": "result", "path": "/stdout", "op": "equals", "value": "Done #4: Call mom\n"},
              {"criterion_id": "AC1", "target": "world", "path": "/kv/todos/1/done", "op": "equals", "value": true},
              {"criterion_id": "AC2", "target": "world", "path": "/kv/todos/0/done", "op": "equals", "value": false}]},
  {"step_id": "finish-missing-task-9", "entry_path": "prompts/todo.prompt.md", "operation": "main", "input": {"argv": ["done", "9"]},
   "checks": [{"criterion_id": "AC3", "target": "result", "path": "/stderr", "op": "equals", "value": "todo: no task #9\n"},
              {"criterion_id": "AC3", "target": "calls", "path": "/resources/todo-store-save", "op": "equals", "value": 0}]}]}
```
- Each criterion needs at least one exact check: `equals`, `not_equals`, `one_of` or `count`. Paths: section 8.
- The `input` must match the `input_schema`. An error step has `"expected_error": "unknown-sku"` and a check on `error` `/code`.
- Check facts, not values that the AI picks freely (wording that the story does not fix, generated IDs).
- `context` is almost always `[]`. It gives one prompt extra text files to read, in this test only. A file linked in a
  prompt's `## Dependencies` already goes with that prompt to every run, so link shared data there. Each row is exactly
  `{"prompt_path": …, "paths": […]}`: a prompt of the repo, and at most 16 UTF-8 text files of the repo (120 KiB in all):
  `"context": [{"prompt_path": "prompts/ui.prompt.md", "paths": ["docs/tile-colors.md"]}]`. A text note, a missing key
  or an extra key gives `invalid-context` at `context[N]`. Never give the story, a test or expected values as context:
  the program would see the answers. Patterns for tests: section 18.

## 3. Schema rules

These rules apply to every `input_schema` and `result_schema`, to each resource `arguments_schema` and `result_schema`,
and to an app map's `state_schema`. Today the runtime reports only one broken rule at a time, often with `"path": null`
and no field name. So check every schema against ALL the rules before the first `pdd check`.

1. The top of each schema is `"type": "object"`.
2. Every object has `properties`, `required` and `"additionalProperties": false`. With no fields: `"properties": {}, "required": []`.
3. `required` lists only names from `properties`, each name one time. A field that is not in `required` is optional.
4. `type` is one string: `object`, `array`, `string`, `integer`, `number`, `boolean` or `null`.
   A list such as `["string", "null"]` is refused (`graph-schema-type-list`).
5. For "a string or null", write `{"oneOf": [{"type": "string"}, {"type": "null"}]}`. Each choice is a full schema.
   Put no other keyword next to `oneOf`, except `title` or `description`.
6. Every array has `items`, and `items` is a full schema.
7. Use only these keywords. string: `minLength`, `maxLength`, `pattern`. integer and number: `minimum`, `maximum`,
   `exclusiveMinimum`, `exclusiveMaximum`, `multipleOf`. array: `items`, `minItems`, `maxItems`, `uniqueItems`.
   object: `properties`, `required`, `additionalProperties`, `minProperties`, `maxProperties`. All types: `enum`,
   `const`, `title`, `description`, `default`, `examples`, `format`. All others are refused: `$ref`, `$defs`, `anyOf`, `if` …
8. Each `enum` value has the right type and comes one time. A `default` must match its own schema.

For an optional input field, leave it out of `required`. Do not use `oneOf` with `null` for it: the Try form shows
`oneOf` only as a raw JSON box, and pdd cannot check that input before it sends. A correct schema (`read` is optional):
```json
{"type": "object", "properties": {"title": {"type": "string", "minLength": 1}, "read": {"type": "boolean"},
   "tags": {"type": "array", "items": {"type": "string"}}, "note": {"oneOf": [{"type": "string"}, {"type": "null"}]}},
 "required": ["title", "tags", "note"], "additionalProperties": false}
```

## 4. Expected values

- Expected values come from the story and the person. Never take them from a run, a Try or the code.
- If the story allows two answers, ask the person. Example: "every 10th coffee free" gives $4.95 off, but
  "the price of its cheapest drink" gives $2.75 off. Do not choose yourself.
- Never change a test to make it pass. Fix the prompt. If you think an expected value is wrong, tell the person.

## 5. Saved data

Declare the data as a resource in the interface. The prose names each operation: "Read the tasks once with
`store.load` and the key `todos`." This is the full `todo-cli` resource. `TASKS` is the list schema of the first
line: write it out in full in all 3 places (`$ref` is not allowed). A missing key reads as `null`, so `load` uses `oneOf`.
```json
TASKS = {"type": "array", "items": {"type": "object", "properties": {"id": {"type": "integer", "minimum": 1},
         "text": {"type": "string"}, "done": {"type": "boolean"}}, "required": ["id", "text", "done"], "additionalProperties": false}}
"resources": [{"name": "store", "kind": "key-value", "access": "write", "operations": [
  {"name": "load", "access": "read",
   "arguments_schema": {"type": "object", "properties": {"key": {"type": "string", "enum": ["todos"]}}, "required": ["key"], "additionalProperties": false},
   "result_schema": {"type": "object", "properties": {"value": {"oneOf": [{"type": "null"}, TASKS]}}, "required": ["value"], "additionalProperties": false}},
  {"name": "save", "access": "write",
   "arguments_schema": {"type": "object", "properties": {"key": {"type": "string", "enum": ["todos"]}, "value": TASKS}, "required": ["key", "value"], "additionalProperties": false},
   "result_schema": {"type": "object", "properties": {"value": TASKS}, "required": ["value"], "additionalProperties": false}}]}]
```
In the test, `initial_world` is the saved data before step 1. `simulation` connects each operation to the world:
```json
"initial_world": {"kv": {"todos": [{"id": 3, "text": "Buy milk", "done": true}]}},
"simulation": {"store.load": {"action": "key-value.get", "world_pointer": "/kv", "key_argument_pointer": "/key",
  "value_argument_pointer": null, "item_key_pointer": null, "item_value_pointer": null,
  "result_template": {"value": null}, "result_value_pointer": "/value"}, "store.save": {...}}
```
- `store.save` is the same, with `"action": "key-value.put"`, `"value_argument_pointer": "/value"` and `"result_template": {"value": []}`.
- Say in the prose what `null` means ("no tasks yet"). Keys must be non-empty strings.
- **World paths.** A `world` check reads the world after the step. It starts as `initial_world`. A key-value entry is
  at `<world_pointer>/<key>`: `/kv/todos/1/done` (todo), `/stamps/sam` (Harbor). `port.write` adds its arguments at the
  end of the list at `world_pointer`: `/savedOrders/0/total` (Harbor). For the length of a list: `/kv/books` `count` 4.
- Check "saves nothing" with a `calls` count of 0 (section 8).
- Other actions: `collection.get`, `collection.get-or-null`, `collection.merge` (the world is a list of records),
  `port.write`, `blob.read`, `blob.write`, `blob.stat`, `sql.execute`, `fixture.lookup` and `compute`.
- `port.write` returns its fixed `result_template`. In Harbor, every saved order got the ID 101. Do not check such IDs.

## 6. Command-line programs (`cli`)

Mark both schemas with the `cli` convention. `argv` goes in. `exit_code`, `stdout` and `stderr` come out. In full:
```json
"input_schema": {"type": "object", "properties": {"argv": {"type": "array", "items": {"type": "string"}}}, "required": ["argv"], "additionalProperties": false},
"result_schema": {"type": "object", "properties": {"exit_code": {"type": "integer"}, "stdout": {"type": "string"}, "stderr": {"type": "string"}},
                  "required": ["exit_code", "stdout", "stderr"], "additionalProperties": false},
"conventions": [{"path": "/entries/0/input_schema", "convention": "cli"}, {"path": "/entries/0/result_schema", "convention": "cli"}]
```
- Input: one item for each word, as a shell splits them. `todo add Walk the dog` is `{"argv": ["add", "Walk", "the", "dog"]}`.
- Write the rule "Every line written to `stdout` or `stderr` ends with one newline." in the prose.
  Expected text includes the last newline: `"Added #4: Walk the dog\n"`. An empty stream is `""`.

## 7. A prompt that calls another prompt

`checkout` asks `pricing` for a quote. The caller's interface has a `calls` entry:
```json
"calls": [{"operation": "quote", "target": "prompts/pricing.prompt.md", "target_operation": "quote", "max_calls": 1}]
```
- Link it in `## Dependencies`: ``- [Pricing](pricing.prompt.md), runtime use for operation `quote`.``
- Say in the prose how many times to call: "Call `pricing` operation `quote` exactly once."
  More calls than `max_calls` refuse the check (`graph-result-failure`).
- To pass an error back, list it in the caller's own `errors`, and say it in the prose:
  "If `pricing` returns the error `unknown-coupon`, return the error `unknown-coupon`."
- Check the count: `/internal/pricing` equals 1. For an unknown product, it equals 0 (section 8).

## 8. Check paths

| `target` | `path` | Real example |
|---|---|---|
| `result` | a JSON pointer into the answer | `/quote/totalCents` equals 3784 |
| `error` | `/code` | equals `"unknown-coupon"` |
| `world` | a JSON pointer into the saved data after the step (section 5) | `/stamps/sam` equals 11 |
| `calls` | `/resources/<node>-<resource>-<operation>`: uses of that resource operation in this step | `/resources/todo-store-save` equals 0 |
| `calls` | `/internal/<node>`: calls to that prompt in this step | `/internal/pricing` equals 1 |

A **node** is one prompt operation in the program of the step. Its name is the prompt file name without `.prompt.md`
(`todo`, `pricing`, `orders_api`). But when the step reaches 2 or more operations of one prompt, each of them is the
node `<file>--op-<operation>--hex-<operation name in hex>`. `printf add | xxd -p` gives the hex: `616464`.
- Calls belong to the whole prompt: each operation reaches every target in its prompt's `calls`. Example: `app` calls
  `store` for `add` and for `list`, so every step on `app` reaches both. The save count under `add` is then
  `/resources/store--op-add--hex-616464-store-save`. `/resources/store-store-save` does not exist there.
  `/internal/store--op-add--hex-616464` counts the calls of `add`.
- Two prompt files with the same file name get other node names. Give each prompt its own file name.
- `got {"missing": true}` means that the path names no node. The path is wrong, not the prompt: fix only the path.
  A declared operation that the step did not use counts `0`. pdd does not check paths before it sends, so work out
  each path with these rules before the first check.

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
- `pdd check` gives each test 4 calls for each step, at least 6 and at most 100. To give more, use `--max-calls N`.
- Too few calls left gives the refusal `repository-graph-catalog-error`. It is not a prompt error. The interface `limits` do not set this budget.
- **Worst case of a step:** 1, plus for each entry in its prompt's `calls`: `max_calls` × (worst case of the called
  prompt + 1). Calls belong to the whole prompt (section 8), so every operation of the prompt has this worst case.
  `checkout` → `pricing` with `max_calls: 1`: 1 + 1 × 2 = 3. `game` → `board` with `max_calls: 30`: 1 + 30 × 2 = 61.
  When one step's worst case is bigger than `--max-calls` (at most 100), the runtime refuses the whole test before it
  starts: `run-admission-failed`, 0 AI calls. So keep `max_calls` small (section 18).
- **Check small first.** A schema refusal costs 0 AI calls. A wrong check path costs the full run: one cost 34 calls.
  - In a new project, check the story with the fewest steps first. Check the others only after it passes.
  - Start a new test with few steps: often one step for each criterion is enough. Add more cases after it passes.
  - After a failure, check only that story again (`pdd check <story>`), not all stories.
  - Before a check of more than 5 steps, tell the person the likely cost: about 4 AI calls for each step.

## 11. `pdd check`

`pdd check --fill-hash` fills the hash of draft prompts. `pdd check` checks every test at the same time.
`pdd check place-order` checks one story. `pdd check --read` reads the last results again. `--fill-hash` and `--read` send nothing.
Before you send a check, run `pdd check --lint` to find format problems (0 AI calls). Never import pdd's source.
`pdd check --lint [STORY…]` sends the files to the server's lint only. It makes no AI call, and it prints every problem
the server finds.
pdd checks the files on this computer first. Then it sends one check for each test. It shows one table (story, test,
result, checks, time), the AI calls and a report link for each test. Anyone with a report link can open it.
A failed check shows the criterion, the path, the expected value and the answer: `AC1  result /totalCents  expected 899, got 900`.
A draft prompt is checked too. Its row and its report say DRAFT. A DRAFT pass is not an approval.

| Exit | Result | What to do |
|---|---|---|
| 0 | passed | Put the one-line result in the PR (section 15). If it says DRAFT, offer a Try. |
| 1 | failed | Show the person the failed check. Fix the prompt. Never change the expected value yourself. |
| 4 | refused | Nothing was judged. Fix the file that pdd names (table below). If the fix changes an expected value, ask the person. |
| 5 | not run | Sign-in, network, server busy or no AI room. Run `gh auth status`. Wait, then run again. If it stays, tell the person. |
| 3 | unknown or still running | Run `pdd check --read`. Never send the check again. |
| 2 | command error | Wrong command or story name. Run `pdd check --help`. |

- After a send timeout, pdd prints `pdd check --read <batch>`. Keep reading with it. A slow job can show up 4 minutes later.
- pdd warns "the AC1 check expects 0, but the AC1 text says 409" when a value is not in the criterion text. For counts,
  status codes and exit codes, this warning is often false. Do not change a check for it. The warning "N of the M
  files sent are not prompt, story or test files" is normal in an app repo.

| Refusal | Usual cause | Fix |
|---|---|---|
| `graph-schema-…` | A schema breaks a rule of section 3. `keyword` names the rule; `path: null` names no field | Check every schema against all of section 3. |
| `invalid-input` | A step input breaks the input schema: `"7pm"`, or a tax rate as a number | Fix the input. pdd shows the field and the rule. |
| `story-criterion-mismatch` | A test criterion is not the story text: often curly quotes | Copy the story line exactly. |
| `unchecked-criteria` | A criterion has no exact check | Add a check for it. |
| `interface-stale` | The prose changed after the hash | Draft: run `--fill-hash`. Approved: set draft, fill the hash, ask again. |
| `repository-graph-catalog-error` | Too few AI calls left for a step | Run again with a higher `--max-calls`. |
| `graph-result-failure` | Often the prose calls a prompt more than `max_calls` | Make the prose and `max_calls` agree. |
| `run-admission-failed` | Nothing ran (0 AI calls). Often one step's worst case is bigger than `--max-calls` (section 10). Other causes give the same code with no reason | Raise `--max-calls` (at most 100), or lower `max_calls` in the prompt's `calls`. The interface `limits` do not help. If it stays, tell the person. |
| `invalid-context` | `context` is not a list of `{"prompt_path", "paths"}` rows, for example a text note (section 2). | Fix the rows, or use `[]`. |
| `graph-provider-failure` | The AI service failed. No verdict, also when pdd prints `✗ … 1 refused` | Tell the person, with its AI calls. The person may send it again. Never send it again on your own. |

## 12. `pdd try` and Save as test

`pdd try place-order` makes a Try link and opens it in the browser. Opening costs 0 AI calls. pdd prints:
`Try link for "Place a coffee order" is open in your browser. It ends in 24 hours, or with: pdd try --stop place-order`
- A draft prompt can be tried. The person tries it before they approve. Show the Try link only to the person.
  Never write it into a file, PR, issue or shared channel: anyone with the link can use it.
- Ask the person: "Did it do what you expect?" Wait for the answer before you open PR 1. If the person is not at this
  computer, run `pdd try <story> --no-open` and give the link in the chat.
- A Try needs at least the worst case of its biggest operation, plus 1. For `checkout`: 3 + 1 = 4 AI calls.
  An action that fails with `session-action-failed` at 0 AI calls means the calls ran out: run `pdd try --new <story>`.
- In a Try, the same input again is answered from the cache, at 0 AI calls. An error answer is not cached.
- A Try pauses after 15 minutes with no clicks. `pdd try <story>` reopens it at 0 AI calls. It does not send changed
  files or a new app map: for that, run `pdd try <story> --new`.

**Save as test.** Only the person saves a case. Never save one yourself. pdd adds each saved case as a new step to the
story's test file and prints `added to tests/<file> as step <id>`. It makes a new file only when the story has none.
- The Try page may say "Save this file in your project as `tests/<name>.json`" and warn about unchecked criteria.
  Ignore that. Do not make a second file: `pdd try` adds the case to the story's test file.
- In a person's terminal, `pdd try` keeps waiting and adds saved cases as they come.
- When you (an agent) run `pdd try`, it reads the saved cases once and returns, so it never blocks you. After the person
  says "I saved some cases", run `pdd try <story>` again to add them.
Then make sure that every criterion still has a check, and run `pdd check <story>`.

## 13. Give your app a screen (app map)

The Try page has a **Screen** tab only when the repo has an app map: a JSON file that connects prompt operations to
screens. It holds no code. Without it, the person uses forms (or a terminal for `cli`).
- `pdd try` uses `app-map.json` at the repo root, else `app/app-map.json`. For another file:
  `pdd try <story> --app-map <path> --new`. Without `--new`, pdd reuses the open Try and does not send the map.
  Git must show the file. It must be an app map like the one below, not a page of your app (`public/index.html`).
  pdd does not check the map. A wrong map may give only "The Try setup is not finished or its result is unknown".
- **A screen from an operation** (`"source": "operation"`): the operation draws the screen. `format` is `html`, `text`
  or `grid`. `result_pointer` selects the drawing: `/html` (a string) or `/lines` (a list of strings). `stylesheets` lists CSS files.
- **A screen from a mockup** (`"source": "mockup"`, `"operation": null`, `"format": "svg"`, `"result_pointer": null`):
  the screen prompt declares the screen and its callbacks in one code line, for example
  `@Composable fun MenuScreen(state: MenuState, onAdd: (String, String) -> Unit): Unit`. Its one operation gets
  `{"state": …}` and returns `{"svg": …}`. Its `## Appearance` section links the mockups:
  `![Menu with cart lines](views/menu-cart__phone.ui.svg)`. The `phase` in the screen input selects one
  (`"phase": "menu-cart"`), and the AI fills it. Each part to fill or tap has an `id`. The prose says how to fill each
  part and which callback a tap part gets ("region `price-latte-m`, callback `onAdd`, arguments `["latte","M"]`").
  Use at most 4 mockups for each screen, 64 KiB each, with no scripts.
- `input` is the operation input, or the `state` of a mockup screen. `{"$ref": "/state/cart"}` copies a value (roots:
  `/state`, `/event`, `/result`, `/route`, `/world`). Other values are used as written. `state_schema` follows section 3.
- **A handler** connects a tap or a key to an operation. `match` for each `kind`: `button` `{"value": "place-order"}`
  (html `<button value="place-order">`), `region` `{"region_id": "price-latte-m", "callback": "onAdd"}` (SVG), `key`
  `{"value": "n"}`. `next` stays (`"same"`) or goes to a `"screen"`. `state` replaces the whole state: list every field,
  or give `null` to keep it. `after` runs more operations in order and puts a result in the state (`"bind": "/order"`).
- Each tap costs the handler's AI calls plus 1 to draw the screen. In Harbor, opening cost 1 and a tap cost 2 to 3.

Cut from the Harbor Coffee app map (`…` marks cut parts):
```json
{"schema_version": "prompt-runtime.app-map.v1", "name": "Harbor Coffee", "initial_screen": "menu", "initial_route": null,
 "initial_state": {"cart": [], …}, "state_schema": {…}, "synthetic": true, "router": null, "routes": [], "stylesheets": [],
 "screens": [{"id": "menu", "prompt_path": "prompts/menu_screen.prompt.md", "operation": null, "source": "mockup",
   "format": "svg", "input": {"phase": "menu-empty", "cart": {"$ref": "/state/cart"}, …}, "result_pointer": null},
   {"id": "cart", …the same, with "phase": "menu-cart"…}, …],
 "handlers": [{"screen": "*", "kind": "region", "match": {"region_id": "price-latte-m", "callback": "onAdd"},
   "handler": {"prompt_path": "prompts/cart.prompt.md", "operation": "add_item"},
   "input": {"cart": {"$ref": "/state/cart"}, "itemId": "latte", "size": "M"},
   "next": {"kind": "screen", "screen": "cart", "route_pointer": null},
   "state": {"cart": {"$ref": "/result/cart"}, …every other state field…}}, …]}
```

## 14. Bug workflow

1. Reproduce: turn the issue into a test. Add a criterion to the story and a step that checks it to the story's test file.
   The expected value comes from the issue and the person.
2. Run `pdd check <story>` on the CURRENT prompt. Do not change the prompt first.
3. ✗ failed: tell the person "Verdict: the bug is in the PROMPT (its check fails on the issue's case)." Fix the
   prompt first (set draft, fill the hash), and check again until ✓.
4. ✓ passed: tell the person "Verdict: the prompt is right; the bug is only in the CODE." The repo's own tests prove
   the code fix.
5. The check report shows before ✗ → after ✓. `pdd try <story>` opens with the issue's input ready.
- If no prompt owns the behavior, say in reproduce: "No prompt exists yet for this behavior, so the bug can only be
  in the code." The verdict line is "Verdict: no prompt covers this yet; the bug can only be in the code." Write the
  prompt from the issue, and write "before: no prompt" in PR 1.
- Put the verdict line first in the gate message, before any details.
- Keep the change small: change one prompt when you can, and test only the criteria of the bug.
- PR 1 must not make the repo's own tests fail. Put a new failing code test in PR 2, or mark it `todo` in PR 1.
  Never offer to merge PR 1 while the repo's tests fail on its branch.

## 15. PR text

Put one line and the report link at the top of the PR text. The link expires after 7 days. Anyone with the link can
open it. Do not paste logs, warnings or full paths of this computer (`/Users/…`). PR 1 cannot merge while a prompt in
it is still draft.
```
Runtime check: ✓ 3 of 3 criteria · 10/10 checks · 1 AI call
Report: https://…/r/617480ac-…
```

## 16. Known limits today

- The report page drops line breaks in strings. The check itself is exact: `"Added #1: Buy milk"` fails against
  `"Added #1: Buy milk\n"`. If expected and got look the same, look for a `\n`.
- Some refusals give no reason ("See the reported reason"). Use the refusal table in section 11.
- The report page says "Run in your signed-in terminal: `pdd replay …`". That command does not exist yet.
- In a Try, the action that uses the last AI calls may not show its answer. The page says "This Try has ended".
- The Try page says "1 AI call each". A step with saved data or a prompt call uses 2 to 3.
- `pdd try --stop <story>` finds the Try only on a branch that has the story's test file.

## 17. The code PR (PR 2): test vectors and the formal check

The runtime proves the prompt. PR 2 must prove that the **code** does the same.

**Test vectors: the PR 1 cases, run on the real code.**
- Use `tests/<story>.json` from PR 1 as it is. Never edit it in PR 2. If an expected value looks wrong, stop and ask
  the person: that is a PR 1 change.
- In `build`, write one replay test in the repo's own test runner (for example `test/<story>.vectors.test.mjs`).
  It reads the JSON file when it runs, and for each step it calls the real public boundary named by `operation`
  (function, command or route). Steps run in order and share state, as on the runtime.
- Map each check target: `result` → the returned value at the path; `error` → the error code; `world` → the app's
  store after the step, seeded from `initial_world`; `calls` → a spy count. A target you cannot map is
  "Not replayed", with the reason. It is never a pass.
- In `verify`, run the replay test. Then run it again on a throwaway copy with ONE planted mistake (in a bug run:
  the old code). At least one case must fail there. A crash does not count.
- Write the table into `verify.md`: case, criterion, input, expected, prompt (PR 1 check), code (got), result.
  Also show that `tests/<story>.json` is unchanged since PR 1.
- A ✗ case goes back to `build` (at most 2 rounds). If it still fails, PR 2 opens with "✗ N vectors fail" as its
  first line.

**The formal check (the new `formal` step, done by an agent that did not write the code).**
- Every PR 2 has a "Formal check" section with one result: **Proved (bounded)**, **Proved (solver)**,
  **Failed + counterexample**, **Not run + reason** or **Not applicable + reason**.
- It is worth it for a precise rule with a clear forbidden result: money and rounding, limits, who may do what,
  order of states, parsers. It is not applicable for looks, wording or plain wiring.
- Take the rule from the Story's `## Rules to check` section, which the person approved in PR 1. Never take it
  from the code.
- Default method: a **bounded check**. Loop over EVERY input in a small, stated range, call the real code, and
  compare with an oracle written from the Story. State the bounds in the PR.
- Use a solver (Z3, or CrossHair for Python) only when the range is too big to loop. Replay each counterexample
  and 2 witnesses on the real code.
- Control: the planted mistake must fail the formal check too. If it does not, write "Not run: the check cannot
  see the mistake".
- Commit the replay test and the formal test as normal tests. Do not commit raw logs.

## 18. Patterns: a pure function and a state sequence

Test only the real operations of the program: functions, commands or routes that the code will have. Never add an
operation only for a check (for example `moveWithInputObservation`, `sequence` or `replay`). The runtime sees results,
saved data and call counts. It cannot see a browser, a phone layout or whether an input object changed. Put such
criteria in a story with no runtime test (pdd only warns "has no test"), and prove them with the repo's tests in PR 2.
Keep the prompt short. A `calls` entry is enough: do not copy the called prompt's schemas. Put a big table or list in a
repo file and link it under `## Dependencies`. Test data goes in the test (`input`, `initial_world`), not in the prompt.

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
- The app really replays a list of moves: one operation takes the list. Make all moves in that one AI call: link the
  rule prompt (`board.prompt.md`) under `## Dependencies` with no `calls` entry, so the AI reads its rules. A `calls`
  entry with `max_calls: 30` makes every step of the prompt need 61 calls (section 10).
