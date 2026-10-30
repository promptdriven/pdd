# PDD runtime runbook

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

## 1. What the runtime is

The runtime runs a prompt as a program. There is no code: an AI reads the `*.prompt.md` file and acts as the program.
The runtime checks the **prompt**, not the code. The repo's own tests check the code.
You need a GitHub login (`gh auth status`). A check sends relevant source selected from Git-visible files (max 10 MiB and 10,000 files).
`pdd check --files` lists the selected files and byte sizes without a network call (section 2). Never put secrets in the repo.

The order of work: story → prompt (`"status": "draft"`) → test → `pdd check --fill-hash` → `pdd check <story>` →
offer `pdd try <story>` → the person tries it and approves → PR 1 with the one-line result (section 15).
Read section 3 (schema rules) and section 8 (check paths) before the first check. Most failed first checks start there.
When the person asks you to report a problem with pdd itself, follow
[docs/ISSUES.md](https://github.com/promptdriven/pdd/blob/main/docs/ISSUES.md).

## 2. The files

| File | What it holds |
|---|---|
| `prompts/<job>.prompt.md` | The program in plain English, then `## Dependencies`, then one Runtime interface block. |
| `user_stories/<story>.md` | One story with a numbered `## Acceptance criteria` list. pdd skips index files: `PLAN.md`, `README.md` and any file with no `## Acceptance criteria` heading. |
| `tests/<story>.json` | The test for that story. pdd finds tests in any folder. If the repo's own tests are in `tests/` or `test/`, use `tests/runtime/` or `test/runtime/`. |

**1 story = 1 test file = many cases.** Each case is one step. Steps run in order and share the saved data.
Across its steps, the test file must check every criterion of its story.

Keep each test step small. One step = one action, or a short run of actions (about 10 moves, rows or calls). Split a long replay into steps with the expected state after each part. The server stops a step after 10 minutes.
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

**Scoped uploads.** A check selects its tests, their stories, entry prompts and explicit test context. It recursively
follows prompt call targets, local links in `## Dependencies` and Markdown images in selected Markdown files.
A selected app map adds its prompt paths and stylesheets. Unrelated repository files are not uploaded.
`pdd check --files [STORY...]` lists exactly which files the same selection uploads, with byte sizes and no network
call. With no Story, it selects all discovered tests. Add `--app-map PATH` to inspect the selection for a Try map.

For extra source, put an include list in the repository root's `pdd-source.json`:
```json
{"include": ["docs/shared-rules.md", "assets/menu.css"]}
```
This file contains only `include`, an array of repository-relative file paths, not globs or directories. These files
are added to the test and dependency selection. Included Markdown and prompts also have their dependencies followed.
The config is read locally and is not automatically uploaded. Selected files must be Git-visible regular files.
Secret-looking names, symlinks (including symlink ancestors), missing files and paths outside the repository are refused.

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

Integer bounds in schemas (`minimum`, `maximum`, `exclusiveMinimum`, `exclusiveMaximum` and `multipleOf`) must lie
within `[-9007199254740991, 9007199254740991]`, or ±(2^53−1). An out-of-range integer bound is refused. The refusal
names the bad bound's JSON Pointer (for example `/properties/count/maximum`), the declared bound (`bound_text`)
and the supported range (`supported_integer_range`).

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
- A person decides expected values. If you think one is wrong, propose a change to the person; never make it yourself.
  Never change a test to make it pass.

**Possible numeric mismatches.** pdd checks nearby numeric literals as typo advice, not as a verdict. It uses the
result path and companion checks to distinguish a component from a total. The warning names the test, step/check,
result path and Story criterion. Confirm that both quantities agree with the Story and prompt; retain a correct
expected value. Calls, world assertions and count checks do not get this advice.

For a reviewed difference that remains ambiguous, record a rationale in the Git-visible repository-root file
`pdd-numeric-reviews.json`. This acknowledges only that advisory; it changes no test or Runtime assertion:
```json
{"schema_version":"pdd.numeric-reviews.v1","reviews":[
  {"test_path":"tests/budget.json","test_sha256":"<current test SHA-256>","step_id":"usage","criterion_id":"AC8",
   "target":"result","path":"/derived_usage","value":95,"reason":"This is component usage; the criterion states the combined cap."}
]}
```
Get the full test hash with `shasum -a 256 tests/budget.json`. Every identity field must match, including current
test bytes, step, criterion, target, path and value. The reason must be nonblank and one line (at most 1000 characters).
A changed test invalidates its review. The file allows at most 100 reviews and 16 KiB; invalid metadata warns and
suppresses nothing. It is local authoring metadata and is not automatically uploaded. Exact criterion-text checks
and all Runtime checks stay in force.

## 5. Saved data

The AI cannot compute a hash. Declare a compute resource with hash_json or hash_utf8, or keep this criterion in native tests. This applies when the program must build or verify a SHA-256 hash: both operations return a lowercase SHA-256. Keep any other digest, for example an HMAC, in native tests. See the [record-id fragment in §21](#verify-a-record-id).

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

Name the program in the prompt’s first heading, for example `# tipjar` (a single safe command name; `pdd`, `node`, `gh` and `git` are reserved).
Mark both schemas with the `cli` convention. `argv` goes in. `exit_code`, `stdout` and `stderr` come out. In full:
```json
"input_schema": {"type": "object", "properties": {"argv": {"type": "array", "items": {"type": "string"}}}, "required": ["argv"], "additionalProperties": false},
"result_schema": {"type": "object", "properties": {"exit_code": {"type": "integer"}, "stdout": {"type": "string"}, "stderr": {"type": "string"}},
                  "required": ["exit_code", "stdout", "stderr"], "additionalProperties": false},
"conventions": [{"path": "/entries/0/input_schema", "convention": "cli"}, {"path": "/entries/0/result_schema", "convention": "cli"}]
```
- Input: one item for each word, as a shell splits them. `todo add Walk the dog` is `{"argv": ["add", "Walk", "the", "dog"]}`.
- An optional string `stdin` property receives piped UTF-8 text. Program exit code 125 is reserved for `pdd try` wrapper failures; use another code for program errors.
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
  For the `error` target, pdd prints `got no error (a normal result)` when the step returned a result and no error.
  Then the path is right, and the prompt did not refuse this input. If pdd still prints `got {"missing": true}` on
  `error`, an error came back without that field: compare the path with the prompt's declared errors.
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
- `pdd check` gives each test 12 calls for each step, at least 18 and at most 1000. Override it with `--max-calls N` from 1 through 1000, the runtime maximum.
- **Choose a ceiling of at least 3 times your worst-case estimate** when setting `--max-calls` for a Check or Try. Include child calls, saved-data operations, redraws and all the moves you plan to try. The budget is a ceiling, not a charge: you are charged only for calls that run. If the estimate does not fit the server maximum, report that limit; do not silently reduce the margin or change expected values.
- A new `pdd try` requests a session budget of 400 calls. `pdd try STORY --max-calls 600` chooses a different ceiling when starting a new Try. The CLI cannot raise an existing Try’s ceiling; `--new` starts fresh saved data. The output shows the runtime-confirmed total and remaining calls. Reusing a Try without this option keeps its current budget.
- Too few calls left gives the refusal `repository-graph-catalog-error`. It is not a prompt error. The interface `limits` do not set this budget.
- **Worst case of a step:** 1, plus for each entry in its prompt's `calls`: `max_calls` × (worst case of the called
  prompt + 1). Calls belong to the whole prompt (section 8), so every operation of the prompt has this worst case.
  `checkout` → `pricing` with `max_calls: 1`: 1 + 1 × 2 = 3. `game` → `board` with `max_calls: 30`: 1 + 30 × 2 = 61.
  When one step's worst case is bigger than `--max-calls` (at most 1000), the runtime refuses the whole test before it
  starts: `run-admission-failed`, 0 AI calls. So keep `max_calls` small (section 18).
- **A Try page allows 40 AI calls for each tap.** A screen or key whose prompt's worst case is over 40 never
  opens: refused at 0 calls. A screen prompt that calls another prompt with a high `max_calls` hits this fast
  (`game` → `board` with `max_calls: 30` is 61 per tap). Keep the screen prompt's chain small: one call with a whole
  list (section 18), not many calls.
- **Check small first.** A schema refusal costs 0 AI calls. A wrong check path costs the full run: one cost 34 calls.
  - In a new project, check the story with the fewest steps first. Check the others only after it passes.
  - Start a new test with few steps: often one step for each criterion is enough. Add more cases after it passes.
  - After a failure, check only that story again (`pdd check <story>`), not all stories.
  - Before a check of more than 5 steps, tell the person the likely cost: about 4 AI calls for each step.

## 11. `pdd check`

`pdd check --fill-hash` fills the hash of draft prompts. `pdd check` checks every test at the same time.
`pdd check place-order` checks one story. `pdd check --read` reads the last results again. `--fill-hash` sends nothing. A saved `--read` may continue original checks held for lint after it passes, using identical source, owner and call ceilings; other reads send nothing.
Before you send a check, run `pdd check --lint` to find format problems (0 AI calls). Exit 0 means finished and passed; queued/running lint exits 3 with its saved read command. Never import pdd's source.
`pdd check --lint [STORY…]` sends the files to the server's lint only. It makes no AI call, and it prints every problem
the server finds.
pdd checks the files on this computer first. Then it sends one check for each test. It shows one table (story, test,
result, checks, time), the AI calls and a report link for each test. Anyone with a report link can open it.
A failed check shows the criterion, the path, the expected value and the answer: `AC1  result /totalCents  expected 899, got 900`.
The report preview shows the first 256 characters of a longer string followed by `…`. The check still compares
the full value exactly. Preview clipping and sensitive-value redaction do not shorten the value being checked.
A draft prompt is checked too. Its row and its report say DRAFT. A DRAFT pass is not an approval.
In a person's terminal, `pdd check` waits until every check ends and prints `Still running: …` every 30 s. In an
agent's shell it returns after about 90 s with `Still running` and the batch; then run `pdd check --read` about every
minute, doing other work in between, until every Story has a result. Never send the same check again.
Before `pdd check` or `pdd try`, tell the person in one line what you run and that it can take a few minutes. pdd prints
a progress line on stderr before each slow step (lint, upload, the queue, the Try setup). When it fails, it says what
failed, the real reason and what to do next: pass that line on as it is.

| Exit | Result | What to do |
|---|---|---|
| 0 | passed | Put the one-line result in the PR (section 15). If it says DRAFT, offer a Try. |
| 1 | failed | Find the cause first ("After a ✗" below). Fix only what the evidence shows. A person decides expected values. |
| 4 | refused | Nothing was judged (`no verdict ·`): a file breaks a rule, or the AI service failed. Read the reason and the next step under the line. When the reason names a file rule, fix that file (table below); for an AI-service cause, change no file. If a fix changes an expected value, ask the person. |
| 5 | not run | Sign-in, network, server busy or no AI room. Run `gh auth status`. Wait, then run again. If it stays, tell the person. |
| 3 | unknown or still running | Run `pdd check --read` about every minute until every Story has a result. Never send the check again. |
| 2 | command error | Wrong command or story name. Run `pdd check --help`. |

**After a ✗ (exit 1).** Find the real cause first, then fix it. Never send the same files again to get another answer.
1. Read pdd's `Why:`, `Next:` and `Rerun:` lines when pdd prints them. Open "Debug this step" on the report. Read the
   criterion text, the prompt and the test step.
2. Tell the person in three lines: the kind, the evidence and the fix you propose.
3. Act by kind:

| Kind | Evidence | What you do |
|---|---|---|
| The prompt is wrong | The Story and the step input give the expected value; the prompt does something else | Fix the prompt. Check that Story once. |
| The program needs a tool | Only a hash, a digest or exact math shows the right answer | Declare a `compute` resource (section 21, "Hash exact bytes"). Check once. |
| The test path is wrong | `got {"missing": true}` on `result` or `world` (section 8) | Fix only the path. |
| The expected value may be wrong | The Story does not give this value, or gives another one | Stop. Ask the person: keep the value (you fix the prompt) or change the test. Give an example. |
| The Story is unclear | Two answers fit the Story | Stop. Ask the person to decide the rule in the Story. |
| The answer changes between runs | `Rerun: failed 1 of 3 (unstable)` | Make the rule in the prompt firmer. Do not fit the prompt to one answer. |
| No verdict | `no verdict ·` with an AI-service or limit cause, or `busy ·` when the remaining checks are busy. Exit 3, 4 or 5 can also hide a failed Story: read each Story line | Tell the person, with pdd's next step. Change no file. Never send it again on your own. |

4. At most 2 fix rounds for the same ✗. Then stop, and tell the person what you tried.

- After a send timeout, pdd prints `pdd check --read <batch>`. Keep reading with it. A slow job can show up 4 minutes later.
- A `possible numeric mismatch` is advisory. Confirm the quantities against the Story and prompt; retain a correct
  expected value. Section 4 explains scoped review rationales. The count of files sent that are not prompt, Story
  or test files is an informational note.

| Refusal | Usual cause | Fix |
|---|---|---|
| `graph-schema-…` | A schema breaks a rule of section 3. `keyword` names the rule; `path: null` names no field | Check every schema against all of section 3. |
| `invalid-input` | A step input breaks the input schema: `"7pm"`, or a tax rate as a number | Fix the input. pdd shows the field and the rule. |
| `story-criterion-mismatch` | A test criterion is not the story text: often curly quotes | Copy the story line exactly. |
| `unchecked-criteria` | A criterion has no exact check | Add a check for it. |
| `interface-stale` | The prose changed after the hash | Draft: run `--fill-hash`. Approved: set draft, fill the hash, ask again. |
| `repository-graph-catalog-error` | Too few AI calls left for a step | Run again with a higher `--max-calls`. |
| `graph-result-failure` | Often the prose calls a prompt more than `max_calls` | Make the prose and `max_calls` agree. |
| `run-admission-failed` | Nothing ran (0 AI calls). Often one step's worst case is bigger than `--max-calls` (section 10). Other causes give the same code with no reason | Raise `--max-calls` (at most 1000), or lower `max_calls` in the prompt's `calls`. The interface `limits` do not help. If it stays, tell the person. |
| `invalid-context` | `context` is not a list of `{"prompt_path", "paths"}` rows, for example a text note (section 2). | Fix the rows, or use `[]`. |
| `graph-provider-failure` | The AI service failed. No verdict: pdd prints `no verdict ·` (✗ only when another check failed, in this Story or another Story) | Tell the person, with its AI calls. The person may send it again. Never send it again on your own. |
| `graph-uncertain-child-dispatch` | One AI call did not answer. No verdict. Your test is fine | Same as `graph-provider-failure`. |

## 12. `pdd try` and Save as test

`pdd try place-order` makes a Try link and opens it in the browser. Opening costs 0 AI calls. While it works (about a minute), pdd
prints a progress line on stderr for each step. It ends with:
`Try ready for "Place a coffee order": <link> (open in your browser). It ends in 24 hours, or with: pdd try --stop place-order`
- A draft prompt can be tried. The person tries it before they approve. Show the Try link only to the person.
  Never write it into a file, PR, issue or shared channel: anyone with the link can use it.
- Ask the person: "Did it do what you expect?" Wait for the answer before you open PR 1. If the person is not at this
  computer, run `pdd try <story> --no-open` and give the link in the chat.
- A Try needs at least the worst case of its biggest operation, plus 1. For `checkout`: 3 + 1 = 4 AI calls.
  An action that fails with `session-action-failed` at 0 AI calls means the calls ran out: run `pdd try --new <story>`.
- In a Try, the same input again is answered from the cache, at 0 AI calls. An error answer is not cached.
- A Try pauses after 15 minutes with no clicks. `pdd try <story>` reopens it at 0 AI calls. It does not send changed
  files or a new app map: for that, run `pdd try <story> --new`. Connecting Ask your agent or a CLI/HTTP door requires matching uploaded prompts; if a prompt changed, start a fresh Try with `--new`.

**Save as test.** Only the person saves a case. Never save one yourself. pdd adds each saved case as a new step to the
story's test file and prints `added to tests/<file> as step <id>`. It makes a new file only when the story has none.
- The Try page may say "Save this file in your project as `tests/<name>.json`" and warn about unchecked criteria.
  Ignore that. Do not make a second file: `pdd try` adds the case to the story's test file.
- With terminal stdout, `pdd try` connects Ask your agent, keeps waiting and adds saved cases as they come. `--no-wait` skips the connection.
- When you (an agent) run `pdd try`, it reads the saved cases once and returns, so it never blocks you. After the person
  says "I saved some cases", run `pdd try <story>` again to add them. An explicit `--agent NAME` connects even without a terminal and waits until Ctrl-C. Keep its private owner chat link out of shared messages.
Then make sure that every criterion still has a check, and run `pdd check <story>`.

## 13. Give your app a screen (app map)

### The drawing is the layout spec

When a screen prompt links a `.ui.svg`, that drawing is authoritative for its visible parts, words, spatial order, stable ids and named state. It is a comparison reference, not an optional illustration. Prose and drawing must describe the same parts; prose owns behavior and the sources of dynamic values. Declare the state and viewport beside the view and name each region/control id in the appearance rules. Mark unowned surroundings `data-context-only="true"` or class `context-only`. Keep DOM/focus order in accessibility prose; SVG source order does not set it.

Before building, run `pdd check --lint --local` (or add Story names) to see local SVG warnings with 0 AI calls and no network. It checks explicit control names, visible labels and named layout regions in both directions. A generic score field does not specify a drawn score box. Static vocabulary matching is advice: warnings name unmatched parts and never block or approve a prompt. Ordinary `pdd check --lint` includes this advice before its existing server lint. Resolve disagreements by making the prompt and drawing agree with the requested design.

Build reads the linked drawing as the layout spec and implements its parts, words, ids, order and state. After building, serve the real page in the reference state and run:

```sh
pdd check --screen http://127.0.0.1:8080/ --drawing prompts/views/active__stacked.ui.svg
```

This uses installed headless Chrome/Chromium at the SVG viewport, no AI or runtime calls. Set `PDD_CHROME_PATH` if the executable is not found. It checks every visible text occurrence and id, including numeric values, against the real page; metadata, hidden and context-only SVG subtrees are excluded. It requires visible page parts, center positions within 15% of each viewport dimension, and the same spatial order for separated parts. Arrange the named state and its dynamic values before comparing. This parts comparison does not certify pixel equivalence; retain any stricter accepted measured/exact comparator and tolerance. Text matches require effective visible glyph paint and literal displayed control labels; password and other nondisplayed stored values never supply labels. Applied clips, masks, filters and unsupported text paint or native formatting leave visibility unproved and return an error. Arbitrary overlay occlusion, colors and typography require separate verification.

Verification must put a **Screen vs drawing** table in `verify.md` and in the body of the code PR (code space):

| Part | Drawing | Screen | Result |
|---|---|---|---|
| Named id or visible text | Expected state/region | Observed state/region | Pass or concrete failure |

Keep actual rows and the command's exit code. A missing/hidden part, wrong region or inverted order fails verify like a failing test. A missing browser, page or reference leaves verify unproved; never mark it passed. Return to build and compare again until the screen matches; never remove required parts from the reference to obtain a pass. A failing table remains a failure if workflow retry limits are reached. Include every linked reference state affected by the change. A 2048 screen without the drawing's score box, seed box or READY bar must fail even when behavior tests pass.

### App map

The Try page has a **Screen** tab only when the repo has an app map: a JSON file that connects prompt operations to
screens. It holds no code. Without it, the person uses forms (or a terminal for `cli`).
- `pdd try` uses `app-map.json` at the repo root, else `app/app-map.json`. For another file:
  `pdd try <story> --app-map <path> --new`. Without `--new`, pdd reuses the open Try and does not send the map.
  Git must show the file. It must be an app map like the one below, not a page of your app (`public/index.html`).
  pdd does not check the map. A wrong map may give only "The Try setup is not finished or its result is unknown".
- **A screen from an operation** (`"source": "operation"`): the operation draws the screen. `format` is `html`, `text`
  or `grid`. `result_pointer` selects the drawing: `/html` (a string) or `/lines` (a list of strings). `stylesheets` lists CSS files.
  The runtime cleans the drawn html. It removes the `background` style, `list-style` and `aria-pressed`. Write
  `background-color` for a fill, `aria-current="true"` for a chosen button, and `display:block` on each `<li>` for a
  list with no bullets.
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
- **A handler** connects a tap or a key to an operation. `match` may use `id`, `region_id`, `callback`, `href`,
  `value`, `name` and `label`. Examples: `button` `{"value": "place-order"}` (html `<button value="place-order">`),
  `region` `{"region_id": "price-latte-m", "callback": "onAdd"}` (SVG), `key` `{"value": "n"}`. `state` replaces the
  whole state: list every field, or give `null` to keep it. `after` runs more operations in order and puts a result
  in the state (`"bind": "/order"`).
- **`next`** always has these 3 keys. Stay on this screen: `{"kind": "same", "screen": null, "route_pointer": null}`.
  Go to a screen: `{"kind": "screen", "screen": "cart", "route_pointer": null}`. Use the router (only with a `router`):
  `{"kind": "route", "screen": null, "route_pointer": "/route"}`.
- **`/event`** in `input` or `state`: every event has `screen`, `target` and `kind`. `target` is the element's own
  `id` when that id is unique on the screen. A `link` adds `href`. A `key` or `command` adds `value` (the key). A
  `button` matched by `value` has that `value`. A `submit` (a `<form>`) adds `fields`: the form's named, visible
  fields, as strings (hidden inputs are not sent). A mockup `region` with a typed callback adds `arguments`. Use one
  field, for example `{"$ref": "/event/target"}`. The whole event (`{"$ref": "/event"}`) is refused.
- **Give every button a unique `id`** in the drawing. Then a tap keeps its target when the screen draws again, also a
  tap that waits in line.
- **On one screen, match all handlers of one kind by the same key.** Two `button` handlers with `{"value": …}` and
  `{"name": …}` on one screen are refused as `ambiguous-handler`.
- **A button on each row:** give the row buttons one `name` and the row's key as `id`:
  `<button name="mark-read" id="b2">Mark as read</button>`. One handler serves all rows:
  `{"kind": "button", "match": {"name": "mark-read"}, "input": {"id": {"$ref": "/event/target"}}, …}`. Then match the
  other buttons of that screen by `name` too (`name="show-all"`). The field that gets `/event/target` must be a plain
  `{"type": "string"}`: a stricter schema (`minLength`, `pattern`) is refused as `template-reference-schema`.
- Each tap costs the handler's AI calls plus 1 to draw the screen. In Harbor, opening cost 1 and a tap cost 2 to 3.
- A tap's worst case is the handler's worst case (section 10) plus 1 to draw. A Try page allows 40 for each tap.
  A screen or handler whose prompt's worst case is over 40 never opens (refused at 0 calls). Keep the chain small.

A full, small app map (a book list with 2 filter buttons; one screen from an operation):
```json
{"schema_version": "prompt-runtime.app-map.v1", "name": "Bookshelf", "initial_screen": "shelf", "initial_route": null,
 "initial_state": {"show": "all", "books": [{"id": "b1", "title": "Dune", "read": false}]},
 "state_schema": {"type": "object", "properties": {
   "show": {"type": "string", "enum": ["all", "unread"]},
   "books": {"type": "array", "items": {"type": "object", "properties": {"id": {"type": "string"},
     "title": {"type": "string"}, "read": {"type": "boolean"}}, "required": ["id", "title", "read"],
     "additionalProperties": false}}},
   "required": ["show", "books"], "additionalProperties": false},
 "synthetic": true, "router": null, "routes": [], "stylesheets": [],
 "screens": [{"id": "shelf", "prompt_path": "prompts/shelf_page.prompt.md", "operation": "render", "source": "operation",
   "format": "html", "input": {"books": {"$ref": "/state/books"}, "show": {"$ref": "/state/show"}}, "result_pointer": "/html"}],
 "handlers": [
  {"screen": "shelf", "kind": "button", "match": {"value": "show-unread"},
   "handler": {"prompt_path": "prompts/books_api.prompt.md", "operation": "list_books"}, "input": {"read": "false"},
   "next": {"kind": "same", "screen": null, "route_pointer": null},
   "state": {"show": "unread", "books": {"$ref": "/result/books"}}},
  {"screen": "shelf", "kind": "button", "match": {"value": "show-all"},
   "handler": {"prompt_path": "prompts/books_api.prompt.md", "operation": "list_books"}, "input": {},
   "next": {"kind": "same", "screen": null, "route_pointer": null},
   "state": {"show": "all", "books": {"$ref": "/result/books"}}}]}
```
`render` returns `{"html": "…"}` with `<button id="show-unread" value="show-unread">Only unread</button>`.

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
3. ✗ failed: tell the person "Verdict: the bug is in the PROMPT (its check fails on the issue's case)." Find the
   cause first (section 11, "After a ✗"). Fix the prompt (set draft, fill the hash) and check again: at most 2 fix
   rounds, then ask the person.
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

Put the `Runtime check` line(s) that `pdd check` prints, with their report links, at the top of the PR text. One
Story gives one line, `Runtime check (<story>): …`. 2 or more Stories give one line each and a last `Runtime check:`
line for all. The link expires after 7 days. Anyone with the link can open it. Do not paste logs, warnings or full
paths of this computer (`/Users/…`). PR 1 cannot merge while a prompt in it is still draft.
```
Runtime check (place-order): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call
Report: https://…/r/617480ac-…
```

## 16. Known limits today

- The report page drops line breaks in strings. The check itself is exact: `"Added #1: Buy milk"` fails against
  `"Added #1: Buy milk\n"`. If expected and got look the same, look for a `\n`.
- Some refusals give no reason ("See the reported reason"). Use the refusal table in section 11.
- The report page says "Run in your signed-in terminal: `pdd replay …`". That command does not exist yet.
- In a Try, the action that uses the last AI calls may not show its answer. The page says "This Try has ended".
- The Try page says "1 AI call each". A step with saved data or a prompt call uses 2 to 3.

## 17. Code space: replay evidence and the formal check

On `agent thread limit reached`, follow the workflow skill's checking fallback. Before checking, close finished subagents if supported, then try a fresh checker first. Only after fresh startup failure may verify/formal reuse an agent that wrote no code, tests or prompts in this run. If no eligible checker can run:

- For review, write `Not checked: review (agent limit)` in the review run file; review always needs a fresh agent, never a reused checker.
- For another unrun check, write `Not checked: <step> (agent limit)` in its run file.

Stop and tell the person to start a new agent session in the run's worktree. No verdict or `workflow done` for unrun checks.
`pdd workflow open 42` focuses or resumes the same session; it does not start a new one or clear the limit.
Only after the check actually runs, replace its `Not checked:` line with the real result in the step's run file and any copy in `verify.md`; never keep both.

Agents replay the approved prompt-space cases against the real code. Runtime checks of prompts do not establish
that the code behaves the same. Agents execute the tests and supply the evidence; pdd validates structure and
identity only. It does not independently prove execution or prompt/code equivalence.

In verify after the last commit, run one `pdd workflow prove <run> --test "<command>" --expect "<Defect: text>"` command that covers all new or changed tests; its line goes on the PR. Fresh worktrees have no installed dependencies, so include any required installation in the command.

**Test vectors: the approved cases, run on the real code.**
- Use `tests/<story>.json` from prompt space as it is. Never edit it in code space. If an expected value looks
  wrong, return to prompt space for the person's approval and start a run with the approved vectors.
- In `build`, write one replay test in the repo's own test runner (for example `test/<story>.vectors.test.mjs`).
  It reads the JSON file when it runs, and for each step it calls the real public boundary named by `operation`
  (function, command or route). Steps run in order and share state, as on the runtime.
- Map each check target: `result` → the returned value at the path; `error` → the error code; `world` → the app's
  store after the step, seeded from `initial_world`; `calls` → a spy count. A target you cannot map is
  "Not replayed", with the reason. It is never a pass. Missing checks and unexecuted operations are not replayed.
- In `verify`, run the replay test. Then run it again on a throwaway copy with ONE planted mistake (in a bug run:
  the old code). At least one assertion must fail there. A crash does not count.
- Write the table into `verify.md`: case, criterion, input, expected, prompt check, code (got), result.
  Also show that `tests/<story>.json` is unchanged since prompt space.
- In bug and feature, finish the initial build, verify and formal steps with fresh independent review.
  After the initial review, a ✗ case or review must-fix goes back to `build` (at most 2 repair rounds),
  then verify, formal and fresh review. The code-space PR keeps the actual `Review:` verdict and remaining
  must-fix list at the top, plus "✗ N vectors fail" if vectors still fail. No new human gate.
  Keep actual failures; never change expected values to get a pass.

**The formal check (done by an agent that did not write the code).**
- Every code-space PR has a "Formal check" section with one result: **Proved (bounded)**, **Proved (solver)**,
  **Failed + counterexample**, **Not run + reason** or **Not applicable + reason**.
- Use it for a precise rule with a clear forbidden result: money and rounding, limits, who may do what,
  order of states, parsers. It is not applicable for looks, wording or plain wiring.
- Take the rule from the approved Story's `## Rules to check` section. Never take it from the code.
- Default method: a **bounded check**. Loop over EVERY input in a small, stated range, call the real code, and
  compare with an oracle written from the Story. State the bounds in the PR.
- Use a solver (Z3, or CrossHair for Python) only when the range is too big to loop. Replay each counterexample
  and 2 witnesses on the real code.
- Control: the planted mistake must fail the formal check too. If it does not, write "Not run: the check cannot
  see the mistake". A crash is not assertion detection.
- Commit the replay test and the formal test as normal tests. Do not commit raw logs.

**Structured record for a workflow run.**
New bundled feature/bug code areas opt in with `replay_evidence: "pdd.replay-evidence.v1"`. Saved areas and
custom workflows without that field keep their publication behavior; small-change has no replay policy.
After each prompt-space publication or push, pdd refreshes the changed scenario files, their original byte
hashes and step/check identities in `status.json` as `replayBaseline`, including empty or blocked selections.
This continues through the final approval publication before code space. Final approval refuses unpublished
scenario edits; publish approved edits in prompt space first. On entry into code space the published anchor
freezes; a code-space retry cannot replace it. No selected vectors means not replayed.

Before completing each code-space step, the agent writes `<run-folder>/replay-evidence.json`; update it
with the formal result after that step. Use the versioned contract in the package's `docs/replay-evidence.md`.
It records the run ID, current Git-visible content fingerprint, every original vector hash, per-check outcomes,
public-boundary executions, exact counts, a semantic mutation control and a typed formal result with scope and
reason. Keep this JSON in the run folder, outside the Git-visible source; never commit it or raw logs.
Missing/unmapped checks need honest not-replayed outcomes, and a control that was not run needs a reason.

pdd revalidates immediately before publishing, after committing leftovers, and when updating an open PR.
It independently inventories current changed scenario files against the saved run base with exact
NUL-delimited Git paths, including non-ASCII names. A scenario absent from the frozen anchor makes replay
BLOCKED even when all anchored checks pass; an unavailable inventory cannot establish PASS.
Changed, absent, empty or unreadable original files cannot pass even with a new source fingerprint. Missing,
malformed or stale records produce prominent **BLOCKED** / **NOT REPLAYED** status above prose and prompt
check results. Actual assertion or formal failures remain publishable with a failure line. An existing PR is
marked publication-pending before source is pushed; a failed final description update leaves it pending.
A structurally valid agent-reported replay pass can coexist with an explicit formal **Not run** or
**Not applicable**; neither means a formal proof. Read the counts, scope, reason and trust boundary together.

## 18. Patterns: a pure function and a state sequence

Test only the real operations of the program: functions, commands or routes that the code will have. Never add an
operation only for a check (for example `moveWithInputObservation`, `sequence` or `replay`). The runtime sees results,
saved data and call counts. It cannot see CSS layout, sizes, animation or whether an input object changed.
A page or a screen is never "browser-only": what it shows and what each tap does are results. Give it an app map
(section 13). A page with no mockup gets a `render` operation that returns `{"html": …}` plus the facts it shows,
for example `{"html": "…", "emptyMessage": "No books yet", "rows": 3}`. Check the facts with `equals` or `count`
on those fields (`/emptyMessage`); use structured HTML checks for markup (section 20). Only what the runtime truly cannot see (CSS layout, sizes,
animation) goes in a story with no runtime test (pdd only warns "has no test"), proved with the repo's tests in PR 2.
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
- If the app really accepts a list of moves, use short lists of about 10 per step. Check the expected state after
  each part and pass it to the next part; keep the same complete replay coverage. Link its rule prompt under
  `## Dependencies`. Do not invent a replay operation only for tests, or expand a short action into an unbounded
  chain of prompt calls. The server stops one step after 10 minutes, regardless of the remaining call budget.

## 19. Use a Try from your terminal or curl

`pdd try STORY --cli` prints a shim path and a PATH line. Startup and every command show a Try AI usage line on stderr: calls for the command, used/remaining in this session and its cap. Unknown counters stay unknown; this is separate from account/tester allowance. Copy the PATH line, then run the program normally.
`--shell` opens bash or zsh with that PATH. Each command uses your gh login and the same Try's saved data.
`pdd try --save-last` appends the last command and its observed result to the original test file; review the
recorded expectation and its saved-data setup. `pdd try --stop STORY` stops the session. A wrapper error prints
**pdd try:** on stderr and exits 125; program errors preserve the program's other exit codes.

`pdd try STORY --serve 8080` exposes named HTTP routes at `http://127.0.0.1:8080`. A prompt names an inbound
route by setting the entry's `input_schema.title`, for example `"title": "HTTP GET /api/books"`. Each entry names
one method and path. Supported methods are GET, HEAD, POST, PUT, PATCH, DELETE and OPTIONS. Use literal path
segments or `:id` parameters declared as string input fields (directly or under a `params` object). Duplicate
method/path patterns are refused. The `http.prompt` simulation binding handles outbound resource
calls inside a graph; a route title only selects an existing admitted entry.

For a query entry, an optional string input `read` receives `?read=false` as `{"read":"false"}`. Declared
boolean and number inputs receive typed values; repeated query fields require arrays. Request-shaped entries
may instead declare `method`, `path`, `query`, `params`, `headers` and `body`. Only declared fields are forwarded.
A JSON body is parsed; a string `body` receives exact UTF-8 text. Inputs still must match the entry schema.

Return `status`, an optional object of response `headers`, and `body` (a string or JSON value). An existing
result such as `{"status":200,"books":[...]}` returns `{"books":[...]}` as its JSON body. HTTP status and headers
come from the prompt; hop-by-hop headers are removed and Content-Length is calculated by pdd. An unknown
route returns 404 without an AI call. Runtime or wrapper trouble returns 502 with a plain **pdd try:** reason.
The listener binds only to loopback and accepts browser requests only from its own origin. Ctrl-C closes the
local server while the Try keeps its data. Use curl or fetch for API routes; browser page, image, script and
stylesheet loads cannot spend calls through an API route.

When the Story has an app map, open `http://127.0.0.1:8080/` for the actual Screen. If it has not been drawn,
click **Open the app**; opening and taps use the same Try budget and saved data. Loading the page alone uses
no AI call. The Screen reuses the hosted renderer, styles and declared click/form/key targets. It keeps an action
ID before sending and reads that same ID after a lost reply or reload; it never sends the action twice. Unknown
outcomes block new taps until recovered. Screen-only Stories need no named HTTP route; startup says **Screen only (no named HTTP routes)**.
If a saved Try has no app map, use the printed `--new --app-map PATH` command to start one with the selected map.
A Story with neither an app map nor named routes gets a plain message describing both options. An app map reserves
GET/HEAD `/` and `/__pdd/screen/`; move conflicting named routes. Credentials stay in pdd, outside the page.

## 20. HTML checks and Try rendering

A structured HTML check selects a result string with `target: "result"` and a JSON Pointer such as `/html`.
Its `html` object names a selector and a kind. The selector matches a lowercase tag and optional exact attribute
values; it is not a CSS selector. For example:
```json
{"criterion_id": "AC1", "target": "result", "path": "/html", "op": "equals", "value": "Done",
 "html": {"selector": {"tag": "button", "attributes": {"id": "finish"}}, "kind": "text"}}
```
- `kind: "element"` supports `exists` only. Its boolean value defaults to `true`; `false` asserts no matches.
- `kind: "attribute"` also names `attribute`, such as `"attribute": "aria-current"`. It supports `exists`, `equals`,
  `not_equals`, `one_of` and `contains`.
- `kind: "text"` supports the same operations on concatenated descendant text, without whitespace normalization.
  Text `exists` tests for nonempty text; attribute `exists` tests presence. Both default to `true`.
  Other operations compare strings; `one_of` takes a list of strings and `contains` a nonempty substring.

Attribute and text assertions must hold for every matched element and fail if none match. A missing attribute
cannot satisfy `not_equals`. Raw HTML is validated before sanitization: at most 256 KiB of UTF-8 HTML, 4,096 elements,
64 nested non-void elements, 64 attributes per element, 64 selector attributes and 256 KiB of text. Duplicate
attributes, unmatched or misnested closing tags, closing tags for void elements, unclosed elements and unterminated
markup fail the check. Parser and size failures appear as `invalid_html` diagnostics.

**One rendering contract.** Structured HTML checks and Try share the sanitizer. Checks select elements and read
attributes and text from the same sanitized HTML that Try displays. The renderer derives interactive target markers
after sanitization. Reported attribute values describe the retained subset, with sensitive values redacted.
Assert only on elements, attributes and style declarations that survive.

The supported HTML subset includes ordinary text and sections, headings, lists, tables, forms and controls.
Allowed attributes include `id`, `class`, `role`, `title`, form attributes such as `name`, `value`, `type` and `disabled`,
and accessibility attributes including `aria-label`, `aria-expanded`, `aria-checked`, `aria-selected` and `aria-current`.
Inline CSS supports physical and logical sizing (`width`, `height`, `inline-size`, `block-size` and their `min-`/`max-`
forms), `overflow-wrap`, `background-color`, color, borders, margin, padding, fonts, text, display, visibility,
opacity, overflow, flex and grid layout. Non-active `text-decoration` such as `line-through` survives.

The sanitizer removes `background` shorthand, `list-style`, `aria-pressed`, event handlers, unknown attributes and
CSS properties, scripts and active content. Embedded `<style>` elements are removed; admitted app stylesheets
provide stylesheet rules. External URLs are removed; retained URL attributes must be repository-local, without a
scheme, host or parent traversal. CSS URLs, scripts, unsafe functions and indirection such as `var()` are filtered.
Allowed CSS functions are `rgb`, `rgba`, `hsl`, `hsla`, `calc`, `min`, `max` and `clamp`, subject to the same safety
filters. A removed element, attribute or declaration cannot satisfy a structured HTML assertion.

The all-Story check estimate includes entry executions, declared saved-data operations and nested prompt-call allowances; conditional operations can use fewer calls. The hard `--max-calls` cap stays authoritative. Named HTTP responses include `x-pdd-ai-calls`, `x-pdd-try-used`, `x-pdd-try-remaining`, `x-pdd-try-cap` and `x-pdd-usage-source` (`runtime` for a receipt, `last-known` for local zero-call responses). Startup shows session usage on stderr. Program stdout, HTTP bodies and status codes retain their program values; CLI stderr carries program text followed by accounting. No model call or repeat dispatch is made for accounting.

## 21. Fake the outside world

Anything outside the code (databases, files, network, clock, randomness and other programs) goes behind an injected port; never call it directly from the decision logic. Declare the actual dependency's operations as Runtime resources, and supply their replies in the test. SQL, blob and compute are specialized resource bindings. Preserve existing public functions, factories and methods; do not invent a check-only API.

The examples below specify small JavaScript modules with matching prompt contracts; native execution is reported separately. Their scenarios are synthetic, with exact expected results chosen before execution. The commands run in a clone of pdd (`git clone -b alpha https://github.com/promptdriven/pdd`), from its root; in your own repository, copy the linked files with their paths first. Each command first runs zero-call server lint, then a live prompt check with a hard ceiling; every step requests `gpt-6.1-sol`. A ceiling is not a charge. Native tests establish code behavior separately.

```sh
pdd check --fill-hash
pdd check --lint fake-database fake-files fake-hash fake-service fake-decision fake-factory
pdd check fake-database --max-calls 9
# Substitute fake-files, fake-hash, fake-service, fake-decision or fake-factory.
```

Each linked prompt includes complete schemas, resource declarations and limits; each scenario includes its starting world, bindings and checks. Copy the complete pair and its Story, then replace the module-owned behavior and expectations from your requirement. Never pass the test or Story as program context.

### Seed a SQL connection

[Module](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/database.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/database.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/alpha/user_stories/fake-database.md) · [Scenario](https://github.com/promptdriven/pdd/blob/alpha/test/runtime/fake-database.json)

Bind one logical connection to one `world_pointer` for all reads, writes and transactions. Starting rows live under `rows`; SQL executes in real in-memory SQLite. Named scalar argument `id` binds `:id`. Inspect `/database/rows/books`, not SQLite snapshot internals. For dynamic nullable parameters use `statement_argument_pointer` plus JSON-text `parameters_argument_pointer`; never interpolate values into SQL.

```json
{
  "initial_world": {
    "database": {
      "schema": [
        "CREATE TABLE books (id INTEGER PRIMARY KEY, title TEXT NOT NULL)"
      ],
      "rows": {
        "books": [
          {
            "id": 1,
            "title": "Dune"
          }
        ]
      }
    }
  },
  "simulation": {
    "db.find": {
      "action": "sql.execute",
      "world_pointer": "/database",
      "statement": "SELECT title FROM books WHERE id = :id",
      "result_mode": "rows",
      "result_template": {
        "rows": []
      },
      "result_value_pointer": "/rows"
    }
  }
}
```

Passing prompt check (DRAFT): [2/2 checks · 2 AI calls](https://runtime.promptdriven.ai/r/13e8c6dc-532a-4f0c-bb0b-1d1b3671d2a8).

### Read UTF-8 files

[Module](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/files.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/files.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/alpha/user_stories/fake-files.md) · [Scenario](https://github.com/promptdriven/pdd/blob/alpha/test/runtime/fake-files.json)

Files are keyed by exact POSIX path, each with UTF-8 `content` and `is_symlink`. `blob.write` additionally selects a content argument; `blob.stat` supports exists/is_symlink/size. These fakes never open a host path. Ownership, permissions, races, fsync and atomic rename require explicit ports and native tests.

```json
{
  "initial_world": {
    "files": {
      "/notes/hello.txt": {
        "content": "Hello\n",
        "is_symlink": false
      }
    }
  },
  "simulation": {
    "files.read": {
      "action": "blob.read",
      "world_pointer": "/files",
      "path_argument_pointer": "/path",
      "content_argument_pointer": null,
      "result_template": {
        "content": ""
      },
      "result_value_pointer": "/content"
    }
  }
}
```

Passing prompt check (DRAFT): [1/1 checks · 2 AI calls](https://runtime.promptdriven.ai/r/91df0610-5ecd-4b3b-833f-58a5162d2690).

### Hash exact bytes

[Module](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/hash.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/hash.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/alpha/user_stories/fake-hash.md) · [Scenario](https://github.com/promptdriven/pdd/blob/alpha/test/runtime/fake-hash.json)

The prompt calls `compute.hash_utf8` with `{text}` and returns `{value}`. The deterministic compute action hashes exact bytes; do not ask the model to calculate a digest. `hash_json` hashes the runtime canonical JSON representation and is not interchangeable with an application-specific canonical serializer.

```json
{
  "initial_world": {},
  "simulation": {
    "compute.hash_utf8": {
      "action": "compute",
      "result_template": {
        "value": null
      },
      "result_value_pointer": "/value"
    }
  }
}
```

Passing prompt check (DRAFT): [1/1 checks · 2 AI calls](https://runtime.promptdriven.ai/r/5b26a5ee-1b45-4a79-beb6-ae1dd4c891a3).

### Verify a record id

This is a fragment, not a runnable example. It shows only the two parts that hashing adds. To run it, you also need a Story, a prompt with a full Runtime interface (its `entries`, `prose_sha256` and `limits`), a scenario with steps and checks, and the native module. "Hash exact bytes" above is a complete example.

`verify(record)` gets a record with `text` and `id`, and returns `{"valid": boolean}`. The prompt removes `id`, calls `compute.hash_json` with `{"value": {"text": record.text}}`, and compares the returned lowercase SHA-256 with `id`.

The `resources` entry of the prompt's Runtime interface:

```json
{"resources":[{"name":"compute","kind":"compute","access":"read","operations":[{"name":"hash_json","access":"read","arguments_schema":{"type":"object","properties":{"value":{"type":"object","properties":{"text":{"type":"string"}},"required":["text"],"additionalProperties":false}},"required":["value"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"value":{"type":"string"}},"required":["value"],"additionalProperties":false}}]}]}
```

The `simulation` entry of the scenario:

```json
{"simulation":{"compute.hash_json":{"action":"compute","result_template":{"value":null},"result_value_pointer":"/value"}}}
```

`hash_json` hashes the runtime's canonical JSON: keys sorted by UTF-16 code units, no spaces, and the runtime's own spelling of numbers (a subset of RFC 8785). An application's own serializer can give other bytes, for example for floats or non-ASCII keys. To hash exact bytes that the application made, use `hash_utf8`. Native tests must prove that the hash and the serializer match.

Lint accepts this declaration also when the native code hashes inside (for example with Python `hashlib`) and takes no `compute` argument. Keep the native signature. [Module binding coverage](https://github.com/promptdriven/pdd/blob/alpha/docs/runtime-bindings.md) checks that the prompt can reach its operations. It does not run native hashing. Native tests own that, and a lint pass is not a behavior pass.

### Inject a fixed-answer callback

[Module](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/service.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/service.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/alpha/user_stories/fake-service.md) · [Scenario](https://github.com/promptdriven/pdd/blob/alpha/test/runtime/fake-service.json)

The native `lookup(service, id)` uses the supplied callback; resource `service.lookup` binds that same boundary. `port.write` appends actual argument objects at `/requests` and returns the fixed `result_template`. Assert both the reply and exact request list. The fixed answer does not prove authentication, transport, timeout handling or any live service effect. Never include credentials in fixtures.

```json
{
  "initial_world": {
    "requests": []
  },
  "simulation": {
    "service.lookup": {
      "action": "port.write",
      "world_pointer": "/requests",
      "result_template": {
        "label": "Available"
      }
    }
  }
}
```

Passing prompt check (DRAFT): [2/2 checks · 2 AI calls](https://runtime.promptdriven.ai/r/53737185-9685-408f-83ca-be9e13c6ae79).

### Separate decide from do

[Module](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/decision.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/decision.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/alpha/user_stories/fake-decision.md) · [Scenario](https://github.com/promptdriven/pdd/blob/alpha/test/runtime/fake-decision.json)

`decideReply` is a pure public decision over supplied facts; `doLookup` obtains those facts through the injected callback and applies the same rule. The first step proves an unavailable decision without I/O; the second proves the exact effect request and available result. Split only when the native design benefits: SQL and callbacks do not require a split merely to bind them.

```json
{
  "initial_world": {
    "requests": []
  },
  "simulation": {
    "service.lookup": {
      "action": "port.write",
      "world_pointer": "/requests",
      "result_template": {
        "available": true
      }
    }
  }
}
```

Passing prompt check (DRAFT): [4/4 checks · 3 AI calls](https://runtime.promptdriven.ai/r/7cd3364c-d048-46a0-b7a3-41194739405c).

### Keep factory instances with handles

[Module](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/factory.mjs) · [Prompt](https://github.com/promptdriven/pdd/blob/alpha/examples/fakes/factory.prompt.md) · [Story](https://github.com/promptdriven/pdd/blob/alpha/user_stories/fake-factory.md) · [Scenario](https://github.com/promptdriven/pdd/blob/alpha/test/runtime/fake-factory.json)

Use `schema_version: "prompt-runtime.interface.v2"`, `instance_types: [{"name":"Greeter","resource":"instances"}]`, and write-access collection resource `instances`. Factory entry `instance` is `{"kind":"factory","type":"Greeter","path":"/handle"}`; method uses kind `method` with the same type/path. Mark both handle fields with the `handle` convention. Store captured state under the executor-issued `instance_handle`; never fabricate a handle or expose closure configuration as a new native method argument. The next step takes `{"$step_result":{"step_id":"create","path":"/handle"}}`. Native callers still receive an object with a method; the handle is its JSON transport identity.

```json
{
  "initial_world": {
    "instances": []
  },
  "simulation": {
    "instances.store": {
      "action": "collection.merge",
      "world_pointer": "/instances",
      "key_argument_pointer": "/handle",
      "value_argument_pointer": "/config",
      "item_key_pointer": "/handle",
      "item_value_pointer": "/config",
      "result_template": {
        "config": null
      },
      "result_value_pointer": "/config"
    },
    "instances.load": {
      "action": "collection.get",
      "world_pointer": "/instances",
      "key_argument_pointer": "/handle",
      "value_argument_pointer": null,
      "item_key_pointer": "/handle",
      "item_value_pointer": "/config",
      "result_template": {
        "config": null
      },
      "result_value_pointer": "/config"
    }
  }
}
```

Passing prompt check (DRAFT): [2/2 checks · 4 AI calls](https://runtime.promptdriven.ai/r/eaa3c792-986a-498c-8970-5d67181d179e).

A prompt pass proves these synthetic cases against the declared fake world. It does not execute the JavaScript module, establish every input/error, approve the prompt, or prove a live effect. If a criterion remains unbound, state the exact missing contract or unsupported effect and the native test needed; never report it as passed.
## Use the Try tools when they are available

The person's own agent can use the stdio server, `pdd mcp`, in the current repository. On the person's intent (for example, "try adding a bookmark with tag news"), use `try_open` to open or reuse the Story's Try, `try_state` to inspect it, fill the input in `try_run`, `try_check` to check the run against the Story, and `try_save_case` to save a case. Follow the tools' returned input schemas and errors. Each run counts against the Try's call budget and appears in the Try page's history; inspect remaining calls before more work.

Saved cases go to a separate `tests/<story>-try-<run-id>.json` with the run's exact starting data; the original scenario stays intact. A recorded case that covers only part of the Story must be completed before `pdd check`, which requires every criterion. Saved cases contain observed results. Review them against the Story with the person before treating them as expected values. Saving or checking a case never approves its expectations or a prompt. If the tools are unavailable, offer `pdd try STORY`.
