# PDD runtime runbook

## 1. What the runtime is

The runtime runs a prompt as a program. There is no code: an AI reads the `*.prompt.md` file and acts as the program.
The runtime checks the **prompt**, not the code. The repo's own tests check the code.
You need a GitHub login (`gh auth status`). A check sends every file that Git shows (max 10 MiB and 10,000 files).
`pdd check --files` lists them. Never put secrets in the repo.

The order of work: story → prompt (`"status": "draft"`) → test → `pdd check --fill-hash` → `pdd check <story>` →
offer `pdd try <story>` → the person tries it and approves → PR 1 with the one-line result (section 12).

## 2. The files

| File | What it holds |
|---|---|
| `prompts/<job>.prompt.md` | The program in plain English, then `## Dependencies`, then one Runtime interface block. |
| `user_stories/<story>.md` | One story with a numbered `## Acceptance criteria` list. |
| `tests/<story>.json` | The test for that story. If `tests/` already holds the app's tests, use `tests/runtime/`. |

**1 story = 1 test file = many cases.** Each case is one step. Steps run in order and share the saved data.
Across its steps, the test file must check every criterion of its story.
Add a second file only for a case that needs a different starting world. That file also checks every criterion.

**The prompt** ends with `<details><summary>Runtime interface</summary>`, a ```` ```json ```` block and `</details>`.
The block of Harbor Coffee's `place_order` (schemas cut):
```json
{"status": "draft", "prose_sha256": "",
 "entries": [{"operation": "place_order", "input_schema": {...}, "result_schema": {...}, "errors": ["unknown-item"]}],
 "calls": [], "resources": [], "limits": {"max_steps": 4, "max_model_calls": 2}, "conventions": []}
```
- Close every schema with `"additionalProperties": false`. List every error that the prose can return in `errors`.
- Do not write `prose_sha256`: `pdd check --fill-hash` fills it. Never set `"status": "approved"` yourself. The person approves.
- To change an approved prompt (prose or interface), set `"status": "draft"`, run `pdd check --fill-hash` and ask the person again.

**The story** has one line for each criterion. Number from 1. Use straight quotes (`"`), not curly quotes.
Text copied from a GitHub issue often has curly quotes. Put real values in the text: "$10.65", "2026-11-02".

**The test** copies every criterion into `criteria`, word for word. From `todo-cli` (some checks cut):
```json
{"schema_version": "prompt-runtime.program-scenario.v1", "story_path": "user_stories/finish-task.md",
 "criteria": [{"id": "AC1", "text": "`todo done 4` prints \"Done #4: Call mom\", exits with code 0 and saves task #4 as done."},
              {"id": "AC2", "text": "Task #1 stays not done."},
              {"id": "AC3", "text": "`todo done 9` prints \"todo: no task #9\" to stderr, exits with code 1 and saves nothing."}],
 "initial_world": {"kv": {"todos": [{"id": 1, "text": "Buy milk", "done": false}, {"id": 4, "text": "Call mom", "done": false}]}},
 "simulation": {"store.load": {...}, "store.save": {...}}, "context": [],
 "steps": [
  {"step_id": "finish-task-4", "entry_path": "prompts/todo.prompt.md", "operation": "main",
   "input": {"argv": ["done", "4"]},
   "checks": [{"criterion_id": "AC1", "target": "result", "path": "/stdout", "op": "equals", "value": "Done #4: Call mom\n"},
              {"criterion_id": "AC1", "target": "world", "path": "/kv/todos/1/done", "op": "equals", "value": true},
              {"criterion_id": "AC2", "target": "world", "path": "/kv/todos/0/done", "op": "equals", "value": false}]},
  {"step_id": "finish-missing-task-9", "entry_path": "prompts/todo.prompt.md", "operation": "main",
   "input": {"argv": ["done", "9"]},
   "checks": [{"criterion_id": "AC3", "target": "result", "path": "/stderr", "op": "equals", "value": "todo: no task #9\n"},
              {"criterion_id": "AC3", "target": "calls", "path": "/resources/todo-store-save", "op": "equals", "value": 0}]}]}
```
- Each criterion needs at least one exact check: `equals`, `not_equals`, `one_of` or `count`.
- The `input` must match the `input_schema`. An error step has `"expected_error": "unknown-sku"` and a check on `error` `/code`.
- Check facts, not values that the AI picks freely (wording that the story does not fix, generated IDs).

| `target` | `path` | Real example |
|---|---|---|
| `result` | a JSON pointer into the answer | `/quote/totalCents` equals 3784 |
| `error` | `/code` | equals `"unknown-coupon"` |
| `world` | a pointer into the saved data after the step | `/stamps/sam` equals 11 |
| `calls` | `/resources/<prompt>-<resource>-<operation>`: count in this step (`<prompt>` = file name without `.prompt.md`) | `/resources/todo-store-save` equals 0 |
| `calls` | `/internal/<called prompt>`: count in this step | `/internal/pricing` equals 1 |

## 3. Expected values

- Expected values come from the story and the person. Never take them from a run, a Try or the code.
- If the story allows two answers, ask the person. Example: "every 10th coffee free" gives $4.95 off, but
  "the price of its cheapest drink" gives $2.75 off. Do not choose yourself.
- Never change a test to make it pass. Fix the prompt. If you think an expected value is wrong, tell the person.

## 4. Saved data

Declare the data as a resource in the interface. The prose names each operation:
"Read the tasks once with `store.load` and the key `todos`." (`todo-cli`, schemas cut):
```json
"resources": [{"name": "store", "kind": "key-value", "access": "write", "operations": [
  {"name": "load", "access": "read", "arguments_schema": {...}, "result_schema": {...}},
  {"name": "save", "access": "write", "arguments_schema": {...}, "result_schema": {...}}]}]
```
In the test, `initial_world` is the saved data before step 1. `simulation` connects each operation to the world:
```json
"initial_world": {"kv": {"todos": [{"id": 3, "text": "Buy milk", "done": true}]}},
"simulation": {"store.load": {"action": "key-value.get", "world_pointer": "/kv", "key_argument_pointer": "/key",
  "value_argument_pointer": null, "item_key_pointer": null, "item_value_pointer": null,
  "result_template": {"value": null}, "result_value_pointer": "/value"}, "store.save": {...}}
```
- `store.save` is the same, with `"action": "key-value.put"`, `"value_argument_pointer": "/value"` and `"result_template": {"value": []}`.
- A missing key reads as `null`. Say in the prose what `null` means ("no tasks yet"). Keys must be non-empty strings.
- Check the saved data with `target: world`. Check "saves nothing" with a `calls` count of 0.
- Other actions: `collection.get`, `collection.get-or-null`, `collection.merge` (the world is a list of records),
  `port.write`, `blob.read`, `blob.write`, `blob.stat`, `sql.execute`, `fixture.lookup` and `compute`.
- `port.write` returns its fixed `result_template`. In Harbor, every saved order got the ID 101. Do not check such IDs.

## 5. Command-line programs (`cli`)

Mark both schemas with the `cli` convention. `argv` goes in. `exit_code`, `stdout` and `stderr` come out.
```json
"conventions": [{"path": "/entries/0/input_schema", "convention": "cli"},
                {"path": "/entries/0/result_schema", "convention": "cli"}]
```
- Input: one item for each word, as a shell splits them. `todo add Walk the dog` is `{"argv": ["add", "Walk", "the", "dog"]}`.
- Write the rule "Every line written to `stdout` or `stderr` ends with one newline." in the prose.
  Expected text includes the last newline: `"Added #4: Walk the dog\n"`. An empty stream is `""`.

## 6. A prompt that calls another prompt

`checkout` asks `pricing` for a quote. The caller's interface has a `calls` entry:
```json
"calls": [{"operation": "quote", "target": "prompts/pricing.prompt.md", "target_operation": "quote", "max_calls": 1}]
```
- Link it in `## Dependencies`: ``- [Pricing](pricing.prompt.md), runtime use for operation `quote`.``
- Say in the prose how many times to call: "Call `pricing` operation `quote` exactly once."
  More calls than `max_calls` refuse the check (`graph-result-failure`).
- To pass an error back, list it in the caller's own `errors`, and say it in the prose:
  "If `pricing` returns the error `unknown-coupon`, return the error `unknown-coupon`."
- Check the count: `/internal/pricing` equals 1. For an unknown product, it equals 0.

## 7. Money and dates

- Do all money math in whole cents. Write the rounding rule in the prose, with an example:
  "Round half a cent up (215.5 becomes 216)." If the app shows dollars, check dollars: `/total` equals 10.65.
- Give a rate as a decimal string, not a number: `"taxRatePercent": "8.875"`.
- Give a date as a `YYYY-MM-DD` string with a `pattern`. Write the calendar rules in the prose
  ("closed every Monday", "a real calendar date"). Use real dates in the story: "Monday 2026-11-02", "2026-02-30".
- A `compute` resource does exact decimal and date math. Whole cents and a written rule were exact for a 14-item bill,
  so use `compute` only when a check shows a math error.

## 8. AI calls

- A step costs 1 AI call when the prompt only answers. It costs 2 to 3 calls when it uses saved data or calls
  another prompt. `checkout` can use 3: 1 for checkout, 1 for pricing, 1 to finish. A 3-step Harbor test used 9.
- `pdd check` gives each test 4 calls for each step, at least 6 and at most 100. To give more, use `--max-calls N`.
- Too few calls left gives the refusal `repository-graph-catalog-error`. It is not a prompt error. The interface `limits` do not set this budget.

## 9. `pdd check`

```sh
pdd check --fill-hash     # fill the hash of draft prompts; sends nothing
pdd check                 # check every test, all at the same time
pdd check place-order     # check one story
pdd check --read          # read the last results again; sends nothing
```
pdd checks the files on this computer first. Then it sends one check for each test and shows one table:
```
Story                           Test                     Result   Checks  Time
Place a coffee order            tests/place-order.json   passed   10/10   21.0 s
Refuse an item not on the menu  tests/unknown-item.json  passed   1/1     16.1 s
2 of 2 stories passed. AI calls: 2. Model asked for: gpt-6.1-sol.
Reports (anyone with a link can open it):
  place-order   https://…/r/617480ac-…
```
A failed check shows the criterion, the path, the expected value and the answer: `AC1  result /totalCents  expected 899, got 900`.
A draft prompt is checked too. Its row and its report say DRAFT. A DRAFT pass is not an approval.

| Exit | Result | What to do |
|---|---|---|
| 0 | passed | Put the one-line result in the PR (section 12). If it says DRAFT, offer a Try. |
| 1 | failed | Show the person the failed check. Fix the prompt. Never change the expected value yourself. |
| 4 | refused | Nothing was judged. Fix the file that pdd names (table below). If the fix changes an expected value, ask the person. |
| 5 | not run | Sign-in, network, server busy or no AI room. Run `gh auth status`. Wait, then run again. If it stays, tell the person. |
| 3 | unknown or still running | Run `pdd check --read`. Never send the check again. |
| 2 | command error | Wrong command or story name. Run `pdd check --help`. |

- After a send timeout, pdd prints `pdd check --read <batch>`. Keep reading with it. A slow job can show up 4 minutes later.
- A provider "unknown" (`graph-provider-failure`) means the AI service failed. There is no verdict.
  Do not send it again on your own. Tell the person, with the AI calls it used. Send again only with their OK.

| Refusal | Usual cause | Fix |
|---|---|---|
| `invalid-input` | A step input breaks the input schema: `"7pm"`, or a tax rate as a number | Fix the input. pdd shows the field and the rule. |
| `story-criterion-mismatch` | A test criterion is not the story text: often curly quotes | Copy the story line exactly. |
| `unchecked-criteria` | A criterion has no exact check | Add a check for it. |
| `interface-stale` | The prose changed after the hash | Draft: run `--fill-hash`. Approved: set draft, fill the hash, ask again. |
| `repository-graph-catalog-error` | Too few AI calls left for a step | Run again with a higher `--max-calls`. |
| `graph-result-failure` | Often the prose calls a prompt more than `max_calls` | Make the prose and `max_calls` agree. |

## 10. `pdd try` and Save as test

`pdd try place-order` makes a Try link and opens it in the browser. Opening costs 0 AI calls. pdd prints:
`Try link for "Place a coffee order" is open in your browser. It ends in 24 hours, or with: pdd try --stop place-order`
- A draft prompt can be tried. The person tries it before they approve. Show the Try link only to the person.
  Never write it into a file, PR, issue or shared channel: anyone with the link can use it.
- A Try needs at least the worst case of its biggest operation, plus 1. For `checkout`: 3 + 1 = 4 AI calls.
  An action that fails with `session-action-failed` at 0 AI calls means the calls ran out: run `pdd try --new <story>`.
- In a Try, the same input again is answered from the cache, at 0 AI calls. An error answer is not cached.

- A Try pauses after 15 minutes with no clicks. `pdd try <story>` reopens a paused Try at 0 AI calls.

**Save as test.** Only the person saves a case. Never save one yourself. pdd adds each saved case as a new step to the
story's test file and prints `added to tests/<file> as step <id>`. It makes a new file only when the story has none.
- In a person's terminal, `pdd try` keeps waiting and adds saved cases as they come.
- When you (an agent) run `pdd try`, it reads the saved cases once and returns, so it never blocks you. After the person
  says "I saved some cases", run `pdd try <story>` again to add them.
Then make sure that every criterion still has a check, and run `pdd check <story>`.

## 11. Bug workflow

1. Reproduce: turn the issue into a test. Add a criterion to the story and a step that checks it to the story's test file.
   The expected value comes from the issue and the person.
2. Run `pdd check <story>` on the CURRENT prompt. Do not change the prompt first.
3. ✗ failed: the prompt is wrong. Fix the prompt first (set draft, fill the hash), and check again until ✓.
4. ✓ passed: the prompt is right. The bug is only in the code. The repo's own tests prove the code fix.
5. The check report shows before ✗ → after ✓. `pdd try <story>` opens with the issue's input ready.

## 12. PR text

Put one line and the report link in the PR text. The link expires after 7 days. Anyone with the link can open it.
PR 1 cannot merge while a prompt in it is still draft.
```
Runtime check: ✓ 3 of 3 criteria · 10/10 checks · 1 AI call
Report: https://…/r/617480ac-…
```

## 13. Known limits today

- The report page drops line breaks in strings. The check itself is exact: `"Added #1: Buy milk"` fails against
  `"Added #1: Buy milk\n"`. If expected and got look the same, look for a `\n`.
- Some refusals give no reason ("See the reported reason"). Use the refusal table in section 9.
- In a Try, the action that uses the last AI calls may not show its answer. The page says "This Try has ended".
- A Try pauses after 15 minutes idle.
