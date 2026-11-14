# Runbook: Files, Runtime Interface, Schemas, and Approvals

> Part of [RUNBOOK.md](../RUNBOOK.md) — see the router table in `../RUNBOOK.md` for other `§N` sections.

## 1. What the PDD interpreter is

The PDD interpreter runs a prompt as a program: an AI reads the `*.prompt.md` file and acts as the program.
The interpreter checks the **prompt**; the repo's own tests check native code.
You need a GitHub login (`gh auth status`). A check sends relevant source selected from Git-visible files (max 10 MiB and 10,000 files).
`pdd test --files` lists the selected files and byte sizes without a network call (section 2). Never put secrets in the repo.

The order of work: story → prompt (`"status": "draft"`) → test → `pdd test --fill-hash` → `pdd test <story>` →
offer `pdd simulate <story>` → the person tries it and approves → PR 1 with the one-line result (section 15).
Read section 3 (schema rules) and section 8 (check paths) before the first check. Most failed first checks start there.
When the person asks you to report a problem with pdd itself, follow
[docs/ISSUES.md](https://github.com/promptdriven/pdd/blob/main/docs/ISSUES.md).

## 2. The files

| File | What it holds |
|---|---|
| `prompts/<job>.prompt.md` | The program in plain English, then `## Dependencies`, then one Runtime interface block. |
| `user_stories/<story>.md` | One story: first one line "As a …, I want …, so that …" in the words of the issue (the PR shows it as the user story), then a numbered `## Acceptance criteria` list. pdd skips index files: `PLAN.md`, `README.md` and any file with no `## Acceptance criteria` heading. |
| `tests/<story>.json` | The test for that story. pdd finds it by its name and folder: `<story>.json` with a folder named `tests` or `test` anywhere in its path, not only as the direct parent (`tests/`, `test/runtime/`, `runtime/tests/`). pdd does not look inside other JSON files to find tests, and a test can have any size up to the upload limit (section 1). Every `.json` file in a `tests` or `test` folder named `<story>.json` or `<story>.<word>.json` is a test of that story, so give fixtures and other data files other names. If the repo's own tests are in `tests/` or `test/`, use `tests/runtime/` or `test/runtime/`. |

A Story can narrow its executable closure only with one dedicated block:

````markdown
```pdd-boundary
prompts/place_order.prompt.md
```
````

List repository-relative prompt paths, one per line, including every entry and
Runtime call target. Use exact fence lines separated from other content by blank
lines. The [Story boundary format](https://github.com/promptdriven/pdd/blob/main/docs/cli.md#explain-resource-bindings) gives the
complete path and admission rules. Markdown links, headings and reference
examples do not narrow scope. No block, duplicate blocks, an invalid/unreadable
path or ambiguous syntax keeps the full dependency closure, including context
resources, and adds a named `boundary-not-applied` plan note. A `Runtime boundary`
heading alone gives `boundary not applied: use the pdd-boundary block`. Only a
valid block permits interface projection; actual Runtime calls across it refuse.
Combined selections keep every selected Story's required edge.

**1 story = 1 test file = many cases.** Each case is one step. Steps run in order and share the saved data.
Across its steps, the test file must check every criterion of its story. Put separate user behaviors in separate Stories (`1` Story and `1` test file each) so `pdd test` runs Stories in parallel instead of running one long sequential file.

Keep each test step small. One step = one action, or a short run of actions (about 10 moves, rows or calls). Split a long replay into steps with the expected state after each part. The server stops a step after 10 minutes.
Add a second file only for a case that needs a different starting world. Name it `<story>.<world>.json`, for example `tests/place-order.empty-shop.json`. That file also checks every criterion. pdd prints every story with no test (and the path it expects), one line for the `.json` files in test folders that match no story (`pdd test --files` lists them), and two files with the same name for one story as an error that names both.

**One rule, one prompt.** Before you write a prompt, look in `prompts/` for a prompt that owns the rule. Change that
prompt. Two prompts must never state the same rule. A command-line program has one program prompt (section 6).
A helper module can have its own prompt. Then the program prompt calls it (section 7) and does not repeat its rules.
Prompts own production modules, never repository test suites (`test/**`, `tests/**`, `*.test.*`, `*_test.*` or `test_*.*`); `pdd lint`, `pdd lint --local` and `pdd owner PATH` warn when a prompt claims ownership of test files via `pdd-bindings.json`, `Generated from` headers or opening-sentence prose claims. Keep each `.prompt.md` prose body (excluding its `<details><summary>Runtime interface</summary>` block) at or below 500 lines (`pdd lint` and `pdd lint --local` warn above 500 lines and print an elevated warning above 1,000 lines advising module decomposition or `"kind": "native-only"` with deterministic code tests), and keep each Story scenario JSON at or below 15 steps and 1,000 lines.

**The prompt** ends with `<details><summary>Runtime interface</summary>`, a ```` ```json ```` block and `</details>`.
The block of Harbor Coffee's `place_order` (schemas cut):
```json
{"status": "draft", "prose_sha256": "",
 "entries": [{"operation": "place_order", "input_schema": {...}, "result_schema": {...}, "errors": ["unknown-item"]}],
 "calls": [], "resources": [], "limits": {"max_steps": 4, "max_model_calls": 2}, "conventions": []}
```
- Omit `kind` for a full interface. Explicit `kind` is `partial` or `native-only`.
  A draft with `"kind": "full"` gets a warning at `/kind`, not a refusal; `pdd test --fill-hash` removes it.
  Approved prompts stay unchanged. Full declares the module's checkable behavior. Partial declares only some operations.
  Native-only requires `reason`: name the native effect that the bound ports in §21 cannot fake.
  It needs status and prose_sha256, but no entries or limits. A checker reviews this reason.
  Approval records it. Checks show `not run: <reason>`; they never count it as passed.
- Missing blocks: run `pdd interface draft PROMPT`, or `pdd interface draft --all` for the repository.
  This local command uses explicit prose transport declarations or schemas without AI calls and preserves prose.
  Unknown fields become questions with a `--contract FILE` recovery command. Use `--extend --contract FILE`
  to add operations without changing existing declarations. Use `--refresh [--contract FILE]` to reopen
  a stale or changed block as draft. Effect ports use §21 resources. Run `pdd lint STORY` for Runtime
  admission; local drafting alone proves no Runtime acceptance.
- A complete block drafted from unchanged committed behavior can use
  `pdd approve PROMPT --automatic --tests COMMAND`. Existing native tests and a complete
  current prompt check must pass; pdd records `automatic-check-pass` evidence.
  Strict mode still requires a person. New behavior requires a person.
- Every schema follows section 3. List every error that the prose can return in `errors`.
- Include `"prose_sha256": ""` in the Runtime interface; let `pdd test --fill-hash` calculate its value instead of calculating the hash manually.
- Show the gate. Judge the person's later reply in any chat. A question, change request or earlier message is not approval. No exact phrase is needed. Never invent a decision or edit approval fields. See [Record a chat approval](https://github.com/promptdriven/pdd/blob/main/docs/cli.md#record-a-chat-approval). In a normal workflow run (not strict mode, not Autopilot), the Story gate shows pdd's Story card: show it as printed, then ask, never a bare "approve?". The person approves each Story with that context. With the approval they may choose the code PR after PR 1 (`--through code`); without it, pdd stops after PR 1. For several runs, show the cards one after another and record one answer for each card.
- After actual approval, record the exact words for the ready gate and all its drafts:

```sh
pdd workflow approve N --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

For one prompt:

```sh
pdd approve PROMPT --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

Choose a delimiter absent as a whole line from the payload. Keep it quoted. Never interpolate the words into shell code or shell quotes. `--said -` records stdin exactly, including newlines. Blank input is refused; pdd does not grade nonblank words.
- The gate saves selected prompt paths and prose hashes when shown. If a prompt changes, show the gate again before approval. Output lists the paths and hashes. In a normal workflow run, a prompt-only repair after the Story approval needs no new approval: when pdd verifies a full check pass on the current prompts (every criterion passes and its saved results match the current files), `pdd workflow done check --summary "Prompt tests line"` opens PR 1 itself and records the route `automatic-check-pass`. It skips the optional try step and asks nothing. A change to a Story, the plan or an expected value shows the Story card again for the person. An AI-service failure is no verdict: it asks no one to approve.
- Without --said, a person at a normal terminal can answer y/N once for the listed gate and all its drafts. `pdd approve PATH` approves one prompt. For a caller outside a normal terminal, `pdd workflow approve` instructs the agent to ask the person, then run with --said and their words; `pdd approve PATH` instructs the person to run that command. Native Herdr area-chat evidence may record history but never authorizes approval. Only an explicit approve call passes an approval gate; steps, `workflow done` and chat messages never do. The one exception is the full-pass route of a normal run above: `workflow done` opens PR 1, and nothing else. Warn, without blocking, when a workflow has no approve gate before code.
- Workflow approval reads `pdd.json` from the main checkout (`sourceRoot`), outside the agent's run worktree. Standalone `pdd approve PATH` reads it from the Git root of the current checkout. Root `pdd.json` with `"strict_approvals": true` permits only a person terminal; absent/false is easy mode. Strict mode refuses --said. Prompt approval records the invoking actor, time, route, exact words and path/hash; PR evidence shows matching approvals safely quoted in code spans. Gate approval does not approve the later code-or-stop gate, except the choice that the person gives with a normal run's Story approval. A person decides expected values; never change them on your own.
- pdd never merges and has no merge command. An agent may merge only after the person's explicit chat request. Resolve the PR's exact current head and require at least one check and all required checks green for that head; missing, failed or pending checks stop. First post a PR comment beginning `Merge requested by the person: "…"`, preserving the exact request safely in a Markdown code span (use a fence longer than any backtick run; JSON-quote controls/newlines). Use a body file, never interpolate the words into shell code. A failed comment stops. Recheck head/checks, then run `gh pr merge PR --merge --match-head-commit <head>` with that same head. A changed head stops; obtain green checks for its current head before retrying.
- To change an approved prompt (prose or interface), set `"status": "draft"`, run `pdd test --fill-hash` and ask the
  person to approve again through these routes.

**The interpreted route.** This route does not generate an implementation. It still needs a typed Runtime interface
derived from the prompt's canonical contract and admitted by the runtime; prose alone does not establish executable
entry points. Schema and safety admission do not prove that execution preserves the contract's meaning.
Static native-code binding checks are a separate route. Independent prompt-to-code review does not apply when no
implementation is generated. Record the actual prompt, interface, selected context and checks instead;
do not report a code review that did not occur.

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
- Each criterion needs at least one exact check: `equals`, `not_equals`, `one_of`, `count`, `at_least`, `at_most`, `not_contains`, `all_in` or `equals_ignore_case` (or HTML `exists`, section 20). Paths and operations: section 8.
- The `input` must match the `input_schema`. Each step requires `step_id`, `entry_path`, `operation`, `input` and `checks`, with optional `expected_error`, `simulation_overrides` (section 21) and `model` (omit `model` on ordinary steps unless testing model selection, so the interpreter uses its fast default model). An error step has `"expected_error": "unknown-sku"` and a check on `error` `/code`.
- Check facts, not values that the AI picks freely (wording that the story does not fix, generated IDs).
- `context` is almost always `[]`. It gives one prompt extra text files to read, in this test only. A file linked in a
  prompt's `## Dependencies` is eligible for that prompt's context, subject to the route's selection below. Link shared data there. Each row is exactly
  `{"prompt_path": …, "paths": […]}`: a prompt of the repo, and at most 16 UTF-8 text files of the repo (120 KiB in all):
  `"context": [{"prompt_path": "prompts/ui.prompt.md", "paths": ["docs/tile-colors.md"]}]`. A text note, a missing key
  or an extra key gives `invalid-context` at `context[N]`. Never give the story, a test or expected values as context:
  the program would see the answers. Patterns for tests: section 18.
- Shared records and starting worlds expand locally before `pdd lint`, `pdd test` and `pdd simulate`: use `{"$contract": "contracts/phone-server.md#order_in"}` or `{"$contract": "contracts/records.json#/defs/order"}` in a Runtime interface schema, and `"initial_world": {"$seed": "contracts/seed-world.json", "set": {"/orders": []}}` for a shared starting world (`pdd contracts` lists shared records).

**Scoped uploads.** A check selects its tests, their stories, entry prompts and explicit test context. It recursively
follows prompt call targets, local links in `## Dependencies` and Markdown images in selected Markdown files.
A selected app map adds its prompt paths and stylesheets. Unrelated repository files are not uploaded.
`pdd test --files [STORY...]` lists exactly which files the same selection uploads, with byte sizes and no network
call. With no Story, it selects all discovered tests. Add `--app-map PATH` to inspect the selection for the Simulator's app map.

**Uploaded files are not necessarily execution context.** Ordinary interpreter dependency discovery resolves local
links after dropping `#fragment`. It does not enforce the named section or interpret authoring, generation, runtime,
verification or testing roles. Graph projection selects direct declared context or retained draft context, appearance
context and explicit test context. It excludes executable call targets, except dependencies explicitly retained for
instances. The interface drafter's dependency context defaults to depth 1 and has a byte budget. These are limits
of these routes, not a description of every adapter; shared-contract adapters have their own rules.

Review the required transitive dependency chain for the intended use. Confirm which files and sections that route
actually receives. Missing files or sections, cycles, required omissions and unsupported selection semantics leave
the affected use incomplete. Recursive CLI upload selection alone does not satisfy that review or weaken the contract.

For extra source, put an include list in the repository root's `pdd-source.json`:
```json
{"include": ["docs/shared-rules.md", "assets/menu.css"]}
```
This file contains only `include`, an array of repository-relative file paths, not globs or directories. These files
are added to the test and dependency selection. Included Markdown and prompts also have their dependencies followed.
The config is read locally and is not automatically uploaded. Selected files must be Git-visible regular files.
Safe in-repository file links and linked folders send the final Git-visible regular target bytes under the authored path. Both authored and target names must be safe and Git-visible. Secret-looking names, outside targets, broken links and loops are refused. The bindings inventory and executable/write destinations retain their strict no-link rules.

## 3. Schema rules

These rules apply to every `input_schema` and `result_schema`, to each resource `arguments_schema` and `result_schema`,
and to an app map's `state_schema`. Local preflight reports schema problems in the prompt and called prompts with JSON Pointers at 0 AI calls. Check every schema against these rules before the first `pdd test`.

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

**Large whole numbers.** For a parameter that takes a Number, write a whole number outside ±(2^53−1) in its exact
Number spelling, for example `"seconds": 4.2501298345826807e+24` for 3600 × 2^70. JavaScript and the interpreter read
it as exactly that Number, and the interpreter admits it with `"type": "integer"`. Write each scenario number with
`String(n)` in JavaScript; between 2^53 and 1e21, `String(n)` gives plain digits, so use `n.toExponential()` there.
Never write a scenario number with `json.dumps` of a Python int: it gives plain digits. The PDD interpreter accepts
plain digits only within ±(2^53−1). It refuses larger ones before execution (`scenario-integer-out-of-range`, 0 AI
calls), and pdd warns before it sends the test. When the warning says `If the parameter takes a Number, write its
exact Number spelling …`, apply that fix and check again. Such a refusal is not a reason for `Runtime: not run`. Only
a value that no Number holds (2^53 + 1, or a BigInt parameter) stays in plain JSON digits. pdd reads, shows, compares
and sends those exact digits, and only the repository's own vector test (§17) checks the value. Do not change the
input type or the expected value to fit the interpreter. pdd warns when a token with a fraction or an exponent loses
digits: `9007199254740993.0` reads as `9007199254740992`.

For an optional input field, leave it out of `required`. Do not use `oneOf` with `null` for it: the Simulator's form shows
`oneOf` only as a raw JSON box. A correct schema (`read` is optional):
```json
{"type": "object", "properties": {"title": {"type": "string", "minLength": 1}, "read": {"type": "boolean"},
   "tags": {"type": "array", "items": {"type": "string"}}, "note": {"oneOf": [{"type": "string"}, {"type": "null"}]}},
 "required": ["title", "tags", "note"], "additionalProperties": false}
```

## 4. Expected values

- Expected values come from the story and the person. Never take them from a run, a simulation or the code.
- If the story allows two answers, ask the person. Example: "every 10th coffee free" gives $4.95 off, but
  "the price of its cheapest drink" gives $2.75 off. Do not choose yourself.
- A person decides expected values. If you think one is wrong, propose a change to the person; never make it yourself.
  Never change a test to make it pass.

**Possible numeric mismatches.** pdd checks nearby numeric literals as typo advice, not as a verdict. It uses the
result path and companion checks to distinguish a component from a total. The warning names the test, step/check,
result path and Story criterion. Confirm that both quantities agree with the Story and prompt; retain a correct
expected value. Calls, world assertions and count checks do not get this advice.

For a reviewed difference that remains ambiguous, record a rationale in the Git-visible repository-root file
`pdd-numeric-reviews.json`. This acknowledges only that advisory; it changes no test or interpreter assertion:
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
and all interpreter checks stay in force.
