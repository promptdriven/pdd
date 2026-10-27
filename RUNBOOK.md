## Runtime: check stories on the PDD server

The runtime runs a prompt as a program. There is no code. An AI model on the PDD server reads the
`*.prompt.md` file and acts as the program. The server checks the answer against your test and makes a report.

### The 3 files

| File | What it holds |
|---|---|
| `prompts/<job>.prompt.md` | The program in plain English. Then `## Dependencies`. Then the Runtime interface block. |
| `user_stories/<story>.md` | One story. It has a numbered `## Acceptance criteria` list. |
| `tests/<story>.json` | The test for that one story (`prompt-runtime.program-scenario.v1`). |

Example from Harbor Coffee. The prompt `prompts/place_order.prompt.md` ends like this (schemas cut):

~~~markdown
If an `itemId` is not on the menu, return the error `unknown-item`.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{"status": "draft", "prose_sha256": "",
 "entries": [{"operation": "place_order", "input_schema": {...}, "result_schema": {...},
              "errors": ["unknown-item"]}],
 "calls": [], "resources": [], "limits": {"max_steps": 4, "max_model_calls": 2}, "conventions": []}
```
</details>
~~~

The story `user_stories/unknown-item.md` has one criterion:
`1. An order with the item "pumpkin-spice" is refused with the error "unknown-item".`
Its test `tests/unknown-item.json`:

```json
{"schema_version": "prompt-runtime.program-scenario.v1",
 "story_path": "user_stories/unknown-item.md",
 "criteria": [{"id": "AC1", "text": "An order with the item \"pumpkin-spice\" is refused with the error \"unknown-item\"."}],
 "initial_world": {}, "simulation": {}, "context": [],
 "steps": [{"step_id": "lee-orders-an-item-not-on-the-menu",
   "entry_path": "prompts/place_order.prompt.md", "operation": "place_order",
   "input": {"customerName": "Lee", "pickupAt": "09:00",
             "items": [{"itemId": "pumpkin-spice", "size": "M", "quantity": 1}]},
   "expected_error": "unknown-item",
   "checks": [{"criterion_id": "AC1", "target": "error", "path": "/code", "op": "equals", "value": "unknown-item"}]}]}
```

A normal answer uses `"target": "result"`, for example `"path": "/totalCents", "op": "equals", "value": 900`.

### Rules

- 1 test file = 1 story. A story has only one test file. The test names its story in `story_path`.
- The test copies EVERY criterion of its story, word for word, into `criteria`. Each criterion needs at least
  one exact check (`equals`, `not_equals`, `one_of` or `count`). Else pdd or the server refuses it (`unchecked-criteria`).
- Each step names its prompt in `entry_path` and an `operation` from its interface. The `input` must match the
  `input_schema`. An error step has `expected_error` and one check on `error` `/code`.
- Check facts, not values that the model picks freely (IDs, wording). Schemas are closed (`additionalProperties: false`).
- Do not write `prose_sha256` yourself. Run `pdd check --fill-hash`. It fills the hash of each `draft` interface.
- The person approves. Keep `"status": "draft"` until the person says OK to the prompt and to each expected value.
  Then set `"status": "approved"`. If you change approved prose, set `draft` again, fill the hash, and ask again.
- One check sends the whole repo: all files that Git shows (tracked and new, not ignored). Max 10 MiB and 10,000 files.
- The server uses its own AI (gpt-6.1-sol). You need only a GitHub login (`gh auth status`). Cost is not a concern in the beta.

### Run a check

```sh
pdd check --fill-hash     # fill the hash of draft interfaces; sends nothing
pdd check                 # check every story
pdd check place-order     # check one story
pdd check --read          # show the last results again; sends nothing
```

pdd first checks the files on this computer. Then it runs lint on the server (0 AI calls). Then it sends one
check for each test, all at the same time. It waits, then shows one table with a report link for each story.

| Result | Exit | What it means | What to do next |
|---|---|---|---|
| passed | 0 | All checks passed. | Put the report links in the handoff. |
| failed | 1 | The program gave a different answer. pdd shows the criterion, path, expected and got. | Show the person the failed check. The person decides: change the prompt or the expected value. |
| refused | 4 | A file breaks a rule. Nothing was judged. pdd shows the code, the file and the field. | Fix the file. If the fix changes an expected value, ask the person first. |
| unknown | 3 | The result is not known yet. | Run `pdd check --read` later. Do not send it again. |
| not run | 5 | Sign-in, network, server busy, or no AI room on the server. | Run `gh auth status`. Or wait and run again. If it stays, tell the person. |
| command error | 2 | Wrong command or story name. | Run `pdd check --help`. |

### Try a story in the browser

`pdd try place-order` makes a Try link and opens it in the browser. The person uses the program by hand.
Each action uses AI calls. The link ends after 24 hours, or with `pdd try --stop place-order`. Make one only when the person asks.

### Never do these things

- Never change a test, an expected value or a prompt to make a failed check pass. Report the failure. The person decides.
- Never set `"status": "approved"` without the person's OK. Never edit `prose_sha256` by hand.
- Never send a check again when its result is unknown. Use `pdd check --read`. Never call the server API yourself.
- Anyone with a link can open it. Put report links only in the handoff and the run status. Never write a Try link into a file, PR, issue or chat.
- Never put secrets in the repo: pdd sends every file that Git shows. Never use another person's GitHub login.
