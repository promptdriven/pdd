# Runbook: Running pdd test, pdd simulate, and Troubleshooting

> Part of [RUNBOOK.md](../RUNBOOK.md) — see the router table in `../RUNBOOK.md` for other `§N` sections.

## 11. `pdd test`

`pdd test --fill-hash` fills the hash of draft prompts. `pdd test` checks discovered tests, reusing unchanged passing Stories from `.pdd/cache/test/`. Use `--lf` for last failures, `--cache-clear` to clear the cache, or `--retry` to retry confirmed unstarted checks in a saved batch.
`pdd test place-order` checks one story. `pdd test --read` reads the last results again. `--fill-hash` sends nothing. A saved `--read` may continue original checks held for lint after it passes, using identical source, owner and call ceilings; other reads send nothing.
Do not run `pdd lint` immediately before `pdd test`: test includes interpreter lint (0 AI calls). Run `pdd test --fill-hash && pdd test --files STORY && pdd test STORY` in one shell call (omit STORY twice for all Stories). Use standalone lint for admission diagnostics alone. Exit 0 means finished and passed; queued/running lint exits 3 with its saved read command. Never import pdd's source.
`pdd lint [STORY…]` sends the files to the server's lint only. It makes no AI call, and it prints every problem
the server finds.
pdd checks the files on this computer first. Then it sends checks for tests without a reusable pass. It shows one table (story, test,
result, checks, time), the AI calls and a report link for each test. Anyone with a report link can open it.
A failed check shows the criterion, the path, the expected value and the answer: `AC1  result /totalCents  expected 899, got 900`.
The report preview shows the first 256 characters of a longer string followed by `…`. The check still compares
the full value exactly. Preview clipping and sensitive-value redaction do not shorten the value being checked.
A draft prompt is checked too. Its row and its report say DRAFT. A DRAFT pass is not an approval.
The `Prompt tests` line's total AI calls already includes automatic reruns reported by the server. For example,
`5 AI calls (2 for reruns)` means 5 total, of which 2 were for reruns; never add the rerun share again.
For a failed step, pdd prints at most one `Rerun:` verdict:

- `Rerun: failed 3 of 3 (stable). A recheck of the same files will not help.` means the failure repeated consistently.
- `Rerun: failed 1 of 3 (unstable). Make the rule in the prompt firmer.` means the answers varied.
- `Rerun: passed M of M reruns.` means all reported reruns passed; the original failed check still needs investigation.
- `Rerun: skipped (<reason>).` means the runtime skipped diagnosis, for example `more-than-3-failed-steps` or `budget`. A skipped or unavailable diagnosis, including a single run, supplies no stability verdict. A refusal is not a failed expectation and has no verdict.

`pdd test` and saved-batch `pdd test --read BATCH` wait until every Story ends in every shell, with
`Still running: …` on stderr every 30 s. Use the shell tool's longest timeout or a background task that notifies
on exit (Claude Code: `run_in_background`; Codex: a long `timeout_ms`). `--timeout MIN` sets an explicit limit.
pdd prints the recovery `--read` command before the first check. If the tool stops pdd, run that command once
to keep waiting on the saved batch. Never poll every minute or send the same check again.

**Maintenance.** During announced maintenance pdd prints the end time and the reason (`The interpreter is in
maintenance until 08:52 UTC (…). pdd waits, then continues.`). Then it waits and sends the check. In your own session,
let it wait. Do not cut the wait short: no Ctrl-C, no `timeout` command and no short `--timeout`. A stopped wait sends
nothing and gives no verdict, and nobody else sends the check again. An Autopilot core job does not wait: it follows
§15 "Autopilot core jobs".

Before `pdd test` or `pdd simulate`, tell the person in one line what you run and that it can take a few minutes. pdd prints
a progress line on stderr before each slow step (lint, upload, the queue, the simulation setup). When it fails, it says what
failed, the real reason and what to do next: pass that line on as it is.

| Exit | Result | What to do |
|---|---|---|
| 0 | passed | Put the one-line result in the PR (section 15). If it says DRAFT, offer a simulation. |
| 1 | failed | Find the cause first ("After a ✗" below). Fix only what the evidence shows. A person decides expected values. |
| 4 | refused | Nothing was judged (`no verdict ·`): a file breaks a rule, or the AI service failed. Read the reason and the next step under the line. When the reason names a file rule, fix that file (table below); for an AI-service cause, change no file. If a fix changes an expected value, ask the person. |
| 5 | not run | Sign-in, network, server busy or no AI room. Run `gh auth status`. Wait, then run again. If it stays, tell the person. |
| 3 | unknown or still running | Run `pdd test --read BATCH` once with a long shell timeout or exit notification; it waits until every Story ends. Never resend the check. |
| 2 | command error | Wrong command or story name. Run `pdd test --help`. |

**A failed check is a FAIL, also with no verdict.** One step with no answer (for example `graph-provider-failure`)
makes its Story `no verdict` (exit 3, 4 or 5). Other steps of the same check can still fail. When the line shows fewer
passed checks than the total (`no verdict · 10 of 13 criteria · 17/19 checks`), open the report and read each step.
A step that shows `expected X, got Y` is a failed check. Follow "After a ✗" for it, and report it as a FAIL, never as
`not run`. Only a check with no failed step is no verdict.

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
| The expected value may be wrong | The Story does not give this value, or gives another one | Stop. Ask the person: keep the value (you fix the prompt) or change the test. Give an example. In a normal run, write the proposed value and run `pdd workflow done check --summary "Prompt tests line"` again: pdd shows the change on the Story card for the person. |
| The Story is unclear | Two answers fit the Story | Stop. Ask the person to decide the rule in the Story. |
| The answer changes between runs | `Rerun: failed 1 of 3 (unstable)` | Make the rule in the prompt firmer. Do not fit the prompt to one answer. |
| No verdict | `no verdict ·` with an AI-service or limit cause, or `busy ·` when the remaining checks are busy. Exit 3, 4 or 5 can also hide a failed Story or a failed step: read each Story line and the report ("A failed check is a FAIL" above) | Tell the person, with pdd's next step. Change no file. Never send it again on your own. |

4. At most 2 fix rounds for the same ✗. Then stop, and tell the person what you tried.

- After a send timeout, pdd prints the `--read` command with the batch. Keep reading with `pdd test --read <batch>`. A slow job can show up 4 minutes later.
- A `possible numeric mismatch` is advisory. Confirm the quantities against the Story and prompt; retain a correct
  expected value. Section 4 explains scoped review rationales. The count of files sent that are not prompt, Story
  or test files is an informational note.

| Refusal | Usual cause | Fix |
|---|---|---|
| `graph-schema-…` | A schema breaks a rule of section 3. Local diagnostics give the rule and JSON Pointer | Check the named schema against section 3. |
| `invalid-input` | A step input breaks the input schema: `"7pm"`, or a tax rate as a number | Fix the input. pdd shows the field and the rule. |
| `story-criterion-mismatch` | A test criterion is not the story text: often curly quotes | Copy the story line exactly. |
| `unchecked-criteria` | No criterion has an exact check. One criterion with no exact check is `not checked`: the others run, but the Story is not a full pass | Add an exact check for each criterion. |
| `interface-stale` | The prose changed after the hash | Draft: run `--fill-hash`. Approved: set draft and fill the hash. In a normal run, a full check pass re-approves it at PR 1 (section 2); else ask again. |
| `repository-graph-catalog-error` | Too few AI calls left for a step | Run again with a higher `--max-calls`. |
| `graph-result-failure` | Often the prose calls a prompt more than `max_calls` | Make the prose and `max_calls` agree. |
| `run-admission-failed` | Nothing ran (0 AI calls). Often one step's worst case is bigger than `--max-calls` (section 10). Other causes give the same code with no reason | Raise `--max-calls` (at most 1000), or lower `max_calls` in the prompt's `calls`. The interface `limits` do not help. If it stays, tell the person. |
| `invalid-context` | `context` is not a list of `{"prompt_path", "paths"}` rows, for example a text note (section 2). | Fix the rows, or use `[]`. |
| `graph-provider-failure` | The AI service failed. No verdict: pdd prints `no verdict ·` (✗ only when another check failed, in this Story or another Story) | Tell the person, with its AI calls. The person may send it again. Never send it again on your own. |
| `graph-uncertain-child-dispatch` | One AI call did not answer. No verdict. Your test is fine | Same as `graph-provider-failure`. |

## 12. `pdd simulate` and Save as test

`pdd simulate place-order` makes a Simulator link and opens it in the browser. Opening costs 0 AI calls. While it works (about a minute), pdd
prints a progress line on stderr for each step. It ends with a line such as
`Try ready for "Place a coffee order": <link> (open in your browser). It ends in 24 hours, …`. To stop it before that, run `pdd simulate --stop place-order`.
- A draft prompt can be tried. The person tries it before they approve. Show the Simulator link only to the person.
  Never write it into a file, PR, issue or shared channel: anyone with the link can use it.
- Ask the person: "Did it do what you expect?" Wait for the answer before you open PR 1. If the person is not at this
  computer, run `pdd simulate <story> --no-open` and give the link in the chat.
- A simulation needs at least the worst case of its biggest operation, plus 1. For `checkout`: 3 + 1 = 4 AI calls.
  An action that fails with `session-action-failed` at 0 AI calls means the calls ran out: run `pdd simulate --new <story>`.
- In a simulation, the same input again is answered from the cache, at 0 AI calls. An error answer is not cached.
- A simulation pauses after 15 minutes with no clicks. `pdd simulate <story>` reopens it at 0 AI calls. It does not send changed
  files or a new app map: for that, run `pdd simulate <story> --new`. Connecting Ask your agent or a CLI/HTTP door requires matching uploaded prompts; if a prompt changed, start a fresh simulation with `--new`.

**Save as test.** Only the person saves a case. Never save one yourself. pdd adds each saved case as a new step to the
story's test file and prints `added to tests/<file> as step <id>`. It makes a new file only when the story has none.
- The Simulator may say "Save this file in your project as `tests/<name>.json`" and warn about unchecked criteria.
  Ignore that. Do not make a second file: `pdd simulate` adds the case to the story's test file.
- With terminal stdout, `pdd simulate` connects Ask your agent, keeps waiting and adds saved cases as they come. `--no-wait` skips the connection.
- When you (an agent) run `pdd simulate`, it reads the saved cases once and returns, so it never blocks you. After the person
  says "I saved some cases", run `pdd simulate <story>` again to add them. An explicit `--agent NAME` connects even without a terminal and waits until Ctrl-C. Keep its private owner chat link out of shared messages.
Then make sure that every criterion still has a check, and run `pdd test <story>`.

## 16. Known limits today

- The appearance-context reader searches `Appearance`, `Appearance context` and `Dependencies` sections.
  It selects at most four views, with **64 KiB total SVG bytes** across those views, and records omitted paths.
  Required omitted context leaves the affected use incomplete. The mockup rendering selector searches only
  `Appearance` and `Appearance context`; its 256 KiB per-SVG safety cap in section 13 is separate.
- `validate_svg` checks SVG safety and structure. It does not establish the whole authoring contract, including
  required title/description, fidelity, ownership, comparator or tolerances. The mockup renderer reads fidelity
  from its appearance sections; absent or unrecognized fidelity remains `unspecified`, not `measured`.
- The appearance-context instruction currently treats sample text as illustrative even when the contract declares
  a comparison-reference state. This is a support gap. Keep the reference's required values and comparison checks;
  do not silently weaken them or claim this route proves them.

- The report page drops line breaks in strings. The check itself is exact: `"Added #1: Buy milk"` fails against
  `"Added #1: Buy milk\n"`. If expected and got look the same, look for a `\n`.
- Some refusals give no reason ("See the reported reason"). Use the refusal table in section 11.
- The report page says "Run in your signed-in terminal: `pdd replay …`". That command does not exist yet.
- In a simulation, the action that uses the last AI calls may not show its answer. The page says "This Try has ended".
- The Simulator says "1 AI call each". A step with saved data or a prompt call uses 2 to 3.

## 19. Use a simulation from your terminal or curl

`pdd simulate STORY --cli` prints a shim path and a PATH line. Startup and every command show a `Try AI usage` line on stderr: calls for the command, used/remaining in this session and its cap. Unknown counters stay unknown; this is separate from account/tester allowance. Copy the PATH line, then run the program normally.
`--shell` opens bash or zsh with that PATH. Each command uses your gh login and the same simulation's saved data.
`pdd simulate --save-last` appends the last command and its observed result to the original test file; review the
recorded expectation and its saved-data setup. `pdd simulate --stop STORY` stops the session. A wrapper error prints
**pdd:** on stderr and exits 125; program errors preserve the program's other exit codes.

`pdd simulate STORY --serve 8080` exposes named HTTP routes at `http://127.0.0.1:8080`. A prompt names an inbound
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
route returns 404 without an AI call. Interpreter or wrapper trouble returns 502 with a plain **pdd:** reason.
The listener binds only to loopback and accepts browser requests only from its own origin. Ctrl-C closes the
local server while the simulation keeps its data. Use curl or fetch for API routes; browser page, image, script and
stylesheet loads cannot spend calls through an API route.

When the Story has an app map, open `http://127.0.0.1:8080/` for the actual Screen. If it has not been drawn,
click **Open the app**; opening and taps use the same simulation budget and saved data. Loading the page alone uses
no AI call. The Screen reuses the hosted renderer, styles and declared click/form/key targets. It keeps an action
ID before sending and reads that same ID after a lost reply or reload; it never sends the action twice. Unknown
outcomes block new taps until recovered. Screen-only Stories need no named HTTP route; startup says **Screen only (no named HTTP routes)**.
If a saved simulation has no app map, use the printed `--new --app-map PATH` command to start one with the selected map.
A Story with neither an app map nor named routes gets a plain message describing both options. An app map reserves
GET/HEAD `/` and `/__pdd/screen/`; move conflicting named routes. Credentials stay in pdd, outside the page.
