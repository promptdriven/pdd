# Runtime client

Own `src/runtime-client.mjs`. Export `runCheck({words, options, cwd}, ports)` and `runTry({words, options, cwd}, ports)`. Each returns an exit code. These commands and the Try MCP tools call the PDD runtime with the person's `gh` login.

## Setup

- Repo root = `git rev-parse --show-toplevel` (a worktree is its own root). No Git repo: exit 2.
- The runtime address is one setting: `PDD_RUNTIME_URL`, else the exported constant `DEFAULT_RUNTIME_URL` in this module. Fixed immutable report links in RUNBOOK evidence are not configuration. No other code, prompt, test or doc names the runtime configuration address; tests use the override or import the constant. It must be an HTTPS origin with no user, password, path, query or fragment. Only for local tests, `http://` is allowed for `127.0.0.1`, `localhost` and `[::1]`. Else exit 2.
- `PDD_STATE_DIR`, default `~/.pdd/runtime`. Refuse a state folder inside the repo (exit 2).
- Ports (tests inject them): `env`, `stdout`, `stderr`, `fetch`, `gh(args)`, `now`, `randomUUID`, `sleep`, `onInterrupt`, `openUrl`, `pollMs`, `postMs`, `interactive` (stdin and stdout are both terminals). Read the environment only from `env`.

## Sign-in

- Token = `gh auth token`, in memory only: never in files, logs, argv, URLs or error text. No `gh`: exit 5, `Install the GitHub CLI, then run gh auth login`. Empty: exit 5, `Run gh auth login`.
- `gh api user --jq '.login + " " + (.id|tostring)'` once per batch; save the login and the user ID.
- Every call sends `Authorization: Bearer <token>` with TLS on and `redirect: 'manual'`.

## `pdd check`

Modes: `--fill-hash` takes no other option or STORY and makes no network call. `--files [STORY...] [--app-map PATH]` prints the exact selected upload manifest, each file size and total bytes, with no network or sign-in. Normalize STORY paths as for a check. Use the same selection as Check, lint and Try: the selected tests and their dependency closure, optional includes and the chosen app map, as owned by [source capture](runtime-preflight.prompt.md#source-capture). Check, lint and the default file preview do not use an app map. `--app-map` is accepted on Check only with `--files`, to preview the map used by a Try (including a default Try map named explicitly). Keep original test paths for Try seeds and saved cases. `--lint [STORY...] [--json] [--timeout MIN]` runs local SVG layout advice, then the server's lint, `POST /v1/lint` (0 AI calls), on the captured files, sets `complete: true` in its lint request, and sends no checks. Only explicit `--lint` requests complete diagnostics; the preliminary lint before Check or Try retains its existing request without `complete`. Apart from the SVG advisory, locally it runs only discovery and the privacy and capture checks (secret names, links, size and file limits), not the local copy of the engine rules (P1-P10, schema rules). It prints every problem the server reports, all at once (each `refused_prompts` entry: code, path, section, message; and each reached prompt that is not approved or a current draft, with the plain hints), one line per selected test (`passes lint` or `refused: <codes>`), and `Lint: N of M tests pass. 0 AI calls. No checks were sent.`. Exit 0 only when lint finished and passed for every selected test, 4 on lint refusals, 5 for not run, not invited or update required, and 3 while queued/running or unknown. A pending explicit lint retains its batch and prints its GET-only read command; sends no checks or Try. `--json` gives `{batch, repo, exit_code, lint_state, summary_line, problems, rows, warnings}`. Normal `pdd check` keeps its local preflight for now. `--read [BATCH|CALL_ID] [--json] [--timeout MIN]` reads saved batch results (and may dispatch original held checks under saved-lint continuation below) or an owner-scoped call by UUID. Hidden `--request UUID` reads one run with GET only. A wrong mix is exit 2.

### Local drawing checks

`--lint --local [STORY...] [--json]` runs only [SVG layout lint](svg-layout.prompt.md), with no runtime, network, token lookup, state-directory access or AI call. With no Story, inspect every Git-visible prompt, including prompts without a Runtime interface or tests. With Story words, use ordinary Story selection and the selected source dependency closure to select prompts; unknown selection is exit 2. Do not run engine P1–P10 or require an approved interface for this advisory. Its warnings never change exit 0. Print every warning and `SVG layout lint: N warnings. 0 AI calls. No checks were sent.`; JSON is `{repo, exit_code:0, warnings, summary_line}`. An actual repository/discovery failure is exit 2. `--local` requires `--lint` and mixes only with `--json` and Story words.

Ordinary `--lint` runs the same advisory on its selected captured prompts before sign-in/server work; merge its warnings into the existing text/JSON warnings without changing server lint semantics, rows, refusal rules, request shapes or call counts. Warning-only SVG differences do not become server refusals.

`--screen URL --drawing PATH [--json]` is a separate local Check mode with no Story operand, gh sign-in, runtime call, saved batch or AI call. Reject all other options/modes, an orphan `--drawing`, or a missing drawing option with exit 2 before side effects. Call [screen comparison](screen-compare.prompt.md) with `cwd`, URL and drawing path; pass `PDD_CHROME_PATH` from the injected environment when present. Text prints its `Screen vs drawing` Markdown table and summary, JSON prints the returned report plus `exit_code`. Exit 0 when all parts pass, 1 for a comparison failure, 2 for invalid input and 5 for unavailable browser, navigation or execution failure. An error must not print a passing table. Keep stdout valid JSON in JSON mode and diagnostics on stderr. These local modes return before runtime address/state/authentication setup.

For explicit complete lint, print every canonical diagnostic from `result.problems` (or the kept report's problems on older servers), preserving file, section, severity, JSON pointer and plain reason/fix. Merge legacy `program.refused_prompts` without duplicating the same code/file/section. A selected test's confirmed `result.tests` refusal also refuses that row, including Story/criterion mismatches even when prompt admission passed. Unselected tests or diagnostics remain visible without overriding selected rows. Preserve unknown and transport rules; complete lint is zero AI calls, never a check.

For lint-only JSON, `lint_state` summarizes the selected tests after the same reached-prompt judgment as their rows and exit code: `passed` when every selected row passes (exit 0), otherwise `refused` (exit 4). Never substitute the raw overall server job state for this selected result. Keep every returned diagnostic in `problems`, including an unselected dependency refusal; reporting it does not silently change a passing selected row. Unknown/not-run/transport handling stays as specified below.

Order:
1. [Preflight](runtime-preflight.prompt.md), scoped capture and sign-in. Nothing is sent yet. If every selected test is refused locally, print the result and exit 4 with no sign-in. The result warnings include the preflight warning about source files that two prompts name. Before a check of ALL stories (no STORY word), print to stderr `Checking all N stories: about A AI calls (at most M).`: A estimates declared work for each step: one entry execution, one use of each declared saved-data resource operation, and prompt-call max_calls multiplied by the target prompt estimate (including its resource operations and calls); cut dependency cycles rather than recursing forever. Conditional operations may use fewer calls. Bound the estimate by the unchanged hard cap; M = the sum of the tests' `max_calls` (cli 12b).
2. Batch ID `YYYYMMDD-HHMMSS-xxxx` (local time). Allocate one new `crypto.randomUUID()` for lint at batch creation and write `batch.json`. Allocate each test's first check UUID only at its first authorized dispatch after the applicable dispatch gates; pending lint allocates no check UUID. Print to stderr `If pdd stops, read the results with: pdd check --read <batch>` after lint passes and right before the first check POST, and again at the end of an exit 3. A pending lint also has a saved result to read: name its batch when the wait limit ends.
3. Lint: write `<id>.posted` (exclusive create), then POST `/v1/lint` multipart (`request` = `{requestId, source_sha256}` (plus `complete: true` only for explicit `--lint`), no `paths`; `source` = the tar). Read until terminal within the caller wait defined below; there is no independent 120-second lint cap. Judge only the prompts that the tests reach (step `entry_path` and their `calls` targets): a prompt in `result.report.program.refused_prompts`, or with `admission_state` neither `approved` nor `draft`, refuses each test that reaches it. A reached `draft` marks the row as a draft. A lint answer with no program report is a refusal when the state is `refused` with refusals, else lint is unknown: exit 3, no checks sent.
4. Checks: validate an explicit --max-calls as a whole number from1 through1000 before sign-in, capture or network effects, including direct runCheck callers. For each test write `<id>.posted`, then POST `/v1/check` with `{requestId, source_sha256, scenario: <test path>, max_calls}` and the same tar. `max_calls` = `--max-calls` or the preflight default (12 for each step, 18 to 1000). Each remote lint, check and new Try setup uses the shared local admission contract below. Hold remaining tests locally; do not reserve a batch slot while its child jobs wait for slots. POST timeout is the earlier 90 s and remaining command budget.
5. Read: GET `/v1/runs/<id>` for each open row every 2 s (at most 8 GETs at a time) until all rows end or the time limit, counted from the start of remote admission, including local-slot, maintenance and capacity waiting, ends. The limit depends on who waits. A person (`interactive`) has no limit. An agent (no terminal) waits at most 90 s, below the 2-minute default limit of Claude Code's shell tool. `--timeout MIN` overrides both. `batch.json` keeps the limit as `timeout_min` (1.5 for 90 s, null for none). While rows are open, in both modes, print ONE progress line to stderr every 30 s after the checks are sent, so an agent that is cut off still has output: `Still running: 2 of 3 Stories done · 14 AI calls so far · 4 min`. A Story is done when all its rows have ended; `Story` when there is one; the AI calls are the sum of the known `usage.calls` of all rows, the running ones too; the time is since the checks were sent, `N s` under a minute, else whole minutes. Save each answer as `<id>.json`. Then print the [output](runtime-output.prompt.md), write `summary.json` and return the exit code.

| Answer to a POST | Row | Next step |
|---|---|---|
| 200/202 JSON, same `requestId` and `id`, right `command` | accepted | read it |
| 429 `server-full` with `dispatch: "not_started"` | waiting | a NEW request ID after `Retry-After` (else 5 s) within the caller deadline under confirmed capacity recovery below. Keep the old ID |
| 503 `check-queue-full` or `lint-queue-full`, with authoritative not-started admission | waiting | wait under the capacity rules below |
| 503 `maintenance`, confirmed not started | waiting | wait/recheck maintenance below |
| 429 without `dispatch: "not_started"` | not run | no new attempt |
| 503 JSON `pool-low-room`, `pool-copy-*`, `github-unavailable` | not run | no new attempt; show the server text |
| 503 text `The runtime opens soon.`, or 401 | not run | send no more POSTs; the gate text or `Run gh auth login` |
| any status with `code` `update-required` (top level or `error.code`) | not run | stop the batch before anything else is sent: the server's `message` as one plain line (else `Please update pdd: npm install -g github:promptdriven/pdd`), exit 5 (0.1.6: the server retires an old address) |
| 403 `not-invited` (top-level `code` or `error.code`, with `login` at the top level or in `error.details`) | not run | stop the batch: one plain line `Your GitHub login <login> is not on the PDD runtime invite list yet. Ask the PDD team to add you.`, exit 5 (lint, checks, GETs, `pdd try` and its stop alike) |
| 403 `no-cloud-access` (top-level `code` or `error.code`; PDD Cloud sign-in did not approve this GitHub account) | not run | final at once, the same stop as `not-invited`: no GET, no wait, no new attempt. One plain line: the server's `message` (top level or `error.message`), else `Your GitHub account does not have PDD runtime access yet. Sign up at https://promptdriven.ai/login with GitHub; you can use the runtime when your account is approved.`, exit 5 |
| 503 `cloud-unavailable` (top-level `code` or `error.code`; PDD Cloud could not confirm access) | not run | the same stop at once: no GET and no silent wait. One plain line `PDD Cloud could not confirm your access. Try again in a minute.` (not the server's text, which says that pdd retries), exit 5. The person runs the same command again |
| 400, 413, 415, 422 JSON | refused | no new attempt; show code and message |
| timeout, lost connection, other 5xx, non-JSON, 409, wrong ID or command | unknown | GET that same ID only. Never POST again for this test in this batch, except a later confirmed service-restarted receipt below |
- Read the `code` and `message` of these answers from `error` first, else from the top level. A server may also send a top-level `update-required` for pdd 0.1.9 with `error.code` `no-cloud-access`: that is the access answer, not an update. An `update-required` with no `error.code`, or with `error.code` `update-required`, still says to update pdd.

- GET: 200 gives the state. 404 after a POST: keep reading, also when its body says `state: refused` with `job_created: false`; it is never a refusal. A row whose POST answer was lost (timeout, lost connection) is read by the same ID for 5 min after the loss, or until `--timeout` if that is later; then it is unknown. A lost lint answer is read the same way. The agent's 90 s default caps both reads: pdd then exits 3 and `--read` reads the same ID later. 410: unknown, `result expired`. 401: stop reading; open rows stay open (exit 3) and pdd prints `Run gh auth login`. A wrong ID or command: unknown. Server `state: unknown`: show its `why`.
- A check that pdd proves it never posted has 0 AI calls, including checks held behind an unknown/unfinished lint or stopped before sending. Keep lint uncertainty and the existing exit code; lint failure does not imply a submitted check. Persist this proof and repair older `--read` rows with no check request IDs. Mark usage unknown when a check is about to be posted; a lost or incompletely accounted server run stays unknown. Never replace server `usage.calls: "unknown"` with report `provider_calls: 0` when accounting is incomplete.
- At the time limit: open rows stay `queued`/`running` (exit 3; the jobs keep running on the server); waiting rows are not run (exit 5, `The runtime stayed busy until the timeout.`). After the table, pdd prints to stderr `Still running. Read the results later with: pdd check --read <batch>` in place of the `If pdd stops` line. `Retry-After` is whole seconds from 1 to 300; no header means 5 s.
- A row is marked `sending` before its POST. If pdd was killed, `--read` reads every posted row by its ID (a posted row with no answer is unknown, exit 3) and calls a row with no request ID not run.
- A server refusal `invalid-input` gets the local P9 rule as its hint. A server `interface-stale` on `steps[N]` gets the P7 hint. A server `interface-unapproved` for a draft row gets the message `The server does not run draft prompts yet. Approve the prompt first, or wait for the server update.` (exit 4), until the server runs drafts.
- Save `engine_sha` from each answer. The local rules match engine `eae2202a68d00ab762fcbbf1eba0d8607a132a15` (checked on Oct 27: the rules copied from 7b03d3ea are the same there). Warn only when the server's sha is another engine: it is not this sha and not a prefix of it with at least 7 hex digits (case does not matter). The warning: `Warning: the runtime engine is <first 12 of its sha>, but pdd's local checks copy engine eae2202a68d0. The engine stays the judge.` Show it at most once a day for each engine sha (a stamp in `$PDD_STATE_DIR/engine-warnings.json`).
- Ctrl-C after `batch.json` exists: stop all calls, keep the state, print the `--read` line, exit 3. A waiting row is then not run: `pdd stopped while the runtime was busy.`
- `--read`: the batch in BATCH, else the last batch of this repo. Use the saved origin. A different gh login: exit 5, `These runs belong to <login>. Run: gh auth switch -u <login>`. One GET for each open row, saved JSON for ended rows. It never makes a request ID or POSTs except saved-lint continuation and confirmed restart recovery below.


## Check admission and confirmed capacity recovery

A terminal same-ID `check` refusal is busy, not a test problem, when it is a queue/capacity/server-full refusal and proves no execution: `usage.calls` is exactly0, no check was evaluated, accounting is not incomplete, and the report says `dispatch:"not_started"` (the known check-queue-timeout contract also guarantees that signal). An explicitly unknown job or lost/wrong-ID response never qualifies. Read raw `result.report.refusal` as well as `result.refusals`; keep every ID and raw answer, including direct admission receipts and the absolute retry-after deadline. Direct check-queue-full/server-full backpressure also needs authoritative not-started admission. Do not retry invalid-source refusals or any request with executed checks, positive/unknown calls, or incomplete accounting.

For confirmed unstarted capacity, wait before a fresh ID using Retry-After, else positive details.retry_after (bound1..300seconds, default5). There is no attempt-count ceiling for confirmed admission backpressure; keep the existing command/agent deadline; honor interruption before waiting, allocating an ID or POSTing. Print a busy progress line and keep reading other submitted jobs. Never duplicate a queued/running/lost job. For an accepted queued job, keep its ID and GET it; when supplied, display queue.ahead, queue.slots_in_use and queue.slots on stderr: `Queued on the runtime: 5 ahead, 8 of 8 slots busy. Your test is fine.` Never resubmit an accepted queued/running job. Missing aggregate fields do not authorize guessed counts or change admission.

When time runs out, show busy/not-run with zero calls and plain advice that no checks ran; do not display the server's source-repair Fix text. Preserve passed and running results. Hold tests with no check POST as zero-call not-run, never a failed assertion. `--read` only reads the old IDs; a terminal capacity receipt becomes busy/not-run without posting. JSON distinguishes `busy` and `can_retry`, and text offers `pdd check --retry BATCH` for eligible rows.

`pdd check --retry BATCH [--json] [--details] [--timeout MIN]` is explicit recovery for that batch only. Check owner login and repository, refresh prior IDs, recapture the original selected source and require the exact saved source SHA before any POST. Retry only confirmed unstarted capacity rows or locally held eligible rows with no POST. Keep all earlier IDs/answers, completed rows, running/unknown rows, original per-test caps and original source identity; never reset/re-execute them. Reuse confirmed lint for identical source. A changed capture, missing proof, unresolved lint or expired/unverifiable receipt cannot authorize a retry; explain how to start a fresh selected check. Honor the saved retry-after deadline across recovery invocations. Each recovery invocation gets its own finite caller wait (including refreshing prior IDs), with no admission-attempt ceiling. `--read` remains GET-only except saved-lint continuation and confirmed restart recovery below. No other check-mode options mix with --retry except json/details/timeout, and it takes no Story words.

## Retry confirmed lint capacity refusals

For Check's preflight, explicit `--lint`, and Try, a confirmed terminal lint refusal
`lint-queue-timeout` with literal `details.retryable: true` is busy, never unknown or a prompt
fault. Read that signal from `result.report.refusal` or `result.refusals`. A direct503
`lint-queue-full` with the same literal flag is also a confirmed capacity refusal. Check admission uses its separate no-execution proof above. Never apply
this lint exception to a paid Try action, a wrong-ID reply, a nonretryable refusal or a lost result.

Retry confirmed busy lint replies until the caller deadline, with no attempt-count ceiling and a fresh saved request ID
and the same captured archive/options each time. Honor Retry-After first, else positive numeric details.retry_after in
seconds (bound1..300, default5), before retrying. Print `The server is busy. Waiting for a lint
slot…` before the wait. No attempt or wait starts after interruption or the total lint deadline:
the caller deadline. Check (including standalone remote lint) keeps its 90-second agent default,
unlimited interactive wait and explicit --timeout override; Try keeps its existing total 5-minute
setup allowance and 90-second agent default, with no independent 120-second lint cap. Bound each lint HTTP request/read by the remaining wait.
A lost reply still reads only that ID; it may retry only after that read confirms the retryable
terminal capacity refusal. Do not submit checks or create a Try until lint succeeds.

When the caller wait ends, return not-run (exit5; door wrappers retain their125 contract),
0check AI calls, and plain advice that the server stayed busy, no checks ran, and the person
can run the same command again later. Preserve every prior ID/answer. Unknown outcomes retain
the existing read-only recovery and unknown wording; do not relabel them as safe capacity.

## Lint still running when the wait ends

A matching lint job whose last confirmed state is `queued` or `running` is pending,
not an unknown result or a capacity refusal. Keep the command/90-second agent limit;
queue time, retry backoff and actual lint work share that budget. Save the last lint ID,
state and pending marker. Return exit 3 with a plain “Lint is still queued/running”
message, no check/Try dispatch, and zero check AI calls. Check and explicit lint name
`pdd check --read BATCH`; Try says no Try was created and lint uses no AI calls.
Lost replies, wrong IDs/commands and explicit unknown states retain unknown handling.

A saved read refreshes unresolved lint using only its latest saved ID, or uses a matching
saved terminal answer. Still-pending lint stays exit3; wrong-ID/command or unknown lint
cannot authorize dispatch. Clear stale unknown/pending wording on confirmed terminal lint;
report global and reached prompt refusals with their paths. Never rejudge posted check rows
or local preflight refusals. Terminal busy lint stays busy without resubmission.

### Continue the original saved Check

Only `--read BATCH` (including latest-batch reads) and `--retry BATCH` may continue a normal
Check held solely by pending lint. This lint-continuation exception never applies to UUID call reads, hidden
--request, standalone lint, Try, posted-job reads or capacity receipts; confirmed restart recovery is separately scoped below. New batches save
explicit normal-Check versus lint-only intent. For supported version 1 legacy records produced
by 0.1.9/0.1.10, recover normal-Check intent only when every held row has its valid original
max_calls (1..1000), positive integer criteria_total and consistent authored steps. Require
producer evidence of an unsent lint-held row: pending-lint evidence, prior unknown-lint
`not_run` evidence, or the known already-read state with phase `lint`, state `not_run`,
no check request IDs and note.code `lint-finished`. The latter is written by the
legacy reader after terminal lint clears its pending/unknown markers. Each evidence form
requires a matching passed lint and all owner, repository, source and exclusive-dispatch
guards below, no check IDs and no existing dispatch claim for the held row. Establish
zero check calls from this known never-posted producer state: supported legacy batch
serialization omits row.calls, so its absence is allowed here. If call evidence is
present, require confirmed zero; positive, unknown or incomplete call evidence refuses
continuation. This does not infer zero for posted, claimed or unknown jobs, and no
evidence form independently authorizes a paid check. These producer fields distinguish
Check from standalone lint, which omits max_calls and criteria_total. Reject missing, contradictory or ambiguous intent with a plain explanation;
never infer paid intent from a passing lint or Story path alone.

Before any new ID, authenticate the saved owner, use the saved runtime origin (never redirect to a changed environment setting), require the saved repository,
recapture exactly the saved selected test paths and require the saved source SHA. Require a
matching terminal passed lint with no selected/global refusal, valid saved per-test call ceilings,
and proof that each eligible row was held solely for lint and has never had a check POST.
A changed capture, unresolved proof or interruption sends nothing. Reuse the completed lint:
no new lint or redundant lint upload; each check retains its required source multipart from the recaptured identical archive. Preserve original batch/source, selection, call ceilings, all
prior IDs and answers, completed/running/lost/unknown jobs. An unsent row has zero check calls;
posted or incompletely accounted usage never becomes zero by inference.

Each continuation gets a fresh finite wait: --timeout MIN when supplied, otherwise 90 seconds,
including receipt refresh, source validation and check polling. Allocate the original held
row's first check ID only after these gates; save it and an exclusive dispatch claim before
POST. Concurrent/repeated reads or retries must share the claim and never duplicate paid
POSTs. A saved dispatch claim or uncertain/lost POST is read by the same ID, never replayed,
even after interruption. A completed read/retry only shows existing results. Existing capacity
recovery rules remain unchanged. Remote --lint and --read allow --timeout (1..120 minutes),
with no Story words on --read; standalone/local SVG lint combinations remain separate.

## Shared local admission and maintenance

Use [runtime slots](runtime-slots.prompt.md) for every remote lint, check and new Try setup before submission. This helper owns local fairness, leases and dead-owner reclamation. Preserve per-row exclusive dispatch claims and immutable .posted evidence: admission never authorizes a duplicate send. Register every allocated request ID on its reservation before POST; record terminal evidence before release. Polling ending, interruption or a lost reply does not end the runtime job: retain its reservation for later confirmation/reclamation. Capacity attempts proved unstarted may release/rejoin fairly; a batch holds no reservation while waiting for child jobs. Local Check modes and paid Try actions/open browser session lifetime take no setup slot.

Before each new submission, authenticate GET /v1/capacity at the configured/saved origin with the ordinary credential and redirect safeguards. Its aggregate response is `{slots:{check:{running,limit,waiting},lint:{running,limit,waiting}},tries:{open,limit,yours,per_account},maintenance:null|{until,reason}}`. These counts are progress, not a substitute for local exclusion or confirmed admission. HTTP 404 means this runtime lacks capacity: continue using admission replies. No other read failure invents permission or silently bypasses auth/cloud/update gates; retain the existing transport handling.

A valid future maintenance.until pauses new submission until that time, then rechecks capacity. Print `The runtime is in maintenance until 18:40 PT (deploy). pdd waits, then continues.` with the supplied time/reason rendered for the person. A confirmed not-started 503 maintenance receives the same waiting treatment, honoring Retry-After and rechecking capacity; an older runtime's 404 still allows later admission-code recovery. Invalid/past maintenance is not an indefinite pause. Do not reinterpret unrelated 503, cloud-unavailable or the legacy opens-soon gate as maintenance.

Local waiting, maintenance, HTTP, queue reads and all backoffs share the existing caller deadline: agent Check/lint 90 seconds, interactive Check/lint unlimited, explicit Check --timeout overrides, Try's existing five-minute setup allowance and 90-second agent lint wait. No new Try timeout flag. At the deadline or interrupt, allocate/send nothing further; keep pending receipts/reservations and valid JSON stdout, with progress only on stderr. A confirmed admission refusal needs no-execution evidence; positive/unknown usage, evaluated checks and incomplete accounting forbid capacity replay.

## One replacement after a confirmed runtime restart

Only a same-ID, correct-command terminal check receipt with state unknown and structured reason code service-restarted in result.refusals or result.report.refusal authorizes one automatic replacement for that original Story row. result.why is display text, never an authority inferred by matching message text. A generic unknown, lost POST, wrong ID/command, expired/unverifiable receipt or another reason never authorizes it. This exception can follow read-only same-ID recovery; the receipt, not an error message, authorizes dispatch.

Persist the consumed replacement allowance across reads/retries and capacity attempts. Before allocating the replacement UUID, require saved owner, repository, identical recaptured source and original per-row max_calls, a live caller wait and an exclusive per-row replacement claim. Overlapping readers cannot both send. Print `The runtime restarted during this check. pdd sends it again (1 of 1).` Keep both IDs, raw receipts and their known/unknown call accounting; do not reset usage or enlarge the row ceiling. Apply ordinary admission to the replacement. A second restarted receipt ends unknown with read/report advice, never a second replacement. UUID call reads and paid Try calls remain GET-only. A deadline-ended eligible replacement stays saved for guarded recovery; approval is never inferred.

## Shared contract advice

Every Check/lint/Try/file-preview capture, held-lint continuation, retry, restart
and workflow freshness recapture uses preflight's effective reference bytes.
Validate selected references before sign-in or upload, including explicit lint,
without adding local engine validation to explicit lint. Missing references send
nothing. Unused contracts are not added to the selected upload.

Only explicit remote `pdd check --lint` additionally compares selected prompt
schemas with the current local contract catalog, reading it with preflight
safe-file rules. Catalog-only reads do not extend the upload selection. Use the reference module's
comparison authority. Print differing copies with consumer/schema location,
canonical target, changed/missing/extra fields or constraints and a `$contract`
suggestion. Exact copies need no drift warning; ambiguous candidates warn and
skip. Merge this advice into existing warnings; it changes no server request,
check expectation, refusal or exit status. Ordinary Check's preliminary lint and
SVG-only `--lint --local` do not run this catalog comparison.

## Shared contract Check history

Export synchronous module function `readContractHistory({root,env})`, returning
`{stories,warnings}` without gh, network, slots, model calls or writes. Each story
row has `story_path`, `baseline` (`checked`, `not-checked`, `unavailable`),
`checked_at` (timestamp or null), `result_state` (`passed`, `failed` or null),
`files` (per-Story effective `{path,sha256}` rows)
and `references` (the resolver's provenance rows). Missing snapshots yield
`unavailable`, never fabricated values. Keep data private under existing state
permissions; no repository metadata file or new record-hash pins.

Save each actual terminal Check's source footprint and reference snapshots from
its submitted capture, individually for each Story, even in a multi-Story batch.
Advance the baseline only for an actual evaluated Check, never a refusal before
execution, pending/not-run/unknown receipt, standalone lint, Try or file preview.
Use the latest actual Check for that Story, retaining its real pass/fail result.
Reading a receipt later can establish that original Check, never substitute the
current files for its submitted snapshots. Missing legacy snapshots remain
unavailable until a new actual Check. Do not use unrelated rows' dependencies or
a whole batch SHA as the Story's freshness identity.

For equal original Check timestamps, prefer a real evaluated failed Check over
a passed Check. Resolve other equal-time/equal-result choices deterministically
without implying chronology. A strictly later original Check always wins.

New reference-backed Try records also retain uploaded effective prompt hashes
and the corresponding contract provenance. Apply the existing pinned-prompt
freshness promise to the expanded current prompt bytes before connected reuse,
doors or owner-tool access, so a contract-only prompt change requires `--new`.
Keep raw authored prompt hashes for compatibility. For legacy records, use the
existing raw-hash rule; if a currently referenced prompt lacks the matching
expanded snapshot, explain that its reference baseline is unavailable and ask for
`--new`. Do not compare the whole scenario/seed/world hash for this guard: an
existing Try deliberately keeps its original persistent world. Preserve Story
identity checks and all existing owner/origin/budget guards.

## State (outside the repo; folders 0700, files 0600; no tar and no token on disk)

```
$PDD_STATE_DIR/repos/<key>.json        last batch and open Try per test; key = first 16 hex of sha256(repo root realpath)
$PDD_STATE_DIR/batches/<batch>/batch.json   origin, root, HEAD, login, user ID, source_sha256, files, bytes, lint, rows
$PDD_STATE_DIR/batches/<batch>/<id>.posted  written before its POST; a second POST with this ID is impossible
$PDD_STATE_DIR/batches/<batch>/<id>.json    last server answer (holds the secret report link)
$PDD_STATE_DIR/batches/<batch>/summary.json the --json output
$PDD_STATE_DIR/tries/<id>.json             Try records
```

Request IDs appear only in state files and in `--json`.

## `pdd try`

A new Try requests a total session budget of400 calls, overridden by explicit `--max-calls N`.
Validate N as a positive whole safe integer from1 through1000 before sign-in, capture or network effects.
It cannot combine with --stop or --save-last. New multipart requests include max_calls.
A budget is a ceiling, not a charge. Report the owner's confirmed result.session.max_calls and
remaining_calls, never a guessed or requested value: `Try budget N calls; R remaining. You are charged
only for calls that run.` For browser mode this goes to stdout beside the ready link; for CLI/serve
setup it goes to stderr so command output stays lossless. Missing legacy metadata says the budget
is unavailable, without inventing a cap or refusing an otherwise valid link. For a newly created Try,
a different confirmed ceiling fails nonzero while retaining its receipt; do not open the link or a door
and imply that the requested ceiling was honored. An explicit budget whose confirmation is absent
also fails as unconfirmed. Default creation may show unavailable metadata for legacy compatibility.


Reusing a Try without an explicit budget keeps its current budget. An explicit budget is a total
ceiling, not extra calls. Raising must preserve session identity, saved data, actions, usage and expiry;
never lower a ceiling, refill spent calls or replace a world to satisfy a budget request. A request
no higher than its confirmed ceiling is a read-only no-op. An existing Try with no confirmed total
ceiling fails read-only before any reopen or budget mutation; never guess its budget. Budget reuse checks recorded origin and
GitHub login even outside door modes. Unknown or missing existing-session state keeps the receipt and
fails without creating a replacement unless the user explicitly supplies --new. Failed or uncertain
budget changes must not be reported as success; an unsupported raise fails before any paused-session reopen; no new dispatch after interruption. The runtime's
owner API binding for this raise is pending the planner's contract; do not invent a mutation path.

- STORY as for `pdd check`. No STORY and one test: use it. Many tests: list them, exit 2. Then preflight, capture and lint as for `pdd check`, for this one test.
- If `repos/<key>.json` has a Try for this test and GET says `result.session.state` `running` with a valid link, open that link again. For `paused`, validate the same-origin link, then explicitly send one authenticated JSON `{}` POST to `/v1/try/<id>/reopen`. Keep the same ID and original seed identity. Read that ID until its session is running before showing/opening the link. Restore consumes no AI calls, creates no new Try and keeps the original expiry and remaining allowance. A lost reopen answer is read by the same ID; never automatically repeat the POST. A busy/refused/missing reopen or unconfirmed restore keeps the record and returns nonzero with its reason and retry advice naming the exact authored test path, shell-quoted when needed; never print a paused link as ready. `--new` stops the paused Try and creates a new one through its normal route, without reopening it. Options that apply only to a new Try remain refused before reopening. After interruption, send nothing new. `--new`: stop the old Try first, then make a new one. A Try that ended (404, 410, failed, refused, unknown, session stopped or unknown) is forgotten, and a new Try is made: a new Try costs no AI calls. A Try that is still starting, or a GET with no answer, is exit 3 with no new Try, unless `--new` stops it first. A new Try whose setup ends `unknown` is forgotten too: `The Try setup did not finish on the server (its state is unknown; the server may have restarted). It used no AI calls. Run pdd try <story> to make a new Try.` (exit 3).
- After Ctrl-C, pdd sends nothing new: no POST starts after the interrupt.
- App map: `--app-map PATH`, else `app-map.json` at the repo root, else `app/app-map.json`. An app map is a Git-visible JSON object with `"schema_version": "prompt-runtime.app-map.v1"` and a nonempty `name` (the engine's first checks). A bad `--app-map` is exit 2 with the reason (`not a Git-visible file`, `not JSON`, wrong `schema_version`, no `name`) and `See RUNBOOK.md §13.`; a bad found file is skipped with a note. With an open Try, `--app-map` or `--tab` without `--new` is exit 2: they apply only to a new Try. POST `/v1/try` multipart `{requestId, source_sha256, seed: <test path>, app_map, tab}`: `app_map` only when there is one; `tab` = `--tab`, else `screen` with an app map, else `call`; `max_calls` is the explicit budget or400. Read until `state: passed`, `result.session.state: running` and a valid `result.url`: the origin's scheme and host, path `/s/<token>/`, no user or password. Else refused, not run or unknown, as for a check, with one exception.
- A Try setup that the server refuses (the POST or the job; runtime team, Oct 27) is not a check: no table and no `pdd check` advice, exit 4. Two plain lines: `The Try could not start: the app map was refused (<code>: <reason>).` and `Fix <app map path> (RUNBOOK §13), then run pdd try <story> --new.` It is the app map when one was sent and the code is `ambiguous-handler`, `template-reference-schema` or `app-map-*`, or the section names the app map. Else `the server refused it (…)` and `Fix what it names, then run pdd try <story> --new.`, with ` Details: <report link>` when there is one. Many refusals join with `; `; a refusal with a `where` (prompt-runtime #379) adds `; at <where>` after its reason. The reason is the server's `reason` (on each `result.refusals[]` item, or on `result.report.refusal` with the same code), else pdd's plain rule (`ambiguous-handler`: on one screen, all taps of one kind must match by the same key; `template-reference-schema`: a field that gets a value from the screen (`$ref`) must be a plain {"type": "string"}), else the engine message, else the server message unless it is the generic `The runtime refused this job…`. A server `fix` takes the place of pdd's fix words: `<fix> Then run pdd try <story> --new.` A Try that is ready but has an invalid link is exit 3 with one line and no table: `Try link refused: it points at <link origin>, not <configured address>. The server's address setting may be wrong; tell the PDD team.` (or `Try link refused: it is not a valid Try link. Tell the PDD team.` when the origin matches). pdd keeps its record so `pdd try --stop` can end it, a later `pdd try` says the same, and pdd never prints that link.
- A reused link says `It keeps its original 24-hour expiry; stop it with: pdd try --stop <story>`, so reopening never promises a fresh 24 hours.
- Open a newly created link with `open` (macOS) or `xdg-open` (Linux) and print the end line `Try ready for "<title>": <link> (open in your browser). It ends in 24 hours, or with: pdd try --stop <story>`. `--no-open`, or a failed open, prints `Try ready for "<title>": <link>` and then how to open it.
- `--stop [STORY]` finds the Try in the state record by story name, test path or test file name, so it works on a branch without the story (real-user issue 14). No STORY stops the one open Try; none or several is exit 2 with the open names. It sends DELETE `/v1/try/<id>` with the header `X-Request-Id: <new UUID>`; read the stop job until `passed`; then forget the Try. A DELETE answer 404 or 410 counts as stopped. A GET 404 or 410 on a recorded Try counts as ended. In both cases pdd deletes the record, so the next `pdd try` makes a new Try; the person never edits a state file.
- The note on other files prints once per command, in calm words, to stderr. `pdd check` folds it into its send line: `Lint passed. Sent 2 checks at 10:47:49: 11 files, 55 KB (4 are not prompt, story or test files; run \`pdd check --files\` to see them).` `pdd try` folds it into its start line: `Starting your Try: sending M files, SIZE (N are not prompt, story or test files; run \`pdd check --files\` to see them)…`. It is not a warning.
- Confirmed not-started 429 server-full or 503 check-queue-full/lint-queue-full during new Try setup waits under admission recovery within the existing setup allowance; accepted setup is read by its ID. Other 429 replies make no new attempt: exit 5 with the server's message, else `Too many Try links are open. Stop one with pdd try --stop`.
- Approvals from the Try page (#9, agreed fields): with the saved cases, pdd reads `GET /v1/try/<id>/approvals` (`{approvals: [{id, prompt_path, prose_sha256, requested_at, state}]}`). For each `pending` request in a person's terminal it uses [prompt approve](prompt-approve.prompt.md): the path must be a Git-visible `*.prompt.md` inside the repo (else declined), the request's `prose_sha256` must equal the local prose hash (else declined: `the prompt changed since you clicked Approve`), an approved and current prompt is done with no question, otherwise it shows the interface and asks the same y/n; one reader serves all questions. Then it sends `POST /v1/try/<id>/approvals/<request id>` with `{"state": "done" | "declined"}` (JSON). `tries/<id>.approvals.json` keeps each answer, so pdd never asks twice and resends only an answer whose POST failed. Without a terminal (an agent) pdd only prints `The Try page asks to approve <path>. A person answers it in a terminal: pdd try <story>` once and answers nothing. A missing endpoint (404) is skipped. Waiting needs both stdin and stdout to be terminals.
- Save as test: after the link is shown, pdd reads `GET /v1/try/<id>/tests` (`{tests: [{id, path, name, created, story_path, test}]}`, try-page DESIGN.md). For each saved case that it has not handled (`tries/<id>.tests.json` keeps the handled IDs), it appends the case's steps to the original authored test that seeded this Try when the saved story matches the seed's story, including when that Story has several test files. Keep this identity when reopening a Try. If that original test is missing or no longer belongs to the same story, refuse the import without choosing another test or creating a replacement. For another story, use its test file found by discovery. It keeps every other byte of the file (a one-line `steps` array gets a one-line step). Criterion IDs map by criterion text; a case with a criterion the file does not have is `not added` with the reason. A saved case is untrusted (anyone with the link can save one): its story must be a Git-visible `*.md` file in the repo with no `..`; an existing target must be a regular `*.json` file whose real path is inside the repo, whose top-level `schema_version` is `prompt-runtime.program-scenario.v1`, and that is not `package.json`, a lock or config file or a dot file; a new file goes only to `tests/<story slug>.json` (never a path from the server), created exclusively, and never when `tests/` is a symbolic link or resolves outside the repo. Each refusal prints `not added: <reason>` and writes nothing. Step IDs stay unique (`-2`, `-3`). Only a story with no test file gets a new file, `tests/<story>.json`. Print `added to tests/<file> as step <id>`. In a terminal (stdout is a TTY) pdd stays open and reads every 5 s until Ctrl-C or the Try ends; `--no-wait`, or no terminal (an agent), reads once and returns. A missing endpoint (404) prints `The runtime does not keep saved tests yet.` only while waiting. Exit 0 = link ready or stopped; other exit codes as for `pdd check`.

## Progress and error causes

pdd reports each slow upload, lint and Try setup step. Use the [progress helpers](runtime-output.prompt.md#progress-and-causes): one stderr line before each slow step and a tick line every 15 s while it waits; stdout keeps the result, so `--json` stays valid.
- Lint (before a check, a Try, the door modes and `--lint`): `Checking N files (SIZE) on the PDD runtime (lint, 0 AI calls)…`, then `Still checking the files: <in line | running>`.
- Try: `Stopping the old Try…` before `--new` stops one, `Stopping the Try for "<title>"…` for `--stop`, `Reopening your Try…` for a paused one, `Starting your Try: sending M files, SIZE…` right before the Try POST, then `Still starting your Try: <in line | running>`. Ticks of a check keep the `Still running:` line every 30 s.
- `--retry`: `Retrying N unstarted checks…`. `--read`: `Reading N results from the PDD runtime…` when it reads any from the server.
- `gh` sign-in is quick, so it prints no line; a failed `gh api user` names gh's first error line.
- A network error that proves the request never reached the server (address not found, connection refused, no route, TLS certificate refused) stops at once, exit 5, nothing else sent: `pdd could not reach the PDD runtime at <origin>: <reason> (<code>). Nothing was sent. Check your network and PDD_RUNTIME_URL, then run the command again.` A timeout or a lost answer keeps the one-shot rule: read the same request ID and never send it twice; the tick line names the reason while pdd reads again.
- HTTP 401: `The PDD runtime did not accept your GitHub login (HTTP 401). Run gh auth login, then run the command again.` Another unexpected status keeps the unknown state and adds the server's message: `The runtime answered HTTP 500: <message>.`

## Dependencies

- [References](contract-refs.prompt.md): required generation and verification
  context for canonical provenance and explicit-lint copy comparison.

- [Runtime slots](runtime-slots.prompt.md): required generation and verification context for shared local admission and jobs. Runtime listing binds its own files port; native process exclusion remains a native verification obligation.

- [Local bindings](runtime-bindings.prompt.md): required generation/runtime context for the local inventory helper.
- [SVG layout lint](svg-layout.prompt.md): required local advisory behavior for generation and tests.
- [Screen comparison](screen-compare.prompt.md): required browser comparison behavior for generation and tests.

[Agent configuration](agent-config.prompt.md) is required generation/runtime context for loading private named launchers before owner authentication.

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md). The [CLI](pdd-cli.prompt.md) calls `runCheck` and `runTry`.

## Terminal and HTTP doors

`runTry` also accepts `--cli`, `--shell` (only with --cli), `--serve [PORT]` (default 8080), and `--save-last`.
These modes share the ordinary Story selection, lint, upload, owner authentication and saved Try.
Reject incompatible modes before any network effect. A door reuses an open Try only at its recorded origin and
with its recorded GitHub login. --cli selects terminal on new sessions and delegates local launch behavior to
[Try doors](try-doors.prompt.md); --serve delegates to [HTTP doors](try-http.prompt.md), passing the selected local app-map path and invocation directory for missing-map recovery guidance only; the authenticated pinned model still decides Screen capability. Show no browser link and do not open the browser for these modes.

Export `runDoorCall(descriptor, input, ports={})`: descriptor identifies root, session ID, original runtime origin,
GitHub login, prompt and operation. Sign in again, require the original login, and send exactly one JSON owner call
with a fresh request ID. Save the ID before sending. A lost POST is recovered only by GET of that same ID;
never repeat a dispatch. Read queued/running calls for up to 15 minutes, returning the confirmed owner GET's result.program_result verbatim (the display report is sanitized). Read the owner GET even when POST is already complete; absent program_result is an incompatible-server error.
Refusals, unknown outcomes, stopped sessions and invalid replies throw a plain error; redact credentials.
Return normalized usage alongside the confirmed result (usage.calls and result.report.remaining_calls; unknown when absent/invalid). A refusal carries its known usage on the thrown error for wrappers. Never dispatch again to obtain usage. No wrapper progress or report text may enter a program's stdout; the door adapter owns the separate usage line on stderr. Session budgets and saved worlds belong
to the runtime. Preserve paused-session refusals; never silently create a new world during a command.

Export `saveDoorCase(root, saved)`, which applies the same safe append rules as a Try-page saved case, honoring
its original `path` when it is a discovered test of that Story. This lets --save-last write into the selected
original test even when another test covers the same Story. It must never create a replacement of that file.

For CLI or HTTP setup every preflight, lint or runtime refusal is a wrapper failure on stderr prefixed `pdd try:`
and exits 125. Argument combinations alone may exit 2. Session records capture hashes of uploaded prompt files
and the login. Before showing or opening a reused --serve door, compare every recorded uploaded prompt hash with the local files; missing hashes, removed files or changed bytes refuse with a --new hint before model metadata, a listener or a call. CLI doors apply the same source-identity rule. --new stops the old session first.
Door calls can provide a captured absolute gh executable path so a project shim named gh does not shadow sign-in. Preserve a stable PATH symlink when recording it; if that saved executable is gone, look up gh again using the launcher-safe PATH search.
A cancelled door call stops polling promptly and reports an unknown result if dispatch may have occurred. Never
resend it. Forward cancellation to polling waits so closing a local HTTP server cannot hang for the call deadline.
A door's lint can finish refused before producing a program report (for example lint-queue-timeout with
provider_calls=0 and dispatch=not_started). Preserve that confirmed refusal's plain reason on stderr/125;
do not mislabel it as an unknown result and do not send a Try. A later explicit setup may use a new lint ID.

Pass the captured source SHA into saved and printed check JSON, including saved reads, so a workflow can bind saved evidence to source without another execution.

## Ask your agent connection

Ordinary `pdd try STORY` connects the person's local agent through the owner-only [agent bridge](agent-chat.prompt.md) only when stdout is a terminal or `--agent` is explicitly supplied. Without a terminal and without --agent, print/open the shared Try link, collect saved cases once and return without loading agent configuration, discovering CLIs or connecting a bridge. An explicit --agent permits a background connection that stays running until Ctrl-C. --no-wait disables connection even with a terminal.
`--agent NAME` chooses a configured display name; builtin lowercase IDs remain aliases. Otherwise use the project's remembered name or discovery. Before sign-in or network in an ordinary connected Try, load private [agent definitions](agent-config.prompt.md), reject an empty list or unknown explicit name, and keep them in context.agentDefinitions for the bridge. Never upload these definitions. Skip this configuration read for ordinary non-terminal Try without --agent, --no-wait, door/stop/save-last modes and the explicit agentBridge:false compatibility test port. Use the same connection eligibility for configuration loading, owner/origin and pinned-prompt reuse checks, and bridge startup; door and explicit-budget guards remain independent.
`--no-wait` explicitly returns without a bridge; it cannot combine with --agent. Agent choice is
not valid with --stop, --save-last, --cli or --serve. Validate conflicts before sign-in/network.
Explicit budget reuse and connected agent reuse both require the recorded login and runtime origin; neither may weaken the other owner check. Reuse must match the authenticated login/runtime and pinned prompt hashes before connecting; a
changed prompt requires --new. Never expose a chat key to another owner's session or print it.
Open the bridge's owner URL in the browser while printing only the ordinary shared Try link. With --no-open or a failed browser open, also print the owner chat URL explicitly labeled private: it contains only a scoped chat capability in the fragment, never the GitHub/provider token.
Keep collecting saved tests and approval requests while connected; an agent terminal cannot approve
prompts. Ctrl-C cancels the agent/poll and disconnects chat, leaving the Try open. --no-wait retains
one-shot saved-test collection. An older runtime with no bridge gets a plain compatibility message
and the ordinary Try behavior. Other relay errors fail plainly, without a new Try or program call.
The injected `agentBridge` port may replace bridge setup in tests; production loads the generic
module. No user configuration, model, global agent settings or login is changed.

## Display a server step time limit

Use [runtime output step time limits](runtime-output.prompt.md#step-time-limits) for check answers, saved reads, Try setup refusals and terminal/HTTP door call refusals. Supply authored step IDs when available. Print its step name, reported minutes, stopped message and small-step advice instead of a failed expectation. Preserve unknown execution, IDs, calls and report links; never replay it automatically. A Try setup time refusal must be displayed before the generic unknown-setup path and must not claim zero AI calls when the receipt says otherwise. Door failures, including CLI/HTTP Try setup, keep wrapper exit125 and the same specific timeout guidance and known usage. The hosted Try page's own runtime action UI remains server-owned.

## Explain failed checks

Pass authored step IDs and short criterion text into runtime output. Preserve a failed check's runtime-contract `diagnosis`, and preserve the failed row's `why`, `who` and `next_step` for text and JSON only for failed state; use the first failed check diagnosis when the run-level fields are empty. The fallback is person-first: `A person decides expected values. The agent may propose a change, and never makes it.` For target `error` with actual `{"missing":true}`, display `got no error (a normal result)` only when the step has a result and no error, or diagnosis kind `no-error`/`needs-tool`; otherwise keep the missing object. Use the authored step ID when the report omits it.

For a connected Try guide, report each newly handled saved case’s id/name/Story/result through the optional private context.onAgentCaseSaved callback after addSavedCase returns. Only successful “added to …” outcomes mark guide memory saved; refusals remain refusals. The callback does not change file selection, criteria, append behavior or save authority, and never receives raw saved-test data. A callback exception cannot undo a saved case or prevent collection of later cases.

## Read one call and recover an interrupted command

A UUID operand to `--read` uses the authenticated owner `GET /v1/runs/<id>` ledger, including `command: call` Try commands as well as check requests; the hidden `--request` remains compatible. Validate the returned identity and command. Do not require a saved batch or POST, create a session, or repeat the operation. A saved call descriptor preserves its original origin and login; refuse a different login before reading. Unknown IDs, unavailable receipts and running calls remain unknown/pending with their exact read command, never successful. Existing batch and no-operand latest-batch reads retain their behavior.

For a confirmed terminal call, text prints its ID, state and complete `result.program_result` (including stdout, stderr and program exit code), known usage and report link. JSON exposes `request_id`, `command`, `state`, `program_result`, `calls`, `report_url` and `exit_code`; absent usage stays unknown. Passed call receipts exit 0 even when the program's own exit_code is nonzero; failed/refused/pending receipts retain check status accounting. Never reinterpret a program exit code as a transport outcome. Missing program_result on a passed call is an incompatible receipt, not invented empty output. Sanitize secrets without losing ordinary output line breaks.

Before dispatch, save the call UUID with origin/login/session metadata privately. Every uncertain dispatched CLI/HTTP door command (interruption, lost response, poll deadline or read failure) gives `pdd check --read <UUID>` in its error, preserving wrapper exit 125. A definitely unsent command has no recovery claim. Read the same UUID later to obtain the runtime's final result; do not promise that a GET resumes execution or releases held calls. The runtime owns execution and settlement.

## Selected module binding coverage

Use the [preflight binding inventory](runtime-preflight.prompt.md#module-binding-inventory) for normal checks, explicit lint and file previews. Carry its coverage in text and JSON, preserving selected Story scope and showing every unbound module with its reason and port attempt. Metadata validation problems are lint problems, including absent/blank unbound reasons and port attempts; explicit lint still sends zero checks and consumes zero AI calls. Local metadata errors can refuse before transport. Coverage never changes a runtime assertion or claims that bound means passed. A missing inventory is explicitly unavailable, not zero modules fully bound.
## Owner access for Try tools

Export `readTryOwner({cwd, story}={}, ports={})`. Resolve the Git root and discovered Story test using existing selection rules; no Story selects the sole open recorded test, otherwise the sole discovered test. When a Story name matches several test files, prefer its sole open recorded test; without that unique open selection, require an exact test path. Reject ambiguity, unknown Story, changed Story identity or changed/missing pinned prompt hashes before a door can run. Authenticate through the existing gh identity and require the saved Try's login. With no saved session, open through runTry with `--no-open` and `--no-wait`; then read its saved record. Read authenticated model metadata and current world from `/v1/try/ID/model` and `/v1/try/ID/state`. The latter returns `{world:...}`; failure leaves current data unavailable with a reason, never initial_world. Return `{root,test,record,model,data,data_error,actions}`. Model failures are actionable errors; a confirmed ended session can be opened once through runTry, preserving its existing unknown-outcome safeguards. Never automatically reopen after an unreachable read. Validate runtime origin before sending credentials.

New Try records pin the Story bytes as `story_sha256`; owner access rejects changed pinned Story bytes. Older records without this field retain their existing Story-path identity check. Return authenticated state action history as `actions` when available.

`saveDoorCase(root, saved, {isolated:true})` records a confirmed observed scenario separately instead of appending. Require the original discovered test/Story identity, an object `initial_world`, original simulation/context, criteria and recorded step. Write a collision-safe, no-overwrite regular `tests/<story>-try-<run-id>.json` inside the real repository; never follow symlinks. Identical existing content is a no-op, conflicting content is refused. Keep the original scenario bytes unchanged. The caller explains partial Story coverage; this operation does not waive runtime whole-Story admission rules.
New Try records retain `seed_scenario` as the original uploaded scenario; owner access returns that snapshot for judging, so local appended recorded cases cannot silently change expected values for an existing Try. Older records use their current discovered scenario.

Door errors carry `unknownOutcome: true` whenever dispatch may have occurred and no confirmed terminal outcome is available, including lost replies, cancellation, mismatched receipts, or failed authenticated reads. This flag is independent of server error wording. Definite admission refusals and confirmed failed/refused terminal outcomes do not carry it; a passed receipt without its lossless program result remains uncertain. Callers must not infer dispatch certainty from error text.

For a confirmed door run, obtain exact before/after worlds from the owner state endpoint when its action list contains the receipt report.action_id. Match that immutable action ID exactly; never use another action or the top-level current world as this run's observation. These snapshots were captured under the server's action lock. A failed observation read cannot erase the confirmed program result or trigger a new dispatch; leave unavailable snapshots missing. Preserve existing receipt snapshots when no matched owner observation is available. This uses B1 state reads, not a new server endpoint or model call.

If owner metadata refuses a saved Try with session-stopped, read that same owner run record. A confirmed paused session is reopened through runTry without --new or a budget change, retaining its session ID, data and allowance; then read owner metadata again. Do not treat another refusal or an uncertain state as confirmation of pause. This makes an explicit tool request resume the same idle-paused Try without resetting it.
