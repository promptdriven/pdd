# Runtime client

Own `src/runtime-client.mjs`. Export `runCheck({words, options, cwd}, ports)` and `runTry({words, options, cwd}, ports)`. Each returns an exit code. These two commands are the only pdd commands that call the PDD runtime. They sign in with the person's `gh` login.

## Setup

- Repo root = `git rev-parse --show-toplevel` (a worktree is its own root). No Git repo: exit 2.
- The runtime address is one setting: `PDD_RUNTIME_URL`, else the exported constant `DEFAULT_RUNTIME_URL` in this module. No other code, prompt, test or doc names the address; tests use the override or import the constant. It must be an HTTPS origin with no user, password, path, query or fragment. Only for local tests, `http://` is allowed for `127.0.0.1`, `localhost` and `[::1]`. Else exit 2.
- `PDD_STATE_DIR`, default `~/.pdd/runtime`. Refuse a state folder inside the repo (exit 2).
- Ports (tests inject them): `env`, `stdout`, `stderr`, `fetch`, `gh(args)`, `now`, `randomUUID`, `sleep`, `onInterrupt`, `openUrl`, `pollMs`, `postMs`. Read the environment only from `env`.

## Sign-in

- Token = `gh auth token`, in memory only: never in files, logs, argv, URLs or error text. No `gh`: exit 5, `Install the GitHub CLI, then run gh auth login`. Empty: exit 5, `Run gh auth login`.
- `gh api user --jq '.login + " " + (.id|tostring)'` once per batch; save the login and the user ID.
- Every call sends `Authorization: Bearer <token>` with TLS on and `redirect: 'manual'`.

## `pdd check`

Modes: `--fill-hash` and `--files` take no other option or STORY and make no network call. `--read [BATCH] [--json]` reads saved results. Hidden `--request UUID` reads one run with GET only. A wrong mix is exit 2.

Order:
1. [Preflight](runtime-preflight.prompt.md), capture and sign-in. Nothing is sent yet. If every selected test is refused locally, print the result and exit 4 with no sign-in. The result warnings include the preflight warning about source files that two prompts name. Before a check of ALL stories (no STORY word), print to stderr `Checking all N stories: about A AI calls (at most M).`: A = for each step, 1 plus the `max_calls` of the calls its entry prompt declares; M = the sum of the tests' `max_calls` (cli 12b).
2. Batch ID `YYYYMMDD-HHMMSS-xxxx` (local time). One new `crypto.randomUUID()` for lint and for each test. Write `batch.json`. Print to stderr: `If pdd stops, read the results with: pdd check --read <batch>`.
3. Lint: write `<id>.posted` (exclusive create), then POST `/v1/lint` multipart (`request` = `{requestId, source_sha256}`, no `paths`; `source` = the tar). Read until terminal, at most 2 min. Judge only the prompts that the tests reach (step `entry_path` and their `calls` targets): a prompt in `result.report.program.refused_prompts`, or with `admission_state` neither `approved` nor `draft`, refuses each test that reaches it. A reached `draft` marks the row as a draft. A lint answer with no program report is a refusal when the state is `refused` with refusals, else lint is unknown: exit 3, no checks sent.
4. Checks: for each test write `<id>.posted`, then POST `/v1/check` with `{requestId, source_sha256, scenario: <test path>, max_calls}` and the same tar. `max_calls` = `--max-calls` or the preflight default (4 for each step, 6 to 100). Start all POSTs at the same time. POST timeout 90 s.
5. Read: GET `/v1/runs/<id>` for each open row every 2 s (at most 8 GETs at a time) until all rows end or the timeout (`--timeout`, default 10 min, from the lint POST) ends. Save each answer as `<id>.json`. Then print the [output](runtime-output.prompt.md), write `summary.json` and return the exit code.

| Answer to a POST | Row | Next step |
|---|---|---|
| 200/202 JSON, same `requestId` and `id`, right `command` | accepted | read it |
| 429 `server-full` with `dispatch: "not_started"` | waiting | a NEW request ID after `Retry-After` (else 5 s) or when a row ends, until the timeout. Keep the old ID |
| 429 without `dispatch: "not_started"` | not run | no new attempt |
| 503 JSON `pool-low-room`, `pool-copy-*`, `github-unavailable` | not run | no new attempt; show the server text |
| 503 text `The runtime opens soon.`, or 401 | not run | send no more POSTs; the gate text or `Run gh auth login` |
| 403 `not-invited` (top-level `code` or `error.code`, with `login`) | not run | stop the batch: one plain line `Your GitHub login <login> is not on the PDD runtime invite list yet. Ask the PDD team to add you.`, exit 5 (lint, checks, GETs, `pdd try` and its stop alike) |
| 400, 413, 415, 422 JSON | refused | no new attempt; show code and message |
| timeout, lost connection, other 5xx, non-JSON, 409, wrong ID or command | unknown | GET that same ID only. Never POST again for this test in this batch |

- GET: 200 gives the state. 404 after a POST: keep reading, also when its body says `state: refused` with `job_created: false`; it is never a refusal. A row whose POST answer was lost (timeout, lost connection) is read by the same ID for at least 5 min after the loss, or until the timeout if that is later; then it is unknown. A lost lint answer is read the same way. 410: unknown, `result expired`. 401: stop reading; open rows stay open (exit 3) and pdd prints `Run gh auth login`. A wrong ID or command: unknown. Server `state: unknown`: show its `why`.
- At the timeout: open rows stay `queued`/`running` (exit 3); waiting rows are not run (exit 5). `Retry-After` is whole seconds from 1 to 300; no header means 5 s.
- A row is marked `sending` before its POST. If pdd was killed, `--read` reads every posted row by its ID (a posted row with no answer is unknown, exit 3) and calls a row with no request ID not run.
- A server refusal `invalid-input` gets the local P9 rule as its hint. A server `interface-stale` on `steps[N]` gets the P7 hint. A server `interface-unapproved` for a draft row gets the message `The server does not run draft prompts yet. Approve the prompt first, or wait for the server update.` (exit 4), until the server runs drafts.
- Save `engine_sha` from each answer. When it is not 7b03d3ea (the engine that the local rules copy), add a warning; the engine stays the judge. Show it at most once a day for each engine sha (a stamp in `$PDD_STATE_DIR/engine-warnings.json`).
- Ctrl-C after `batch.json` exists: stop all calls, keep the state, print the `--read` line, exit 3.
- `--read`: the batch in BATCH, else the last batch of this repo. Use the saved origin. A different gh login: exit 5, `These runs belong to <login>. Run: gh auth switch -u <login>`. One GET for each open row, saved JSON for ended rows. It never makes a request ID and never POSTs.

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

- STORY as for `pdd check`. No STORY and one test: use it. Many tests: list them, exit 2. Then preflight, capture and lint as for `pdd check`, for this one test.
- If `repos/<key>.json` has a Try for this test and GET says `result.session.state` `running` or `paused` (the live server pauses an idle Try; the link wakes it) with a valid link, open that link again. `--new`: stop the old Try first, then make a new one. A Try that ended (404, 410, failed, refused, unknown, session stopped or unknown) is forgotten, and a new Try is made: a new Try costs no AI calls. A Try that is still starting, or a GET with no answer, is exit 3 with no new Try, unless `--new` stops it first. A new Try whose setup ends `unknown` is forgotten too: `The Try setup did not finish on the server (its state is unknown; the server may have restarted). It used no AI calls. Run pdd try <story> to make a new Try.` (exit 3).
- After Ctrl-C, pdd sends nothing new: no POST starts after the interrupt.
- App map: `--app-map PATH`, else `app-map.json` at the repo root, else `app/app-map.json`. An app map is a Git-visible JSON object with `"schema_version": "prompt-runtime.app-map.v1"` and a nonempty `name` (the engine's first checks). A bad `--app-map` is exit 2 with the reason (`not a Git-visible file`, `not JSON`, wrong `schema_version`, no `name`) and `See RUNBOOK.md §13.`; a bad found file is skipped with a note. With an open Try, `--app-map` or `--tab` without `--new` is exit 2: they apply only to a new Try. POST `/v1/try` multipart `{requestId, source_sha256, seed: <test path>, app_map, tab}`: `app_map` only when there is one; `tab` = `--tab`, else `screen` with an app map, else `call`; no `max_calls`. Read until `state: passed`, `result.session.state: running` and a valid `result.url`: the origin's scheme and host, path `/s/<token>/`, no user or password. Else refused, not run or unknown, as for a check. A Try that is ready but has an invalid link is exit 3 with one line and no table: `Try link refused: it points at <link origin>, not <configured address>. The server's address setting may be wrong; tell the PDD team.` (or `Try link refused: it is not a valid Try link. Tell the PDD team.` when the origin matches). pdd keeps its record so `pdd try --stop` can end it, a later `pdd try` says the same, and pdd never prints that link.
- Open the link with `open` (macOS) or `xdg-open` (Linux) and print `Try link for "<title>" is open in your browser. It ends in 24 hours, or with: pdd try --stop <story>`. `--no-open`, or a failed open, prints the link instead.
- `--stop [STORY]` finds the Try in the state record by story name, test path or test file name, so it works on a branch without the story (real-user issue 14). No STORY stops the one open Try; none or several is exit 2 with the open names. It sends DELETE `/v1/try/<id>` with the header `X-Request-Id: <new UUID>`; read the stop job until `passed`; then forget the Try. A DELETE answer 404 or 410 counts as stopped. A GET 404 or 410 on a recorded Try counts as ended. In both cases pdd deletes the record, so the next `pdd try` makes a new Try; the person never edits a state file.
- The note on other files prints once per command, in calm words, to stderr. `pdd check` folds it into its send line: `Lint passed. Sent 2 checks at 10:47:49: 11 files, 55 KB (4 are not prompt, story or test files; run \`pdd check --files\` to see them).` `pdd try` prints `Sent M files (N are not prompt, story or test files; run \`pdd check --files\` to see them).` before it posts the Try. It is not a warning.
- 429: no new attempt; `Too many Try links are open. Stop one with pdd try --stop`; exit 5.
- Approvals from the Try page (#9, agreed fields): with the saved cases, pdd reads `GET /v1/try/<id>/approvals` (`{approvals: [{id, prompt_path, prose_sha256, requested_at, state}]}`). For each `pending` request in a person's terminal it uses [prompt approve](prompt-approve.prompt.md): the path must be a Git-visible `*.prompt.md` inside the repo (else declined), the request's `prose_sha256` must equal the local prose hash (else declined: `the prompt changed since you clicked Approve`), an approved and current prompt is done with no question, otherwise it shows the interface and asks the same y/n; one reader serves all questions. Then it sends `POST /v1/try/<id>/approvals/<request id>` with `{"state": "done" | "declined"}` (JSON). `tries/<id>.approvals.json` keeps each answer, so pdd never asks twice and resends only an answer whose POST failed. Without a terminal (an agent) pdd only prints `The Try page asks to approve <path>. A person answers it in a terminal: pdd try <story>` once and answers nothing. A missing endpoint (404) is skipped. Waiting needs both stdin and stdout to be terminals.
- Save as test (Serhan, Oct 27): after the link is shown, pdd reads `GET /v1/try/<id>/tests` (`{tests: [{id, path, name, created, story_path, test}]}`, try-page DESIGN.md). For each saved case that it has not handled (`tries/<id>.tests.json` keeps the handled IDs), it appends the case's steps to the test file of that story (found as in discovery) and keeps every other byte of the file (a one-line `steps` array gets a one-line step). Criterion IDs map by criterion text; a case with a criterion the file does not have is `not added` with the reason. A saved case is untrusted (anyone with the link can save one): its story must be a Git-visible `*.md` file in the repo with no `..`; an existing target must be a regular `*.json` file whose real path is inside the repo, whose top-level `schema_version` is `prompt-runtime.program-scenario.v1`, and that is not `package.json`, a lock or config file or a dot file; a new file goes only to `tests/<story slug>.json` (never a path from the server), created exclusively, and never when `tests/` is a symbolic link or resolves outside the repo. Each refusal prints `not added: <reason>` and writes nothing. Step IDs stay unique (`-2`, `-3`). Only a story with no test file gets a new file, `tests/<story>.json`. Print `added to tests/<file> as step <id>`. In a terminal (stdout is a TTY) pdd stays open and reads every 5 s until Ctrl-C or the Try ends; `--no-wait`, or no terminal (an agent), reads once and returns. A missing endpoint (404) prints `The runtime does not keep saved tests yet.` only while waiting. Exit 0 = link ready or stopped; other exit codes as for `pdd check`.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md). The [CLI](pdd-cli.prompt.md) calls `runCheck` and `runTry`.
