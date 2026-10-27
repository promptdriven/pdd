# Runtime client

Own `src/runtime-client.mjs`. Export `runCheck({words, options, cwd}, ports)` and `runTry({words, options, cwd}, ports)`. Each returns an exit code. These two commands are the only pdd commands that call the PDD runtime. They sign in with the person's `gh` login.

## Setup

- Repo root = `git rev-parse --show-toplevel` (a worktree is its own root). No Git repo: exit 2.
- `PDD_RUNTIME_URL`, default `https://runtime.34-72-131-98.sslip.io`. It must be an HTTPS origin with no user, password, path, query or fragment. Only for local tests, `http://` is allowed for `127.0.0.1`, `localhost` and `[::1]`. Else exit 2.
- `PDD_STATE_DIR`, default `~/.pdd/runtime`. Refuse a state folder inside the repo (exit 2).
- Ports (tests inject them): `env`, `stdout`, `stderr`, `fetch`, `gh(args)`, `now`, `randomUUID`, `sleep`, `onInterrupt`, `openUrl`, `pollMs`. Read the environment only from `env`.

## Sign-in

- Token = `gh auth token`, in memory only: never in files, logs, argv, URLs or error text. No `gh`: exit 5, `Install the GitHub CLI, then run gh auth login`. Empty: exit 5, `Run gh auth login`.
- `gh api user --jq '.login + " " + (.id|tostring)'` once per batch; save the login and the user ID.
- Every call sends `Authorization: Bearer <token>` with TLS on and `redirect: 'manual'`.

## `pdd check`

Modes: `--fill-hash` and `--files` take no other option or STORY and make no network call. `--read [BATCH] [--json]` reads saved results. Hidden `--request UUID` reads one run with GET only. A wrong mix is exit 2.

Order:
1. [Preflight](runtime-preflight.prompt.md), capture and sign-in. Nothing is sent yet. If every selected test is refused locally, print the result and exit 4 with no sign-in.
2. Batch ID `YYYYMMDD-HHMMSS-xxxx` (local time). One new `crypto.randomUUID()` for lint and for each test. Write `batch.json`. Print to stderr: `If pdd stops, read the results with: pdd check --read <batch>`.
3. Lint: write `<id>.posted` (exclusive create), then POST `/v1/lint` multipart (`request` = `{requestId, source_sha256}`, no `paths`; `source` = the tar). Read until terminal, at most 2 min. Judge only the prompts that the tests reach (step `entry_path` and their `calls` targets): a prompt in `result.report.program.refused_prompts`, or with `admission_state` not `approved`, refuses each test that reaches it. A lint answer with no program report is a refusal when the state is `refused` with refusals, else lint is unknown: exit 3, no checks sent.
4. Checks: for each test write `<id>.posted`, then POST `/v1/check` with `{requestId, source_sha256, scenario: <test path>, max_calls}` and the same tar. `max_calls` = `--max-calls` or `min(100, max(4, ceil(steps * 2 * 1.2)))`. Start all POSTs at the same time. POST timeout 90 s.
5. Read: GET `/v1/runs/<id>` for each open row every 2 s (at most 8 GETs at a time) until all rows end or the timeout (`--timeout`, default 10 min, from the lint POST) ends. Save each answer as `<id>.json`. Then print the [output](runtime-output.prompt.md), write `summary.json` and return the exit code.

| Answer to a POST | Row | Next step |
|---|---|---|
| 200/202 JSON, same `requestId` and `id`, right `command` | accepted | read it |
| 429 `server-full` with `dispatch: "not_started"` | waiting | a NEW request ID after `Retry-After` (else 5 s) or when a row ends, until the timeout. Keep the old ID |
| 429 without `dispatch: "not_started"` | not run | no new attempt |
| 503 JSON `pool-low-room`, `pool-copy-*`, `github-unavailable` | not run | no new attempt; show the server text |
| 503 text `The runtime opens soon.`, or 401 | not run | send no more POSTs; the gate text or `Run gh auth login` |
| 400, 413, 415, 422 JSON | refused | no new attempt; show code and message |
| timeout, lost connection, other 5xx, non-JSON, 409, wrong ID or command | unknown | GET that same ID only. Never POST again for this test in this batch |

- GET: 200 gives the state. 404 after a POST: keep reading; at the timeout the row is unknown. 410: unknown, `result expired`. 401: stop reading; open rows stay open (exit 3) and pdd prints `Run gh auth login`. A wrong ID or command: unknown. Server `state: unknown`: show its `why`.
- At the timeout: open rows stay `queued`/`running` (exit 3); waiting rows are not run (exit 5).
- A server refusal `invalid-input` gets the local P9 rule as its hint. A server `interface-unapproved` or `interface-stale` on `steps[N]` gets the P7 hint.
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
- If `repos/<key>.json` has a Try for this test and GET says `result.session.state: running` with a valid link, open that link again. `--new`: stop the old Try first, then make a new one.
- POST `/v1/try` multipart `{requestId, source_sha256, seed: <test path>, tab}` (tab default `call`; no `app_map`, no `max_calls`). Read until `state: passed`, `result.session.state: running` and a valid `result.url`: the origin's scheme and host, path `/s/<token>/`, no user or password. Else refused, not run or unknown, as for a check.
- Open the link with `open` (macOS) or `xdg-open` (Linux) and print `Try link for "<title>" is open in your browser. It ends in 24 hours, or with: pdd try --stop <story>`. `--no-open`, or a failed open, prints the link instead.
- `--stop`: DELETE `/v1/try/<id>` with the header `X-Request-Id: <new UUID>`; read the stop job until `passed`; then forget the Try.
- 429: no new attempt; `Too many Try links are open. Stop one with pdd try --stop`; exit 5. Exit 0 = link ready or stopped; other exit codes as for `pdd check`.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md). The [CLI](pdd-cli.prompt.md) calls `runCheck` and `runTry`.
