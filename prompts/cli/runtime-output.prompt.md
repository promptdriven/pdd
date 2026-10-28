# Runtime output

Own `src/runtime-output.mjs`. It turns `pdd check` rows into the terminal table, the `--json` object and the exit code. It makes no call and writes no file.

## Rows

A row is one test: `story`, `title`, `test`, `state`, `checks {passed, total}`, `failed_checks [{criterion_id, target, path, expected, actual}]`, `refusals [{code, section, message, engine_message, hint, reason, fix, where, cause}]`, `calls`, `seconds`, `requested_model`, `report_url`, `request_id`. A confirmed unstarted capacity row has `busy:true`, `can_retry:true` and state `not_run`; it is not a source refusal or failed assertion. Render its capacity advice without a Fix-the-test line and mark a busy-only summary `busy`, not ✗. Mixed actual failures retain ✗. Preserve request ID, report and zero-call accounting. States: `passed`, `failed`, `refused`, `not_run`, `unknown`, `queued`, `running`.

- From a server answer: checks come from `result.report.samples[0].steps[].checks[]`; refusals from `result.refusals` (prompt-runtime #379 adds `reason` in plain words, `fix`, `file`, `at`, `where` = file and place as one text, and `cause`: `call-budget`, `ai-service`, `test`, `prompt`, `server` or `unknown`; `where` falls back to `file` and `at`; each is null when missing); calls from `usage.calls`; the model from `usage.requested_model` (else the report's `evaluation.requested_model`). pdd uses `state`, not `outcome`.
- Seconds are rounded to 0.1.
- Expected and got values that fit on one line print as JSON on the check line, so strings are quoted and escaped (`"Sam\n"` differs from `"Sam"`). They fit when no string has a line break before its end and each JSON is at most 80 characters.
- Other values (round-2 tester: a CLI's stdout lost its line breaks and was cut near the difference) print as a block under the check line: `    expected:` and `    got:`, each followed by its lines, 6 spaces in. A string shows its own lines with no quotes, and `(ends with a line break)` when it ends with one; any other value shows as JSON with 2-space indents. pdd never cuts inside a line. A value shows at most 20 lines: from line 1, or from 2 lines before the first line where two strings differ when that line is later. Lines left out are named: `… N lines before` above, `… N more lines in the report` below. Each line loses control characters and the token but keeps its spaces.
- Clean all server text: remove control characters, the token and server paths (`/home/…`, `/srv/…`, `/var/…`, `/tmp/…` and similar). Expected and actual values keep their JSON type but lose the token.

## Exit code

The first match from the top wins:

| Code | When |
|---|---|
| 3 | A row is unknown, queued, running or in any state that is not a known end, the lint result is unknown, or Ctrl-C |
| 5 | A row was not run (sign-in, gate, server busy at the time limit or when pdd stopped, no AI room) |
| 4 | A row was refused (local preflight, lint or engine) |
| 1 | A row failed |
| 0 | All passed |

## Text (stdout)

1. Exit 3: the first line is `pdd check --read <batch>`.
2. The table: `Story`, `Test`, `Result`, `Checks`, `Time`. Story = the story title. Result `not run` for `not_run`; a draft row adds ` (DRAFT)` to its result and to its report link line. Checks `n/m` or `-`. Time `21.0 s` or `-`.
3. One paste line per Story (0.1.6, many Stories in one run), in table order: `Runtime check (<story>): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call`, with ` (DRAFT)` after the story when a row of it ran a draft prompt; a Story with two test files gets one line for both. With one Story, its line is the only Runtime check line (round-2 tester: no second line that repeats it). With two or more Stories, the overall summary line comes last of these lines, one line that an agent can paste into a PR: `Runtime check: ✓ 3 of 3 criteria · 10/10 checks · 1 AI call`; `Runtime check (DRAFT): …` when a row ran a draft prompt. ✓ only when every row passed; ✗ only when a row failed, was refused or was not run; otherwise `running` (a row is still queued or running) or `unknown`, so a check that still runs never shows ✗ or "failed" (cli 12b). Criteria come from the report's `criterion_results`; a row with no such list counts its test's criteria, all passed only when the row passed. Rows that are refused, not run, unknown, queued or running add `· N refused` (and so on). Calls count only ended rows; others add ` + N unknown`.
4. A block for each problem row, failed rows first:
   - `FAILED  <title> (<test>)`, one line for each failed check `  AC1  result /totalCents  expected 899, got 900` (or the check line `  AC1  result /stdout` and its block), the row warnings, then `  Report: <url>   Next: show the person this check. Do not change the expected value yourself.`
   - `REFUSED before sending (not sent, 0 AI calls)`, then for each row `  <test>  step N  <code>` and the message and hint lines.
   - `REFUSED  <title> (<test>)`, then for each refusal with a `reason`: `  <code>: <reason>`, `  Where: <where>` when there is one, and `  Fix: <fix>`; when `cause` is `ai-service` the last line is `  Your test is fine. Run it again.` in place of the fix. A refusal with no `reason` (the live server before #379) keeps `  <code>  <section>  <message>` and the engine message when it adds detail. Both end with the `pdd:` hint when there is one.
   - `NOT RUN  <title> (<test>): <message> (<code>)`.
   - `STILL RUNNING after <limit>: <title>. Do not send it again.` at the time limit; the limit is `90 s` for the agent default, else `N min` (after Ctrl-C: `STILL RUNNING when pdd stopped reading: …`; in `--read`, or with no known limit: `STILL RUNNING: …`)
   - `UNKNOWN  <title>: the run may have executed. Its result is unknown.` and the server's reason.
   - An AI provider failure (state `unknown` with `graph-provider-failure`, or a sample `failure_cause.kind` of `transport_unknown`) has its own block: `UNKNOWN  <title>: the AI provider failed during the run. It is not a failed check. Do not send it again yet.`, then the code, the cause and the report link. The block ends with `To try again, run \`pdd check\` again (a new request).` pdd never resends it.
5. With `--details`: every check of each row, failed checks first.
6. `X of Y stories passed. Model asked for: M.` Skip the model part when it is not known. Time is shown only for ended rows.
7. `Reports (anyone with a link can open it):` and one `  <story>  <url>` line for each row with a link.

## JSON (stdout, `--json`)

One object: `{batch, repo, exit_code, summary_line, draft, rows: [{story, title, test, state, checks, criteria, failed_checks, refusals, calls, seconds, requested_model, report_url, request_id, draft, reason, summary_line}], warnings}`. A row's `summary_line` is the paste line of its Story. `draft` is true for a row that ran a draft prompt, and at the top when any row did. When the server answer has `draft_prompts` (a list of repo paths), a nonempty list means DRAFT and an empty one means not DRAFT; it wins over pdd's local guess. Older servers without the field keep the local guess. `reason` is `{code, message}` for a row that was not run or is unknown (`graph-provider-failure` for a provider failure), else null. Nothing else goes to stdout.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. The [runtime client](runtime-client.prompt.md) builds the rows and prints this output.

Saved check JSON includes source_sha256 (full captured upload hash, null when no capture) so workflow evidence can verify it against the exact selected source.

## Try usage
Export tryUsage(answer, {cap}={}), tryUsageLine(usage, {command=false}={}) and tryUsageHeaders(usage). Normalize only nonnegative safe-integer counts; absent/malformed counts are unknown, never invented zero. Owner model calls.cap/remaining, session.max_calls/remaining_calls and call usage.calls/report.remaining_calls are the existing server fields. Derive cumulative used only from valid cap and remaining <=cap; this is the Try session allowance, not a machine/account/tester allowance. Format a short startup/session line and per-command line that distinguishes this command's calls, session used, remaining and cap, with unknowns explicit. HTTP header names are x-pdd-ai-calls, x-pdd-try-used, x-pdd-try-remaining and x-pdd-try-cap; values are decimal integers or unknown. These headers are owned metadata and cannot come from program result headers.

## Progress and causes
Every pdd command reports progress and errors through these two helpers, so all progress has one style.
- Export `progressTicker(stream, now, everyMs = 15000)`. A slow step (more than about 2 s: network, lint, upload, the queue, AI calls, git, gh, Herdr, an agent) first prints one plain line that ends with `…`, for example `Checking 3 files (29 KB) on the PDD runtime (lint, 0 AI calls)…`. The returned `tick(text)` prints `<text> · <time>` at most once every `everyMs`, counted from the start, with the time from `sinceText` (`N s` under a minute, else `N min`). Each step ends with a clear line: the result, or `Try ready: <link>`.
- Progress goes to stderr only, never to stdout, so the result and `--json` stay clean. A person and an agent (no terminal) get the same lines: no spinner, no carriage return, no colour codes.
- Export `causeText(value, secrets = [])`: the first nonempty line of a tool's or server's error text, with control characters, the given secrets and GitHub or API tokens removed, at most 300 characters. An error line says what failed, this real reason, and what to do next.

## Step time limits

Export `stepTimeLimit(answer, {steps=[], secrets=[]}={})` to recognize a server step time refusal from raw report/sample/step refusals. The published server currently reports legacy `graph-provider-failure` with explicit timeout/timed-out/time-limit detail (including failure_cause.detail or legacy failure_cause.kind timeout); do not classify a generic provider failure, queue wait or client polling deadline as a step limit. A typed failure_cause.kind `step_timeout` also identifies a step limit independent of its code. No dedicated new code is assumed until the runtime publishes it.

Identify the step by its reported step_id/name, otherwise a valid steps[N] refusal section mapped to authored step IDs (including the sole matching companion refusal section when raw sample metadata omits it), otherwise say unnamed step. Preserve/sanitize the server-provided name. Use an explicit positive timeout_seconds/limit_seconds from the refusal or its details, otherwise a timeout detail's explicit seconds/minutes; legacy default is180seconds. A typed step_timeout without a reported duration uses the requested600second policy. Never infer the time limit from total job elapsed time. Return code, step, minutes and the message `Step NAME took more than N minutes and was stopped.` plus `Make the step smaller, for example split 30 moves into 3 steps of 10.`

This is inconclusive execution, never a failed expectation. Project it as unknown with structured time_limit and reason, retaining actual usage, earlier check evidence and report/ID. In text, give a STOPPED block with that step message and advice, suppress the generic provider-failure/failed-expectation framing for this refusal. Other provider failures retain existing behavior. JSON contains the same message and structured time_limit. No automatic retry is authorized.
