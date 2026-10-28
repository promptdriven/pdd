# Runtime output

Own `src/runtime-output.mjs`. It turns `pdd check` rows into the terminal table, the `--json` object and the exit code. It makes no call and writes no file.

## Rows

A row is one test: `story`, `title`, `test`, `state`, `checks {passed, total}`, `failed_checks [{criterion_id, target, path, expected, actual}]`, `refusals [{code, section, message, engine_message, hint}]`, `calls`, `seconds`, `requested_model`, `report_url`, `request_id`. States: `passed`, `failed`, `refused`, `not_run`, `unknown`, `queued`, `running`.

- From a server answer: checks come from `result.report.samples[0].steps[].checks[]`; refusals from `result.refusals`; calls from `usage.calls`; the model from `usage.requested_model` (else the report's `evaluation.requested_model`). pdd uses `state`, not `outcome`.
- Seconds are rounded to 0.1.
- Expected and got values print as JSON, so strings are quoted and escaped (`"Sam\n"` differs from `"Sam"`).
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
3. One paste line per Story (0.1.6, many Stories in one run), in table order: `Runtime check (<story>): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call`, with ` (DRAFT)` after the story when a row of it ran a draft prompt; a Story with two test files gets one line for both. Then the overall summary line, last of these lines, one line that an agent can paste into a PR: `Runtime check: ✓ 3 of 3 criteria · 10/10 checks · 1 AI call`; `Runtime check (DRAFT): …` when a row ran a draft prompt. ✓ only when every row passed; ✗ only when a row failed, was refused or was not run; otherwise `running` (a row is still queued or running) or `unknown`, so a check that still runs never shows ✗ or "failed" (cli 12b). Criteria come from the report's `criterion_results`; a row with no such list counts its test's criteria, all passed only when the row passed. Rows that are refused, not run, unknown, queued or running add `· N refused` (and so on). Calls count only ended rows; others add ` + N unknown`.
4. A block for each problem row, failed rows first:
   - `FAILED  <title> (<test>)`, one line for each failed check `  AC1  result /totalCents  expected 899, got 900`, the row warnings, then `  Report: <url>   Next: show the person this check. Do not change the expected value yourself.`
   - `REFUSED before sending (not sent, 0 AI calls)`, then for each row `  <test>  step N  <code>` and the message and hint lines.
   - `REFUSED  <title> (<test>)`, then `  <code>  <section>  <message>`, the engine message when it adds detail, and the `pdd:` hint.
   - `NOT RUN  <title> (<test>): <message> (<code>)`.
   - `STILL RUNNING after N min: <title>. Do not send it again.` at a time limit of N min (after Ctrl-C: `STILL RUNNING when pdd stopped reading: …`; in `--read`, or with no known limit: `STILL RUNNING: …`)
   - `UNKNOWN  <title>: the run may have executed. Its result is unknown.` and the server's reason.
   - An AI provider failure (state `unknown` with `graph-provider-failure`, or a sample `failure_cause.kind` of `transport_unknown`) has its own block: `UNKNOWN  <title>: the AI provider failed during the run. It is not a failed check. Do not send it again yet.`, then the code, the cause and the report link. The block ends with `To try again, run \`pdd check\` again (a new request).` pdd never resends it.
5. With `--details`: every check of each row, failed checks first.
6. `X of Y stories passed. Model asked for: M.` Skip the model part when it is not known. Time is shown only for ended rows.
7. `Reports (anyone with a link can open it):` and one `  <story>  <url>` line for each row with a link.

## JSON (stdout, `--json`)

One object: `{batch, repo, exit_code, summary_line, draft, rows: [{story, title, test, state, checks, criteria, failed_checks, refusals, calls, seconds, requested_model, report_url, request_id, draft, reason, summary_line}], warnings}`. A row's `summary_line` is the paste line of its Story. `draft` is true for a row that ran a draft prompt, and at the top when any row did. When the server answer has `draft_prompts` (a list of repo paths), a nonempty list means DRAFT and an empty one means not DRAFT; it wins over pdd's local guess. Older servers without the field keep the local guess. `reason` is `{code, message}` for a row that was not run or is unknown (`graph-provider-failure` for a provider failure), else null. Nothing else goes to stdout.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. The [runtime client](runtime-client.prompt.md) builds the rows and prints this output.
