# Know what happened to my selected tests

I can trust the result of lint and paid checks: a pass has evidence, a refusal
keeps its reason, and unfinished work stays unfinished.

## Acceptance criteria

1. `pdd lint place-order` passes only when lint is complete and the server explicitly passes that test; its row, summary, JSON and exit code agree.
2. Refused lint with a program report but no selected verdict keeps the server's refusal code and text, exits 4 (or 3 when only incomplete evidence exists), never says the test passed, and sends no paid checks.
3. Incomplete lint says "lint did not finish", shows unknown and exits 3. Empty lint or a complete lint missing the selected verdict also stays unknown, never exit 0. A program without a prompts list produces a truthful result without an internal error.
4. An unrelated refusal remains visible as a diagnostic. Only a complete passing verdict for the selected test allows that test to pass despite it; a refused selected test or reached prompt still refuses the row.
5. New checks, saved-lint continuation, retry, the restart replacement and a new Try use the same gate: every selected test that would be sent must have a passing lint outcome before anything paid is sent. Rejected gates allocate no paid request and retain zero unsent calls. Source, owner, intent and call-ceiling protections remain in force.
6. Queued, running, passed, failed, refused, not run and unknown remain distinct in the table, Story summary, JSON and exit. Empty outcomes exit 3; unknown is not counted as a done Story. Missing per-criterion evidence does not count authored criteria as passed.
7. A retryable pool-copy-unavailable answer with dispatch not_started shows not run, exits 5, keeps the server's text and has neither a cross nor a refused block. Uncertain execution is never retried by inference.
8. When the server sends step 3 of 5, 4 settled AI calls and 1 in flight, the running row, progress line and summary show "running · step 3 of 5 · 4 AI calls so far · 1 in flight". Missing progress fields stay unknown; no step or call count is invented. Saved reads retain supplied progress.

## Server evidence

Read from the server's main branch before defining the cases:

- `server/lint_driver.py:163-209`: lint problems carry `complete` and `tests: [{path, verdict}]`; test verdicts are `passed`, `refused` or `not-checked`. Engine reports can carry `refusal`; the merged public test list retains path and verdict only.
- `server/runner.py:768-782`: a lint starts with `report.lint = {tests: [], app_maps: [], complete: false}`; delivered results replace it with the test verdicts and `complete` flag. A program report alone does not prove completion.
- `server/app.py:169-305`: terminal `result` has `report` and `refusals`; lint exposes `problems_complete`, `tests` and `problems`; queued/running results are null. Job `state` and report `verdict` can refuse even while `program` exists. Public refusals include reason, field/location, fix and message.
- Running `progress: {steps_done, steps_total, step, calls_settled, calls_open}` is a forward client contract, used when the server sends it. The current server does not prove it yet.

## Native cases

`test/runtime-outcomes.test.mjs` uses the real client and output exports with
`test/runtime-fake.mjs`, temporary Git/state folders and injected clock/transport.
It tests complete pass; program-bearing refusal; incomplete, empty and missing
verdicts; unrelated diagnostics with and without selected evidence; every gate;
all exit states; retryable pool refusal; full and partial running progress.
Expected changes are listed for the person in the builder's EXPECTED-CHANGES.md.
No paid interpreter check or live server result is claimed. The client has native
filesystem/capture effects without a complete interpreter binding; these native
regressions do not claim an interpreter prompt verdict.
