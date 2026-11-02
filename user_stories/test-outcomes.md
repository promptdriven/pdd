# Know what happened to my selected tests

I can trust the result of lint and paid checks: a pass has evidence, a refusal
keeps its reason, and unfinished work stays unfinished.

## Acceptance criteria

1. `pdd lint place-order` passes only when the server gives that test its own passing verdict. This counts even when the lint did not finish for other tests. Its row, summary, JSON and exit code agree.
2. Refused lint with a program report but no verdict for my test keeps the server's refusal code and text, exits 4, never says the test passed, and sends no paid checks.
3. A lint that ended without a pass for my test says why ("lint did not finish" or "lint gave no verdict for this test"), shows not run and exits 5, so I know that reading again will not help. Only a lint that has not ended yet is unknown with exit 3. Empty lint is never exit 0. A program without a prompts list produces a truthful result without an internal error.
4. An unrelated refusal remains visible as a diagnostic. Only the selected test's own passing verdict allows that test to pass despite it; a refusal of the selected test or of a prompt it reaches still refuses the row.
5. New checks, saved-lint continuation, retry, the restart replacement and a new Try use the same gate, per test: a selected test is sent only when its own lint verdict is a pass. With 18 selected tests and one lint refusal, the other 17 are still sent; the refused one stays refused and a test with no verdict is not run. A test with its own pass is sent even when the lint did not finish for other tests. A held-back test allocates no paid request and keeps zero calls, and the restart replacement says in one line why it held a test back. Source, owner, intent and call-ceiling protections remain in force.
6. Queued, running, passed, failed, refused, not run and unknown remain distinct in the table, Story summary, JSON and exit. Empty outcomes exit 3; unknown is not counted as a done Story. Missing per-criterion evidence does not count authored criteria as passed.
7. An answer that the server marks retryable with dispatch not_started shows not run, exits 5, keeps the server's code and text and has neither a cross nor a refused block, whatever the code is (for example pool-copy-unavailable or login-queue-timeout). Uncertain execution is never retried by inference.
8. When the server sends step 3 of 5, 4 settled AI calls and 1 call without a settled result, the running row, progress line and summary show "running · step 3 of 5 · 4 AI calls so far · 1 not yet settled". When the step also has a name, I see both: "step 3 of 5 (render)". With several running tests, a line shows one progress part with the summed calls, and the calls of checks that ended stay on the line. Missing progress fields stay unknown; no step or call count is invented. Saved reads retain supplied progress.

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
No paid interpreter check or live server result is claimed. The client has native
filesystem/capture effects without a complete interpreter binding; these native
regressions do not claim an interpreter prompt verdict.
