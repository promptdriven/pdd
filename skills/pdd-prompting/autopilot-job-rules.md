# Autopilot core job rules

Read this whole file before you write or check the PR body. It is short on purpose: one read holds all of it. The long
reference is RUNBOOK.md §15 "Autopilot core jobs", with §3, §11 and §17.

These rules are for a job of the Autopilot core engine (`pdd autopilot start --engine core`). The job makes one PR
with no workflow run. It writes the `Runtime:` lines and one `Evidence:` line in the PR body. Autopilot checks each
line against its own records. A line that the records do not support is red.

## Changed

- Changed means changed against the base: `git diff --name-only origin/BASE...HEAD`. BASE is the PR's base branch,
  usually `main`.
- It never means changed since the previous PR head. A Story or prompt that a merge from the base brought in is not
  changed.
- A changed Story is a Story whose Story file or test file changed, or whose test reaches a changed prompt.

## Runtime lines

- Commit every change. Then run `pdd test` for each changed Story.
- Write one `Runtime:` line for each changed Story, with the verdict first:
  ```text
  Runtime: PASS (user_stories/format-bytes.md, 19/19 checks)
  Runtime: not run (user_stories/package-repository.md: native-only prompt, no Runtime test)
  ```
- A PASS of a Story that the PR does not change never counts.

## A failed check is a FAIL

- One step with no answer (for example `graph-provider-failure`) makes its Story `no verdict` (exit 3, 4 or 5). Other
  steps of the same check can still fail.
- When the line shows fewer passed checks than the total (`no verdict · 10 of 13 criteria · 17/19 checks`), open the
  report and read each step.
- A step that shows `expected X, got Y` is a failed check. Find the cause and fix it (RUNBOOK §11 "After a ✗").
  Never write a failed check as `not run`.
- Only a check with no failed step is no verdict.

## When `not run` is allowed

- `not run` is only for a cause that this PR cannot fix: a native-only prompt, a Story with no Runtime test, no
  verdict with no failed step, maintenance (below), or a refusal that pdd gives no fix for.
- A refusal with a fix from pdd is this PR's work. Apply the fix and check again.
- Write the exact cause in the line: `Runtime: not run (STORY: CAUSE)`.

## Large whole numbers

- For a parameter that takes a Number, write a whole number outside ±(2^53−1) in its exact Number spelling, for
  example `"seconds": 4.2501298345826807e+24` for 3600 × 2^70. The interpreter admits it with `"type": "integer"`.
- Write each scenario number with `String(n)` in JavaScript. Between 2^53 and 1e21, `String(n)` gives plain digits,
  so use `n.toExponential()` there.
- Never write a scenario number with `json.dumps` of a Python int. It gives plain digits. The interpreter refuses
  plain digits outside ±(2^53−1) before execution (`scenario-integer-out-of-range`, 0 AI calls).
- When pdd warns `If the parameter takes a Number, write its exact Number spelling …`, write that spelling and check
  again. This refusal is never a reason for `not run`.
- Only a value that no Number holds (2^53 + 1, or a BigInt parameter) stays in plain JSON digits. Then only the
  repository's own vector test checks it.
- Do not change the input type or the expected value to fit the interpreter.

## Maintenance

- Do not wait for maintenance. pdd prints `The interpreter is in maintenance until HH:MM UTC (…)` before it sends
  anything.
- Stop pdd then. Write `Runtime: not run (maintenance until HH:MM UTC)` with the end time that pdd printed. This one
  line stands for each changed Story that pdd did not send.
- Autopilot sends the check itself when maintenance ends, and it rewrites the line. Never send it again yourself.
- Never cut short a check that pdd has already sent.

## Vectors in the Evidence line

- `vectors=` counts the replay files (`*.vectors.test.*`) that the PR changes or that read a changed scenario file.
- Count `node:test` tests (the `# tests` and `# pass` lines), not steps or checks, for example `vectors=pass (36/36)`.
- Give only the counts that you saw.

## After a merge from the base

- Check that the fix is still needed.
- Check out the new merge base (`git merge-base origin/BASE HEAD`) in a throwaway worktree. Copy in the PR's changed
  tests and run them.
- When they pass on the base code too, the base already holds the fix. Keep the base's code, keep only what the base
  does not hold, and say so in the PR body.

## For the reviewer

- A Runtime PASS counts only for a changed Story (above). A PASS of another Story proves nothing for this PR.
- A failed step inside a check with no verdict is a FAIL. When the checks did not all pass, open the report.
- A `not run` line needs a cause from "When `not run` is allowed". A cause that pdd gives a fix for is a must-fix.
- A config or metadata file (`package.json`, a lock file, CI settings) needs no prompt and no Story. Never ask for a
  new prompt for it. Ask for a test only when the change alters a result that users see.
