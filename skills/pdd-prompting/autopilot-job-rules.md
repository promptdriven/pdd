# Autopilot core job rules

Read this whole file before you write or check the PR body. It is short on purpose: one read holds all of it. The
long reference is RUNBOOK.md §15 "Autopilot core jobs", with §3, §11 and §17. A tool output over about 10,000 tokens
loses its middle: read big files in parts.

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
- Write one `Runtime:` line for each changed Story. Put the verdict first. Then put the Story file path (as
  `git diff` shows it) first in the parentheses:
  ```text
  Runtime: PASS (user_stories/format-bytes.md, 19/19 checks)
  Runtime: FAIL (user_stories/format-bytes.md, 2 of 19 checks failed: steps format-10, zibi)
  Runtime: not run (user_stories/package-repository.md: native-only prompt, no Runtime test)
  ```
- A single line with no Story (for example `Runtime: PASS`) is valid only when the PR changes one Story or none.
- Two lines for the same Story are red.
- A PASS of a Story that the PR does not change never counts.
- A FAIL line blocks the merge.

## A failed check is a FAIL

- One step with no answer (for example `graph-provider-failure`) makes its Story `no verdict` (exit 3, 4 or 5). Other
  steps of the same check can still fail.
- When the line shows fewer passed checks than the total (`no verdict · 10 of 13 criteria · 17/19 checks`), open the
  report and read each step.
- A step that shows `expected X, got Y` is a failed check. Find the cause and fix it (RUNBOOK §11 "After a ✗").
  Never write a failed check as `not run`.
- Only a check with no failed step is no verdict.

## When `not run` is allowed

- `not run` is only for a cause that this PR cannot fix: a native-only prompt, no verdict with no failed step,
  maintenance (below), or a refusal that pdd gives no fix for.
- A changed Story with no Runtime test is no such cause. Write its Runtime test (one step for each criterion) and run
  `pdd test`, or mark the owning prompt's interface native-only with a reason.
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
- Stop pdd then. For each changed Story that pdd did not send, write `Runtime: not run (STORY: maintenance until
  HH:MM UTC)` with the end time that pdd printed.
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

## Choices and questions

- Autopilot decides when at least one reasonable fix solves the problem and breaks nothing that people use today: pick
  that fix and list it in the PR body under "Choices Autopilot made:", one line each with its reason
  ("- CHOICE (REASON)"), with "(changes public behavior: WHAT)" when users see a change. For example, "make remove
  safer" is decided: ask y/N only in an interactive terminal, --yes skips it, scripts stay unchanged; nothing is asked.
- A pdd-bug or pdd-small-change run never asks a choice question: pick the fix that makes the reported behavior right
  with the least surprise.
- With `decisions` `decide` (the default): never ask a person about a choice. Decide every choice yourself,
  product-direction ones too, and list each; list the big ones first, each marked "(big)". A choice question is never
  posted: Autopilot starts the job once more with "Autopilot decides this choice: do not ask."
- With `decisions` `ask`: a choice may be a question (`"kind":"choice"`) only when every reasonable fix breaks
  something that people use today, or, in a pdd-feature run, for a product-direction decision that the issue and the
  answers above do not settle: whether a new feature area or capability should exist, how a feature works at the
  design level when there are two different designs, removing a feature, an on-purpose change to a core contract,
  security, privacy or data policy, or something that costs money; an open trusted issue that asks the same product
  question counts too. Then do not choose and open no PR. Decide and list every other choice. An issue gets at most
  one choice question.
- A bug fix may change an approved rule (Serhan, D1): when the fix of a pdd-bug or pdd-small-change run changes a
  rule in an approved prompt, change it without asking and list it with "(changes approved rule: OLD -> NEW)", so a
  person sees it. The repository's approval setting still applies to the changed prompt.
- Two cases always go to a person, in every run: a change against a person's recorded answer to an earlier question
  (an answer above, a decision issue), and a change of what blocks merges (a new required check, a gate, a hash pin,
  CI policy). Do not make such a change: write the needs-person result with `"kind":"blocker"`. A real blocker (missing access or a secret, an issue that contradicts
  itself, work that cannot be done) is `"kind":"blocker"` too.
- The needs-person result asks exactly one question with 2 or 3 options, so a person can answer with one letter:
  ```json
  {"outcome":"needs-person","kind":"blocker|choice","question":"<one plain question>","options":["<answer A>","<answer B>"],"recommended":"<the letter you recommend>"}
  ```
- A vague issue is never a reason to ask. When the issue, or a person's answer above, settles a choice, build.
- Autopilot posts the question on the issue, adds `pdd:needs-decision` and says: "Please answer in a comment (one
  letter is enough)." A trusted person's reply ends the wait: at its next check Autopilot reads the answer, removes
  the label itself and goes on. The next job gets the answer.

## For the reviewer

- A tool output over about 10,000 tokens loses its middle, so never read the whole PR's diff in one call. Run
  `git diff --stat` first, then read one file per command. End the summary with "Read: FILE, FILE, ...".
- A Runtime PASS counts only for a changed Story (above). A PASS of another Story proves nothing for this PR.
- A failed step inside a check with no verdict is a FAIL. When the checks did not all pass, open the report.
- A `not run` line needs a cause from "When `not run` is allowed". A cause that pdd gives a fix for is a must-fix.
- A config or metadata file (`package.json`, a lock file, CI settings) needs no prompt and no Story. Never ask for a
  new prompt for it. Ask for a test only when the change alters a result that users see.
- Every choice that the issue did not settle must be listed in the PR body under "Choices Autopilot made:" with its
  reason (with "(changes public behavior: ...)" when users see a change); a missing or wrong line is a P2 must-fix
  (fix the list).
- A bug or small-change fix may change a rule in an approved prompt; it must be listed with "(changes approved rule:
  OLD -> NEW)", and a missing mark is a P2 must-fix (fix the list). A change against a person's recorded answer to an
  earlier question, or a change of what blocks merges (a required check, a gate, a hash pin, CI policy), is a P1
  must-fix in every mode: undo it, or end with the needs-person result `"kind":"blocker"`.
