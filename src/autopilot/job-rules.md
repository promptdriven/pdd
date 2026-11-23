# Autopilot core job rules

Read this whole file before you write or check the PR body. It is short on purpose: one read holds all of it. Load
`$PDD_SKILLS/pdd/SKILL.md` and the co-located references (`prompting.md`, `stories.md`, `verification.md`) on demand. A tool output over about 10,000 tokens
loses its middle: read big files in parts.

These rules are for a job of the Autopilot core engine (`pdd autopilot start`). The job makes one PR.
It writes the `Runtime:` lines and one `Evidence:` line in the PR body. Autopilot checks each
line against its own records. A line that the records do not support is red.
Do not self-spawn a Fresh Verifier subagent during build or repair: Autopilot runs its own independent Blind Fresh Reviewer right after your PR.

## Mode choice (inside `$PDD_SKILLS/pdd/SKILL.md`)

- Use `small-change` mode only when every planned file is an unowned path `d` file outside PDD (docs, guides, CI, lock
  files, packages, non-behavior config or metadata, or test-only maintenance — never `*.prompt.md`,
  `user_stories/*.md`, or product/app code), also when the issue is written as a bug.
- If an issue touches prompt-owned or product/app code (`src/`, `app/`, etc.), pick `bug` or `feature` mode instead. Follow the 100% Truth Rule in `prompting.md`: update any existing owning prompt before code; for unowned legacy code, either adopt/extract a clean pure PDD module with a top-of-file `Prompt:` header or apply a surgical brownfield code fix verified with Red→Green TDD (never write half-prompts).
- Write no new Story and no new prompt for a path `d` non-code file.
- If a `small-change` run already touched owned or product code, note it and include the Story test, replay and
  `Runtime:` evidence or rerun under `bug` or `feature` mode.
- A repair on a path-`d`-only PR keeps path `d` without adding a new Story or prompt.

## Changed

- Changed means changed against the base: `git diff --name-only origin/BASE...HEAD`. BASE is the PR's base branch,
  usually `main`.
- It never means changed since the previous PR head. A Story or prompt that a merge from the base brought in is not
  changed.
- A changed Story is a Story whose Story file or test file changed, or whose test reaches a changed prompt.

## Runtime lines

- Commit every change. Then run `pdd test` for each changed Story, all of them in one `pdd test` batch where you can
  (`pdd test STORY STORY ...`). Every Story whose test reaches a changed prompt counts.
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
- A step that shows `expected X, got Y` is a failed check. Find the cause and fix it in the owning prompt or scenario.
  Never write a failed check as `not run`.
- Only a check with no failed step is no verdict.

## When `not run` is allowed

- `not run` is only for a cause that this PR cannot fix: a native-only prompt, no verdict with no failed step,
  maintenance (below), or a refusal that pdd gives no fix for.
- `real-binding-unavailable`, expired external logins, stopped daemons, or missing real end-to-end tests are never a
  silent skip or pass in either `auto` or `observe` mode. Autopilot parks auth/tool outages without burning repair
  rounds and resumes validation on the same commit head once healthy.
- A changed Story with no Runtime test is no such cause. Write its Runtime test (one step for each criterion) and run
  `pdd test`, or mark the owning prompt native-only with frontmatter kind and reason.
- A refusal with a fix from pdd is this PR's work. Apply the fix and check again. For `impossible-result-value-pointer`,
  set `result_value_pointer` to `""` when the port returns the value directly, or state the exact returned JSON object
  keys in the prompt's Ports section so `result_schema` includes that pointer.
- Write the exact cause in the line: `Runtime: not run (STORY: CAUSE)`.

## Real end-to-end tests

- For every non-doc runtime change, write real end-to-end tests upfront for the changed surface instead of mock-only
  unit tests alone:
  - CLI or scripts: run the real subprocess/CLI binary and assert stdout, stderr, files, and exit code.
  - API, server, or database: start a real local HTTP/WS server or real DB round-trip and assert real responses.
  - Web UI: exercise the real rendered flow in a browser (for example Playwright).
  - External tool, auth, or cloud integration: exercise the real live binding where healthy; never rewrite a real E2E
    check into mocks when a login or external service is down.
- For a bug fix, prove the regression test (including the real E2E check) fails on the merge base and passes on HEAD
  (`pdd prove --base origin/BASE --test ... --expect ...`).
- Never add silent validation skips (`test.skip` on validation/E2E tests or `real-binding-unavailable` local-skip
  bypasses). Docs-only changes need no E2E run.

## Large whole numbers

- For a parameter that takes a Number, write a whole number outside ±(2^53−1) in its exact Number spelling, for
  example `"seconds": 4.2501298345826807e+24` for 3600 × 2^70. The interpreter admits it with `"type": "integer"`.
- Write each scenario number with `String(n)` in JavaScript (and `n.toExponential()` between 2^53 and 1e21).
- Never write a scenario number with `json.dumps` of a Python int: plain digits outside ±(2^53−1) are refused before
  execution (`scenario-integer-out-of-range`, 0 AI calls).
- Only a value that no Number holds (2^53 + 1, or a BigInt parameter) stays in plain JSON digits and is checked by the
  repository's own vector test. Do not change the input type or expected value to fit the interpreter.

## Maintenance

- Do not wait for maintenance. pdd prints `The interpreter is in maintenance until HH:MM UTC (…)` before it sends
  anything.
- Stop pdd then. For each changed Story that pdd did not send, write `Runtime: not run (STORY: maintenance until
  HH:MM UTC)` with the end time that pdd printed.
- Autopilot sends the check itself when maintenance ends and rewrites the line. Never cut short an already-sent check.

## Vectors and formal proofs in the Evidence line

- `vectors=` counts the replay test files (`*.vectors.test.*`, `test_vectors*.py`, `*_vectors_test.go`, `tests/*vectors*.rs`) that the PR changes or that read a changed scenario file.
- `formal=` uses `proved_solver_code` (or `bounded`) ONLY when the formal suite imports/executes production code and passes a production-code mutation control (never claim `proved` for disconnected Z3 spec models — report `proved_spec_model` or `not-applicable`).
- Report exact observed counts (`passed/total`) from the repo's native test runner (`node:test`, `pytest`, `vitest`, `go test`, `cargo test`), never steps or checks, for example `vectors=pass (36/36)`. Give only counts you actually ran and saw.

## After a merge from the base

- Check that the fix is still needed by checking out `git merge-base origin/BASE HEAD` in a throwaway worktree,
  copying in the PR's changed tests, and running them.
- When they pass on the base code too, keep the base's code, keep only what the base does not hold, and say so in the
  PR body.

## Choices and questions

- When at least one reasonable fix solves the problem and breaks nothing that people use today, pick it and list it in
  the PR body under `Choices Autopilot made:` (`- CHOICE (REASON)`, adding `(changes public behavior: WHAT)` when
  users see a change).
- A `bug` or `small-change` mode run never asks a choice question: pick the fix that makes the reported behavior right
  with the least surprise.
- With `decisions` `decide` (the default): decide every choice yourself and list each, big ones first marked `(big)`.
- With `decisions` `ask`: routine compatible choices are agent decisions when a safe, low-surprise choice exists. Ask
  (`"kind":"choice"`) only when every reasonable fix breaks something people use today, or in `feature` mode when a
  choice changes product direction (new capability, removing a feature, core contract, security/privacy/data policy, or
  cost). An issue gets at most one choice question.
- A bug fix may change an approved rule: when a `bug` or `small-change` mode fix changes a rule in an approved prompt,
  change it without asking and note `(changes approved rule: OLD -> NEW)` in `Choices Autopilot made:`. The
  repository's approval setting still applies to the changed prompt.
- Two cases always go to a person as `"kind":"blocker"`: contradicting a person's recorded answer to an earlier
  question, or changing what blocks merges (a new required check, gate, hash pin, or CI policy). Real blockers (missing
  access/secret, contradictory issue) are `"kind":"blocker"` too.
- Return a needs-person decision as JSON with 2 or 3 options so a person can answer with one letter:
  ```json
  {"outcome":"needs-person","kind":"blocker|choice","question":"<one plain question>","options":["<answer A>","<answer B>"],"recommended":"<the letter you recommend>"}
  ```
- A vague issue is never a reason to ask. When the issue or an earlier human answer settles a choice, build.

## For the reviewer

- Read strictly the diff, owning prompts/Stories, and harness evidence — never trust PR prose alone. Run `git diff --stat` first, then read one file per command. End the summary with `Read: FILE, FILE, ...`.
- Verify every touched user-facing path is backed by real unmocked execution (`pdd prove` / `verify.paths` Feature Map, real CLI/HTTP/DB/browser/host probes — not mocked-only stubs) and run a fast 1-to-3 line Deliberate-Break Probe (flip 1–3 changed logic conditions/returns in a scratch edit, confirm an assertion fails, revert) on medium/big diffs.
- A Runtime PASS counts only for a changed Story (above). A failed step inside a `no verdict` check is a FAIL.
- A `not run` line needs a cause from "When `not run` is allowed". A cause that pdd gives a fix for is a must-fix.
- Non-code path `d` files (docs, config, CI, `package.json`, lock files, tests/fixtures) need no prompt and no Story;
  a new prompt or Story added for a non-code file is a must-fix.
- Every unsettled choice must appear under `Choices Autopilot made:` with its reason (and `(changes approved rule: OLD -> NEW)` when a bug fix changed an approved prompt rule). Contradicting a recorded human answer or altering merge blockers is a P1 must-fix: undo it or return `"kind":"blocker"`.
