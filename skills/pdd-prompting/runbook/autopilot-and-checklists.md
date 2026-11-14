# Runbook: Bug Workflow, PR Fields, Checklists, Autopilot, and Handoffs

> Part of [RUNBOOK.md](../RUNBOOK.md) — see the router table in `../RUNBOOK.md` for other `§N` sections.

## 14. Bug workflow

1. Reproduce: turn the issue into a test. Add a criterion to the story and a step that checks it to the story's test file.
   The expected value comes from the issue and the person.
2. Run `pdd test <story>` on the CURRENT prompt. Do not change the prompt first.
3. ✗ failed: tell the person "Verdict: the bug is in the PROMPT (its check fails on the issue's case)." Find the
   cause first (section 11, "After a ✗"). Fix the prompt (set draft, fill the hash) and check again: at most 2 fix
   rounds, then ask the person.
4. ✓ passed: tell the person "Verdict: the prompt is right; the bug is only in the CODE." Keep the correct prompt
   unchanged. The code-only checker route below proves the code fix.
5. For a prompt bug the check report shows before ✗ → after ✓; for a code-only bug show before ✓ → after ✓. `pdd simulate <story>` opens with the issue's input ready.
- The failing check of step 2 is the "before" evidence. If the prompt changed after it, register that saved result
  for the same Story. Name a full local commit id whose files are exactly the checked files (commit an exact
  reconstruction if that state was never committed). For run 18 and test `tests/count-words.json`:
  `pdd workflow evidence-associate 18 --workspace . --stage before --commit SHA --test tests/count-words.json`, then
  save `pdd test --read BATCH --json` to a file outside the repository and run
  `pdd workflow evidence 18 --summary /tmp/before.json`. pdd refuses a commit whose selected files do not hash to the
  batch's source. No new check is sent, and the result never counts as a current pass, check or approval.
- If no prompt owns the behavior, say in reproduce: "No prompt exists yet for this behavior, so the bug can only be
  in the code." The verdict line is "Verdict: no prompt covers this yet; the bug can only be in the code." Write the
  prompt from the issue, and write "before: no prompt" in PR 1.
- Put the verdict line first in the gate message, before any details.
- Keep the change small: change one prompt when you can, and test only the criteria of the bug.
- PR 1 must not make the repo's own tests fail. Put a new failing code test in PR 2, or mark it `todo` in PR 1.
  Never offer to merge PR 1 while the repo's tests fail on its branch.

**Independent checker: code-only bugs.** Use this route only for a bug with the recorded Story-gate verdict
"the prompt is right; the bug is only in the CODE". Compare the owning prompt and required context on the old
and new snapshots: they must be unchanged. Check the same issue-derived Story and expected cases on each
snapshot. Both prompt checks must pass in full. Each counts only when it matches the Story, the test cases and
the prompt source of its snapshot, from a fresh run (not cached); unavailable or unverifiable results are no
verdict, never an assumed pass.

Independently run the same native regression against the old code and the corrected code, using the same
expected cases and public boundary. The old code must fail an assertion for the issue's reason and the new
code must pass. A pre-target crash, setup error, missing test or passing old code is not proof. Keep the exact
snapshot/head identities, commands, exits and failing assertion in the checker evidence. Replay and formal
checks in §17, independent review, exact-head suites, approvals and merge rules still apply.

The PR body must state: prompt unchanged and passing on old and new snapshots; native regression fails on
old code for the bug's reason and passes on the new code. Retain the real report links and counts, native
old-code proof and limitations. Do not label the old prompt as failing. A wrong or changed prompt uses the
prompt-bug route: the old prompt must fail the issue case and the corrected prompt must pass. No owning
prompt uses the existing "before: no prompt" route, never this exception.

Autopilot waits saved as `capability:route-code-only-checker` wake through the installed capability rule
(#3112). Keep prior verdicts and route history. A wake supplies no approval or checker PASS; revalidate the
current candidates before a new verdict.

## 15. PR text

In a pdd workflow run, pdd writes the PR title and text. The top is for people: a status line (ready, waiting or
blocked), the user story, a short summary, the cases, what changed, a table of checks (PR 1) or proof (PR 2) and
one approval, next or merge line. pdd fills the status line and the tables only from its own records: saved `pdd test`
and `pdd lint` results, the replay evidence (§17), the old-code proof, review.md, CI and the checker verdict. It says
✅ only when each record that the PR needs is there and current. `pdd workflow status 42` (the run's issue) refreshes the status line
and the rows of each open PR ("Updated <time>"). All the rest (pdd result lines, your step summaries, approvals,
verify.md) stays whole in a closed "Details for tools and audits" section. pdd owns the description: it rewrites the
part above Details at each status and all of it at each push. Put notes for people in a PR comment.

### Small-change issue checklist

The plan in scope.md lists every requested item from the complete issue and trusted
follow-up comments. Preserve each item through change and verify. Mark it pending,
done with concrete evidence, or excluded with a reason and an exact quote from the
issue that permits exclusion. The run's plan cannot narrow the issue. The fresh
checker first derives its own request inventory from the original issue and trusted
follow-ups, then compares it with the checklist and PR diff. Missing requests,
unjustified exclusions, pending work and unsupported done claims are must-fixes.
A passing wording/structure test does not prove that a requested behavior is correct.

Save the checklist outside source, at `<run-folder>/small-change-checklist.json`:

```json
{
  "schema_version": "pdd.small-change-checklist.v1",
  "run_id": "<run ID>",
  "source": {"kind": "git-content-v1", "sha256": "<current content fingerprint>"},
  "items": [
    {"id": "R1", "request": "Correct the generated setup instructions",
     "source": "https://github.com/example/project/issues/17",
     "quote": "Correct the generated setup instructions", "state": "done",
     "evidence": "Generated instructions checked with the setup fixture"},
    {"id": "R2", "request": "Add a picture",
     "source": "https://github.com/example/project/issues/17",
     "quote": "Optionally add a picture", "state": "excluded",
     "exclusion": {"reason": "The issue makes the picture optional",
                   "quote": "Optionally add a picture"}}
  ]
}
```

This example is synthetic. Item ids are unique and nonblank. Keep source URLs and
exact request quotes, including trusted comment URLs. Update the fingerprint with
`sourceFingerprint(root)` from `src/workflow-replay.mjs` after source edits; never
replace a missing item with a smaller inventory. The native reader validates shape,
current source and completion evidence. It does not establish semantic coverage or
judge whether a quote permits exclusion. The independent checker does those checks
against the issue. The PR shows every item's state, quote and evidence or exclusion.
Missing checklist evidence waits; malformed/stale evidence and must-fixes block ready.

The structured `formal` block in `replay-evidence.json` (§17 and
the record contract at `docs/replay-evidence.md`) is the only formal exemption field.
For documentation-only work, record `result: "not_applicable"`, a specific `scope`
and `reason`, and `control_outcome: "not_run"`. Use the normal schema_version,
run_id and current source fingerprint; scenario vectors are not required for this
standalone block. Do not invent a proof or control. Body, Summary, Proof and saved
status read the same validated field. A scope/formal note cannot override it.
A one-PR small-change requires a recorded formal result, even without a Story or Rules to check.
Missing formal evidence waits before formal step completion and blocks readiness after completion;
malformed, stale, failed or not_run evidence cannot say ready. A valid exemption
means not applicable, never proved. The checker verifies that the diff fits it.
Other workflows keep their step-completion policy for a missing formal block unless a known Story has
`## Rules to check`; malformed or stale supplied evidence blocks readiness. This adds no person gate.

### Agent PR fields

Give pdd the human parts as labeled lines in your `done` summary, one per line. A later line with the same label
replaces an earlier one, also from a later step of the same PR:

| Label | PR 1 (prompt, Story and tests) | PR 2 (code) |
|---|---|---|
| `Title:` | what must be true | what is true after the merge |
| `Problem:` | the wrong or missing behavior, in one sentence | kept from PR 1 |
| `Cause:`, `Fix:`, `Result:` | — | one sentence each |
| `Case:` | one line per issue case: input, today, expected | input, before, after, expected |
| `File:` | `File: PATH — NOTE`, at most one short note per file | the same |

A one-PR run (small change) uses `Problem:`, `Change:` and `Result:`. Use `Area:` only when the owning prompt's
name is not a good title area. PR 1's Verdict is the verdict line of §14. pdd writes "This PR", the user story (from
the Story's "As a …" line, §2), the changed files and their +/− counts itself. Your words never fill a table: "CI is
green" in a summary stays your words. In the PR title and description your words cannot close an issue: pdd breaks
each closing keyword (fix, close, resolve and their forms) in the title, the summary, the cases, the file notes and
verify.md, so only pdd's `Closes #N` closes one. Code spans and code blocks stay as you wrote them (GitHub reads no
reference there). A commit message can close an issue, so do not write "Fixes #N" in one. Outside a workflow run (including integration or release PRs into `main`), write one `Closes #N` line per completed issue in the PR body, and `Refs #N` for any partial issue. In the readable part your
words also cannot add a link or a mention. Separate the cells of a `Case:` line with `|`; put a value that has a `|`
in a code span. Do not paste logs, warnings or full paths of this computer (`/Users/…`). PR 1 cannot merge while a
prompt in it is still draft.

```text
Verdict: the prompt is right; the bug is only in the CODE.
Before ✓ 6 of 6 criteria https://…/r/… → after ✓ 6 of 6 criteria https://…/r/…
Prompt tests (format-price): ✓ 6 of 6 criteria · 6/6 checks · 6 AI calls
Report (format-price): https://…/r/…
Title: every price shows dollars and two cent digits
Case: 1205 | $12.50 | $12.05
```

In PR 2 the same case has four cells: `Case: 1205 | $12.50 | $12.05 | $12.05`.

### Autopilot core jobs

A job of the Autopilot core engine (`pdd autopilot start --engine core`) makes one PR with no workflow run. It
writes the `Runtime:` lines and one `Evidence:` line in the PR body. Autopilot checks each line against its own
records. A line that the records do not support is red. The same rules, short enough for one read, are in
`autopilot-job-rules.md` of the pdd-prompting skill; a job reads that file in full.

- **Skill choice:** use `pdd-small-change` only when every planned file is an unowned path `d` file outside PDD (docs,
  guides, CI, lock files, packages, non-behavior config or metadata, or test-only maintenance — never `*.prompt.md`,
  `user_stories/*.md`, or product/app code), also when the issue is written as a bug. Write no new Story or prompt for
  path `d` files. If an issue touches prompt-owned or product/app code (`src/`, `app/`, etc.), even when no prompt
  exists yet, pick `pdd-bug` or `pdd-feature` instead. If a `pdd-small-change` run already touched owned or product
  code, note it and keep the Story test, replay and `Runtime:` evidence or rerun under `pdd-bug` or `pdd-feature`. A
  repair on a path-`d`-only PR keeps path `d` without adding a new Story or prompt.
- **Changed** means changed against the base: `git diff --name-only origin/BASE...HEAD` (BASE is the PR's base
  branch, usually `main`). It never means changed since the previous PR head. A Story or prompt that a merge from the
  base brought in is not changed. A changed Story is a Story whose Story file or test file changed, or whose test
  reaches a changed prompt.
- Commit every change, then run `pdd test` for each changed Story, all of them in one `pdd test` batch where you
  can (`pdd test STORY STORY ...`); every Story whose test reaches a changed prompt counts, however many. Write one
  `Runtime:` line for each changed Story.
  Put the verdict first. Then put the Story file path (as `git diff` shows it) first in the parentheses:
  ```text
  Runtime: PASS (user_stories/format-bytes.md, 19/19 checks)
  Runtime: FAIL (user_stories/format-bytes.md, 2 of 19 checks failed: steps format-10, zibi)
  Runtime: not run (user_stories/package-repository.md: native-only prompt, no Runtime test)
  ```
  A single line with no Story (for example `Runtime: PASS`) is valid only when the PR changes one Story or none. Two
  lines for the same Story are red. A PASS of a Story that the PR does not change never counts. A FAIL line blocks
  the merge.
- A failed check is a FAIL, also when its check has no verdict (§11). Find the cause and fix it ("After a ✗"). Never
  write a failed check as `not run`.
- `not run` is only for a cause that this PR cannot fix: a native-only prompt, no verdict with no failed step, or a
  refusal that pdd gives no fix for. A changed Story with no Runtime test is no such cause: write its Runtime test
  (one step for each criterion) and run `pdd test`, or mark the owning prompt's interface native-only with a reason.
  A refusal with a fix from pdd is this PR's work. For example, a whole number outside the interpreter's range: apply
  the Number spelling that pdd prints (§3 "Large whole numbers") and check again.
- Do not wait for maintenance. When pdd prints that the interpreter is in maintenance (§11), it has sent nothing yet.
  Stop pdd then. For each changed Story that pdd did not send, write `Runtime: not run (STORY: maintenance until
  HH:MM UTC)` with the end time that pdd printed. Autopilot sends the check itself when maintenance ends and rewrites the line. Never send it again yourself. Never
  cut short a check that pdd has already sent.
- `vectors=` counts the replay files (`*.vectors.test.*`) that the PR changes or that read a changed scenario file.
  Count `node:test` tests (the `# tests` and `# pass` lines), not steps or checks, for example `vectors=pass (36/36)`.
- After a merge from the base, check that the fix is still needed. Check out the new merge base
  (`git merge-base origin/BASE HEAD`) in a throwaway worktree, copy in the PR's changed tests, and run them. When they
  pass on the base code too, the base already holds the fix. Then keep the base's code, keep only what the base does
  not hold, and say so in the PR body.

**Choices and questions.** These rules are in rule 1 of the job brief too.

- Autopilot decides when at least one reasonable fix solves the problem and breaks nothing that people use today: pick
  that fix and list it in the PR body under "Choices Autopilot made:", one line each with its reason
  ("- CHOICE (REASON)"), with "(changes public behavior: WHAT)" when users see a change. For example, "make remove
  safer" is decided: ask y/N only in an interactive terminal, --yes skips it, scripts stay unchanged; nothing is asked.
- A pdd-bug or pdd-small-change run never asks a choice question: pick the fix that makes the reported behavior right
  with the least surprise.
- With `decisions` `decide` (the default): never ask a person about a choice. Decide every choice yourself,
  product-direction ones too, and list each; list the big ones first, each marked "(big)". A choice question is never
  posted: Autopilot starts the job once more with "Autopilot decides this choice: do not ask."
- With `decisions` `ask`: routine compatible choices of command syntax, options or data representation are agent
  decisions when a safe, low-surprise choice exists. Preserve existing APIs, defaults and behavior unless the request
  authorizes a change. Several valid designs alone are not a reason to ask. A choice may be a question
  (`"kind":"choice"`) only when every reasonable fix breaks something that people use today, or, in a pdd-feature
  run, when the choice actually changes product direction: whether a new feature
  area or capability should exist, removing a feature, an on-purpose change to a core contract, security, privacy or
  data policy, or something that costs money; an open trusted issue that asks the same product question counts too.
  Then do not choose and open no PR. Decide and list every other choice. An issue gets at most one choice question.
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

For the reviewer:

- Non-code path `d` files (docs, config, CI settings, `package.json`, lock files, and test files or fixtures) need no
  prompt and no Story; never ask for a new prompt or Story for them, and treat a new prompt or Story added for a
  non-code file as a must-fix.
- Every choice that the issue did not settle must be listed in the PR body under "Choices Autopilot made:" with its
  reason (with "(changes public behavior: ...)" when users see a change); a missing or wrong line is a P2 must-fix
  (fix the list).
- A bug or small-change fix may change a rule in an approved prompt; it must be listed with "(changes approved rule:
  OLD -> NEW)", and a missing mark is a P2 must-fix (fix the list). A change against a person's recorded answer to an
  earlier question, or a change of what blocks merges (a required check, a gate, a hash pin, CI policy), is a P1
  must-fix in every mode: undo it, or end with the needs-person result `"kind":"blocker"`.

## 22. Bounded handoffs and measurement

This is an agent instruction example, not an executable Runtime program. The workflow skill owns gates, role eligibility and repair limits; §11 owns CHECK waiting, §17 owns code verification and §10 owns interpreter budgets. Keep those instructions available. No new wait API is needed.

### A small handoff through a long check

Use a small task such as a change to `examples/fakes/service.prompt.md`, its `user_stories/fake-service.md` and `test/runtime/fake-service.json`. The following is an illustrative route, not approval or a command to spend calls. The coordinator records the task, accepted decisions, source identity, exclusive file owners, current stage, unresolved failures/approvals and durable report paths in the run folder. It keeps that ledger between stages instead of each child's full conversation.

1. **Author.** Give a fresh author the governing AGENTS and skill instructions, full prompting guide, relevant RUNBOOK sections, task and acceptance, owning prompt, dependencies and relevant callers and cases. Assign exclusive draft paths without inherited chat. The author returns the paths, changed behavior, missing context, case coverage and open choices; the coordinator shows the required Story gate.
2. **Long CHECK.** Give a fresh checker the governing instructions, frozen drafts, dependencies, source, authorized call cap and §11. After authorization, run `pdd test fake-service --max-calls 6` once. Retain the printed batch/read command, report links and each Story's actual verdict, including failures, refusals and no verdict. For a check expected to exceed a short wait, choose the longest blocking wait allowed by the tool and the active progress and cancellation requirements on the first call. If it returns a session or cell ID, continue bounded waits on that same ID until terminal, cancelled or interrupted, within tool limits. These are tool wait continuations, not separate process/status polling; do not restart or separately poll an uncertain check. If the tool stops CHECK, use its printed saved-batch read command as §11 directs; do not resubmit uncertain work. The CLI's progress stream and internal receipt polling need no coordinator turn; reads can continue lint-held checks under §11.
3. **Repair.** Give a fresh author the failed criterion, exact input, expected and actual values, owning prompt, dependencies, report and authorized repair scope. Preserve the original failure and expected values, make a minimal repair, return changed prompts to the required gate and check only the affected Story under the existing rules.
4. **Independent verify.** After the person requests code and build completes, give a fresh eligible verifier the approved cases, current source, dependencies, regressions and failure evidence. Verify the real public boundary and regressions under §17. Independent review remains separately eligible; unrun or unmapped checks are not passes.

For a long external native process, retain its runner session ID or PID, start time, command, stdout/stderr and terminal receipt. Use that runner's completion wait or exit notification, not CHECK's batch recovery. Report compact progress or failure changes from the existing runner/log stream. Cancel only the owned session or process through its supported control, then wait for termination and record the actual exit, signal or unknown result. If the runner cannot notify or wait until exit, state that limit and record necessary bounded status turns. A missing receipt or lost connection is unknown, not success or permission to start a second process.

The coordinator resumes reasoning on a stage change, actionable failure, user steering or completion. Preserve source evidence, dependencies, failures and approvals; request missing governing context. After a successful CHECK, follow the existing prompt/Simulator review and person approval before PR 1, then ask for code. After build, follow verify, formal and fresh independent review under §17. Keep a native failure's first receipt and repair or rerun under the existing limit; record incomplete results and recovery decisions after interruption. Try stays optional; ask the person and wait for agreement before it starts.

In a synthetic prompt-only benchmark, independent draft verification stays a draft/manual review. It never claims that an unchanged native implementation fulfills the newly drafted rule, and it is separate from §17 code proof.

### Freeze and measure before setting a target

Keep the benchmark manifest, raw logs, context inventories, scripts and results in the task's run folder, outside product commits. Freeze one small task/source snapshot, acceptance and full coverage, model/effort, CLI/agent/shell/tool versions, permitted tools, cache state, run order/repetitions and repair/stop policy. Both arms get these same conditions. The baseline is current shipped guidance, including fresh agents and one-call CHECK; the revised arm changes only the selected guidance. Freeze each arm's bytes before starting. A version change or unequal outcome/coverage limits comparison.

Record coordinator, each child and interpreter separately, by actual session/request identity with provenance. For each report requests, total input, cached input, uncached input, output, start/end, wall time and terminal outcome. Keep absent usage unknown. Derive uncached as total minus cached only when the receipt defines cached as a subset; do not add cached to a total that already includes it. Deduplicate provider receipts and nested interpreter accounting by request identity. Overall elapsed time is arm end minus start; never sum overlapping role durations.

Record each role's initial brief, inheritance setting, supplied file paths/bytes, handoff bytes and tool/report output bytes. Distinguish supplied files from content actually read, and available per-request input from retained-history telemetry. File bytes do not establish token counts, cache reuse or what the model retained. If retained-history telemetry is unavailable, say so.

Classify tool-internal polls, saved-report reads, model-driven waiting/status and actionable reasoning separately. A report read may be internal or model-driven; count actual model requests rather than report files. Include failed, aborted, refused and missing runs. Compare equivalent completed outcomes and disclose incomplete attribution. Synthetic accounting fixtures or fake-clock waits prove only their stated arithmetic/boundary; they do not establish model savings. Choose numeric regression targets only after the controlled baseline. Dollar claims also need authoritative measured usage and applicable rates. Present the frozen task and proposed per-arm authoring/interpreter ceilings for a person's budget decision before any live arm.
