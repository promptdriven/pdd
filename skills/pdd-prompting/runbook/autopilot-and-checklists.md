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

Autopilot core jobs (`pdd autopilot start --engine core`) open one PR without a workflow run and record `Runtime:` and `Evidence:` lines in the PR body. Read [`../autopilot-job-rules.md`](../autopilot-job-rules.md) in full when running an Autopilot core job; it is the single authoritative owner of skill choice, changed-Story scope, `Runtime:` / `Evidence:` syntax, `not run` admission, large whole-number spelling, and `Choices Autopilot made:` reporting.

## 22. Bounded handoffs and measurement

### A small handoff through a long check

Keep the coordinator thin and launch fresh subagents strictly in stage order only after prior-stage files exist on disk:

1. **Author:** supply the issue, owning prompt/Story/scenario paths, and `RUNBOOK.md` fast path in one complete brief; wait once with a long timeout (no short status polls).
2. **Check:** run one `pdd test` batch for all selected Stories; if the tool wait times out, resume with `pdd test --read` rather than resending.
3. **Repair:** give a fresh author the failing criterion, input, expected vs actual values, and owning prompt without changing expected values.
4. **Independent verify & review:** after `build`, run fresh eligible `verify`, `formal`, and `review` subagents under §17. For external native processes, wait on runner exit notifications rather than polling loops.

### Freeze and measure before setting a target

Keep benchmark manifests, logs, and scripts in the run folder outside product commits. Freeze task snapshot, model/effort, CLI/tool versions, cache state, and stop policy across baseline and revised arms. Record coordinator, child subagent, and interpreter sessions separately (`requests`, `input_tokens`, `cached_input`, `output_tokens`, wall time `end - start`, and terminal outcome; never sum overlapping durations or fabricate missing usage).
