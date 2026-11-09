# Readable workflow PR descriptions

Own `src/workflow-pr-body.mjs`. It renders the part of a pdd workflow PR that a person reads first (#3042): a title, a status line, the user story, a short summary, a cases table, what changed, one table of checks or proof and one approval, next or merge line. The [runner](workflow-runner.prompt.md) gathers the facts from Git, the run folder, pdd's own records, CI and the checker; this module only renders them and reads nothing itself. Everything else that pdd writes (IDs, batches, request IDs, step notes, agent notes, approval records, verify.md, inventory, replay text) stays whole in one closed Details section below. Nothing is lost.

## Evidence authority

For code PRs, the Summary Result and Proof table use the same recorded rows. The agent's Result remains in Details only. A Result claim cannot supply a gate or formal result.

Coverage validation is distinct from a defect proof: a current `old-passes` proof in a one-PR small-change with a complete, nonempty Git diff containing only test files and test helpers/fixtures is coverage validation when at least one executable test file has added lines. It says both snapshots pass and does not establish a defect fix; it does not block for old code passing. The runner supplies this classification as `records.proof.kind: coverage`; other proofs use `defect`. Unknown or incomplete diffs, fixture-only work, production changes, two-PR runs and bug/feature runs cannot receive this exception. All other gates, stale or missing evidence and failed tests keep their rules.

## Small-change scope and exemptions

For a one-PR small-change code PR (`single: true`), `records.checklist` is the request-evidence owner's
validated checklist. Show every item, in order, in `## Issue checklist`, with its
id, request, state, source, exact quote and completion evidence or exclusion
reason/quote. Escape these as inert table cells; do not truncate item text or
omit rows. The Proof table includes the checklist status and must-fix count.
Missing evidence waits; malformed/stale evidence and any must-fix block readiness.
Independent checker PASS still needs comparison with the original issue.

The existing structured `records.formal` block (from replay-evidence.json) is the
only formal exemption field. A documentation-only exemption uses
`result: not_applicable`, scope and a specific reason; prose alone never exempts.
A one-PR small-change needs a recorded formal result: missing waits until formal completes,
then blocks; stale/malformed and not_run block. A completed step is not a result.
Summary, Proof, Details and saved status consume that same validated block.
Keep the public [formal-evidence contract](../../docs/replay-evidence.md#reading-the-pr-status)
and both RUNBOOK copies aligned with this rule, including its exception to
"not needed". Other workflows keep their Story and replay policy. Formal evidence
requirements add no person gate.

## Agent fields

`readPrFields(texts)` reads labeled lines from the `done` summaries of a PR's steps, in step order. A line starts (after optional spaces and one `- ` or `* `) with exactly one label and a colon: `Title`, `Area`, `Problem`, `Cause`, `Fix`, `Change`, `Result`, `This PR`, `Verdict`, `Case` or `File`. A later line replaces an earlier line with the same label. `Case: INPUT | BEFORE | AFTER | EXPECTED` gives a cases row; 3 cells are `INPUT | BEFORE | EXPECTED` and 2 cells `INPUT | EXPECTED`; other cell counts and an empty input are ignored. A `|` inside a code span stays in its cell (`` `a || b` `` is one input), and a cell loses a trailing backslash, so `INPUT \| TODAY \| EXPECTED` copied from a Markdown table still gives three cells. The Case rows of the latest text that has any replace all earlier rows, at most 12. `File: PATH — NOTE` (or `-`, `–` or `:` as the separator, the path optionally in backticks) gives one short note for a changed file. It returns `{title?, area?, problem?, cause?, fix?, change?, result?, thisPr?, verdict?, cases, notes}`.

## User story

`userStory(text)` returns the first "As a …, I want …, so that …" statement of a Story file as one line, or null. The statement may start after `> `, a list marker or bold marks, and may wrap over following lines of its paragraph (it ends at a blank line, a heading, a list item, a fence, a table row or HTML). It needs "As a" or "As an", then ", I want" and "so that".

## Area and title

`prArea({area, files, workflow})`: the agent's `Area` field when it has a usable name, else the first changed `*.prompt.md` (its name without `.prompt.md` and a language suffix such as `_python`), else the first changed Story under `user_stories/` (not `PLAN.md` or `README.md`), else the first changed source file (a common source extension such as `.js`, `.ts`, `.py` or `.go`) outside test, fixture, doc, Story and prompt folders, else the first other such file that is not Markdown, JSON, a lock file or text, else the workflow name. The result is lowercase letters, digits, `.`, `_` and `-`, at most 40 characters.

`readablePrTitle({layout, workflow, area, statement, number, part})`: `spec(AREA): STATEMENT (#N · part 1: spec)` for PR 1, `fix(AREA): STATEMENT (#N · part 2: fix)` for a bug code PR, `feat(AREA): STATEMENT (#N · part 2: feat)` for a feature code PR and `fix(AREA): STATEMENT (#N)` for a one-PR run (`part` null). STATEMENT is the agent's `Title` field (PR 1: what must be true; PR 2: what is true after the merge), else the issue title, on one line. GitHub puts the title into the merge commit, and a closing keyword in a commit closes an issue; a commit message has no code spans. So in the whole statement, also between backticks, every closing keyword gets a zero-width space after it and so does each `@` before a name, as in [inert agent words](#inert-agent-words): the title `Fixes #5 by padding` closes nothing. GitHub refuses a title over 256 UTF-16 code units: cut only the statement, at a Unicode character boundary, and show ` …`; the type, area and suffix always stay.

## The readable part

`readablePrTop(facts, {fileLimit = 40})` returns `{text, notes}`. `notes` are lines for Details, for example "User story: … has no "As a …, I want …, so that …" line, so this PR has no User story section." Top to bottom:

1. One status line, computed only from the records below: `⛔ Not fixed yet` for a warning-light PR (`notFixed`: the runner's issue reference is `Refs #N` because of a `Not fixed yet:` line), with `; REASON` for each problem; else `⛔ Blocked: REASON; REASON` when any record shows a problem, else `⏳ Waiting for X, Y and Z` when a record that the PR needs is missing, stale or not finished, else `✅ Ready to merge`. So ✅ needs every required record, current: for a code PR of a two-PR run the old-code proof `proved` for the head, review.md with no must-fix when the area has a review step, the formal rule below when the area has a formal step, CI green and (not in a manual run) a checker PASS for the current head. Reasons: prompt tests fail, lint fails, N draft prompts to approve, N approved cases fail on the new code, replay evidence is blocked or incomplete, the old code (feature: the planted mistake) fails no case, formal check failed at INPUT, formal check WORDS (the formal rule below), an old-code proof problem (the changed tests fail on the new code, also pass on the old code, fail on the old code for another reason, a setup error, a stop, a time-out, too much output, the proof is unavailable, in a two-PR code PR the proof found no changed tests, any other outcome), review has N must-fix, CI fails, no CI checks configured (CI `none`: GitHub has no check for the head, so pdd never waits for one forever and never says ready), the checker says FAIL or is not sure, the checkers disagree on this head (a split), PR 1 (#N) is closed without a merge. Waiting: the source to be published (while a push is pending), pdd records for the new head (`headChanged`: GitHub shows a head that pdd did not publish), prompt tests on the current source (PR 1 with an "older source" result), a fresh old-code proof (`stale`), the old-code proof (`not-run`, or no proof record, in a two-PR code PR; a one-PR run may have none), the formal result (the formal rule below), the formal step (an area without replay evidence whose formal step is not done: `formalDone`), the review (no review.md verdict), CI, the checker (not in a manual run), and PR 1 as the red-pair rule below says. When `updatedAt` is a time, the line ends with ` · Updated YYYY-MM-DD HH:MM UTC`, the time pdd wrote it.
   - Formal rule (#3029), for a code PR with replay evidence in an area with a formal step. The replay result's `formal` is the [formal status](workflow-replay.prompt.md#the-formal-result-on-its-own); `rulesToCheck` is the runner's fact that a Story of the run has `## Rules to check` (true, false, or null when pdd found no Story file of the run). A recorded Failed result always blocks (formal check failed at INPUT). With scenario vectors (the status is `required`), a formal status that is not recorded holds the PR also when `rulesToCheck` is false: a missing status waits for the formal result while the formal step is not done and blocks after it (formal check missing); malformed and stale block. When `rulesToCheck` is false and the status is not `required`, nothing else about the formal check holds the PR. Else (true, or unknown) the PR needs a recorded Proved (bounded), Proved (solver) or Not applicable result: a recorded Not run blocks (formal check not run); a missing status waits for the formal result while the formal step is not done (`formalDone` not true), and blocks after it (formal check missing); malformed and stale block (formal check malformed (FIELD), formal check stale (source changed)).
   - Red pair (RUNBOOK §2): `pr1Order(facts)` gives PR 1's place for a code PR stacked on PR 1 that is not merged: `carried` when GitHub shows the run's base as this PR's base (`carriesPr1`) or PR 1's CI is failing (PR 1 then merges only with this PR, never alone): no wait for PR 1, but while this PR does not target the run's base yet it waits for this PR to target `BASE` (`baseBranch`, else "the base branch"); `first` when PR 1's CI is passing or `none`: waiting for PR 1 (#N); `ci` when PR 1's CI is pending or unknown: waiting for the CI of PR 1 (#N); `closed` when PR 1 is closed without a merge: blocked. A merged PR 1, no PR 1 or a code PR that is not stacked gives null and no wait.
   - With `notFixed`, the next line (after a blank line) is pdd's fixed sentence `Not fixed yet: this helps find the cause. The issue stays open.`. It is a limit, not a claim.
2. `## User story`: each Story line (at most 3), else no section and a note.
3. `## Summary`: PR 1 bullets **Problem**, **This PR** (the agent's field, else pdd's own "no code change. It holds the prompt `x.prompt.md`, the Story and N test files."), **Verdict**; a code PR **Problem**, **Cause**, **Fix**, **Result** (Result is generated from the recorded vector, formal and regression/coverage rows, including their old-code/control cells) ("Fix" is a closing keyword, so its label is `**Fix` + a zero-width space + `:**`, and "**Fix:** #5 …" closes nothing); a one-PR run (`single`, such as small-change) **Problem**, **Change** (else its Fix field), **Result**. Missing fields are left out; with no bullet there is no section.
4. Cases: PR 1 `## Expected behavior` with Input, Today (when any row has a before value) and Expected; a code PR `## Before / after` with Input, Before (when any row has one), After and Expected, where Expected shows ` ✓` when After equals it and ` ✗` when it differs. No section without rows. No acceptance criteria list.
5. `## What changed (+A −D, N files)`: the Git numbers; one bullet per file with its agent note, else its own `(+a −d)` (or `(binary)`), at most `fileLimit` files, then "…and N more files (see the Files tab)." N is `diff.count` when the facts carry it (a saved copy keeps only 40 files), else the number of files.
6. `## Checks` (PR 1, columns Check and Result) or `## Proof` (code PR, columns Check, New code and Old code; a feature run says Planted mistake instead of Old code, and its old-code proof cell then starts with "old code: "). Rows come only from pdd's records, never from agent words:
   - PR 1: Prompt tests (`pdd test`) with its result and one report link, "(older source)" when the saved source is not current, else "no pdd result (`pdd:no-verdict`)"; Lint (`pdd lint`); Prompts approved only when draft prompts remain; Full test suite (CI); Independent checker.
   - Code PR: Approved cases on real code (vectors) from the validated replay evidence: `✓ P of T` or `✗ F of T fail`, and in the second column `✗ N fail (as expected)` from the semantic mutation control; a blocked or not replayed record shows its reason. Formal check (SCOPE) from a recorded formal status: `Proved (bounded)`, `Proved (solver)`, `Failed at INPUT` (the counterexample), `Not run: REASON` or `Not applicable: REASON`, never "Proved" otherwise. A formal status that is not recorded, in an area with a formal step, gives `Formal check` with the replay owner's `formalStatusText(formal, rulesToCheck)` as `WORDS — DETAIL. Repair: STEP.`, then ` NOTE` when its note is not empty (the same words as the replay header, never a bare "not recorded"), or `not needed (no Rules to check in the Story)` only when its `notNeeded` is true. Without replay evidence (a small change), use the separately read `records.formal` status with the same result, scope, reason and control rules. For a one-PR small-change, a missing result waits until the formal step completes, then blocks; for other areas it retains the existing policy unless a known Story has Rules to check; a malformed or stale supplied block always blocks. A recorded Failed always blocks. A known Story with Rules needs Proved or Not applicable. Reading this block does not opt the area into scenario replay. With neither status source (legacy facts), show `Not recorded: pdd has no formal result for this run (see Details)`. Coverage validation (`kind: coverage`) shows a coverage label, pass in both snapshot columns, and an explicit limit that this is not a defect proof. Otherwise Regression tests (old-code proof) from the judged `pdd workflow prove` record, with the native test counts when known. Full test suite (CI) on this commit. Fresh review from the first line of review.md (`no must-fix` or `✗ N must-fix`, else not recorded) when the area has a review step. Independent checker.
   - A row that is not finished shows `⏳ pending` (CI that is pending, unknown or not yet read; a checker without a verdict). CI `none` shows `no CI checks configured`. A split checker verdict shows `✗ split (PASS and FAIL)` with the verdicts. A manual run's checker row without a verdict says `— (a person reviews)`.
7. PR 1: one `**Approval:**` line. An automatic run: `Automatic approval: Autopilot \`auto\` mode, started by LOGIN on DATE. No person was asked.` (`observe` for that mode; without a login "started on DATE"; when a person also approved in the terminal, that sentence replaces "No person was asked."). A manual run: the person's recorded words on one line, each in a code span with where and when ("in chat, 2026-11-06"), the last 3, then "(N earlier in Details)".
8. PR 1: `**Next:**` In an automatic run: "PR 2 (the code) started by itself: #N." when PR 2 exists, else "PR 2 (the code) starts by itself (Autopilot `MODE` mode)." In a manual run: "PR 2 (the code): #N." or "The code PR starts when you ask for it." Then the issue reference ("Part of #N.").
9. Code PR: `**Merge:** automatic when every check above is green (Autopilot \`auto\` mode). Closes #N.` in an automatic auto-mode run that is not a draft; else "waiting for a person to merge" (with "(draft PR)" for a draft). The issue reference is the runner's (`Closes #N` or `Refs #N`). Then, by `pr1Order`: `carried` adds "This PR also merges PR 1 (#N). Do not merge PR 1 alone."; `first` adds "Builds on PR 1 (#N): merge it first."; `ci` adds "Builds on PR 1 (#N)." with no order; `closed` adds "Builds on PR 1 (#N), which is closed without a merge."; null adds nothing.

`readableNextLines(facts)` returns the lines of step 8 or 9 alone, so the runner can replace PR 1's Next line when PR 2 opens.

Links appear once in the readable part: one report link, `#N` references for PRs and issues. No internal words (no run IDs, batches, "agent note", handoff or overlay words).

## Inert agent words

`inertText(value, max)` makes agent words one safe Markdown line: control and bidi characters go, whitespace collapses, the text is cut at a word end with ` …` (at most `max` code points). Outside code spans, a Markdown image or link keeps only its text (`![x](…)` → `x`, `[report](…)` → `report`), and a bare `http://`, `https://`, `ftp://` or `www.` address gets a zero-width space so that GitHub does not link it; `<` and `>` become `&lt;` and `&gt;`; `pdd-workflow:` and `pdd-product:` never appear (the colon is escaped), so an agent cannot add HTML, an image or a second report link, close the Details section or forge an ownership marker. Outside code spans an `@name` gets a zero-width space after `@` (no notification), and every closing keyword (close, closes, closed, fix, fixes, fixed, resolve, resolves, resolved, any case) gets one zero-width space after it, whatever follows: GitHub also reads `Fixes: #5`, `Closes:#5`, `CLOSES: #10`, `Resolves: org/repo#3`, `**fixes** #5` and `fixes&nbsp;#5`. A word that already has one gets no second one. The text of a code span stays exact, with no zero-width space (GitHub reads no mention and no reference in code), so `` `npm i @types/node` `` and `` `git commit -m "fixes #5"` `` can be copied. A backtick after a backslash opens no code span. So merging closes only the issue of pdd's own `Closes #N` line. Table cells also escape `|`; an empty cell is `—`. `codeSpan(value)` puts a path or the person's words in a code span longer than any backtick run inside.

## The whole description

`balancedDetails(text)` keeps agent text inside the Details section from closing it: outside code spans and fences, a `</details>` with no open `<details>` before it becomes `&lt;/details&gt;`, an open fence is closed at the end and each open `<details>` gets its `</details>`. The runner uses it for verify.md. A fence opens only where GitHub opens one (at most three spaces before it; a backtick fence has no backtick after its mark, so "```x```" is inline code), and any line that is the fence mark alone closes it, so pdd never takes text for code.

`closingInert(text)` makes agent Markdown that pdd shows whole in Details (verify.md, and the verdict and change lines of a check) close no issue: outside code spans, fenced code (the same fence rule) and indented code blocks, every closing keyword gets one zero-width space after it, as in `inertText`. An indented code block is a run of lines indented by 4 spaces or a tab that starts after a blank line (or at the start), outside a list, and goes on while lines stay indented or blank. An address (`http://`, `https://`, `ftp://`, `www.`), a link target `](…)` and an HTML tag keep their text, so their links still work; a keyword at the end of an address (before any trailing `:*_~.,!?`) gets one only when an issue reference follows it ("…/fixes #5", "…/closes: o/r#3"), so an address that only ends in a keyword word ("…/tree/fix") stays exact. Code spans, fences and indented code blocks stay byte for byte. verify.md "This Fixes #8 and Resolves: #9." closes neither issue. `sameReadableTop(a, b)` is true when two descriptions differ at most in the ` · Updated …` time of their first line (and trailing space), so a refresh writes only a real change.

`DETAILS_OPEN` is `<details><summary>Details for tools and audits</summary>`. pdd owns the description: it rewrites the part above Details at each `pdd workflow status` and all of it at each push. `TOP_NOTE` says so to a person who edits it, as one HTML comment (readers never see it): `<!-- pdd writes this description. It rewrites the part above Details at each pdd workflow status and all of it at each push. Write your notes in a PR comment. -->`. `readablePrBody(top, details)` returns the readable part, a blank line, `DETAILS_OPEN`, a blank line, `TOP_NOTE`, a blank line, the details text, a blank line and `</details>`. `detailsOf(body)` returns `{details, after}` when the first `<details` line of a description is exactly `DETAILS_OPEN` (the text up to the last `</details>` line without a leading `TOP_NOTE`, and any text after it), else null (a description that an older pdd wrote).

## Dependencies

- [Small-change evidence](workflow-small-change.prompt.md): required schema and completion checks for checklist rendering and readiness.

## Typed Runtime adapters

The native object helpers above retain their signatures and results. Runtime uses
`readablePrTopJson({factsJson, fileLimit?})` for the same renderer: parse `factsJson`
as a JSON object, pass it and the optional limit to `readablePrTop`, and return
its `{text, notes}` result. A malformed JSON value, null, array or scalar raises
an error with code `invalid-facts`. `fileLimit` defaults to 40 as above.
`readPrFieldsJson(texts)` applies the field-reader rules and returns the full
result as JSON text, including arbitrary file-path keys in `notes`. These adapters
preserve unbounded map keys without an open Runtime object schema. They do not
add a record, verdict, filesystem read or model call.

## Dependencies

- [Workflow runner](workflow-runner.prompt.md): required authoring/generation/verification/testing context. It gathers the facts, keeps the pdd body inside Details, fits the whole description in its 60,000-character budget and publishes it.
- [Workflow replay](workflow-replay.prompt.md): required context for the replay result fields (counts, mutation, formal status, result, scope, reason and control outcome); `formalStatusText` gives the formal row's words, detail, repair step, note and whether it is not needed.
- [Committed proof](workflow-prove.prompt.md): required context for the old-code proof outcomes.

<details>
<summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "f67f4e5331c85384bcbe0a824bc95b814966c0b6373dab675169785dec6cba47",
  "entries": [
    {
      "operation": "readablePrTitle",
      "input_schema": {
        "type": "object",
        "properties": {
          "layout": {
            "enum": [
              "spec",
              "code"
            ],
            "type": "string"
          },
          "workflow": {
            "type": "string"
          },
          "area": {
            "type": "string"
          },
          "statement": {
            "type": "string"
          },
          "number": {
            "type": "integer",
            "minimum": 1
          },
          "part": {
            "oneOf": [
              {
                "type": "integer"
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "layout",
          "workflow",
          "area",
          "statement",
          "number"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "string",
        "maxLength": 256
      },
      "errors": []
    },
    {
      "operation": "readablePrTopJson",
      "input_schema": {
        "type": "object",
        "properties": {
          "factsJson": {
            "type": "string"
          },
          "fileLimit": {
            "type": "integer",
            "minimum": 0
          }
        },
        "required": [
          "factsJson"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "text": {
            "type": "string"
          },
          "notes": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "text",
          "notes"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid-facts"
      ]
    },
    {
      "operation": "readPrFieldsJson",
      "input_schema": {
        "type": "array",
        "items": {
          "type": "string"
        }
      },
      "result_schema": {
        "type": "string"
      },
      "errors": []
    },
    {
      "operation": "userStory",
      "input_schema": {
        "type": "string"
      },
      "result_schema": {
        "oneOf": [
          {
            "type": "string"
          },
          {
            "type": "null"
          }
        ]
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [],
  "limits": {
    "max_steps": 1,
    "max_model_calls": 1
  },
  "conventions": []
}
```

</details>
