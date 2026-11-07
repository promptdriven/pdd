# Readable workflow PR descriptions

Own `src/workflow-pr-body.mjs`. It renders the part of a pdd workflow PR that a person reads first (#3042): a title, a status line, the user story, a short summary, a cases table, what changed, one table of checks or proof and one approval, next or merge line. The [runner](workflow-runner.prompt.md) gathers the facts from Git, the run folder, pdd's own records, CI and the checker; this module only renders them and reads nothing itself. Everything else that pdd writes (IDs, batches, request IDs, step notes, agent notes, approval records, verify.md, inventory, replay text) stays whole in one closed Details section below. Nothing is lost.

## Agent fields

`readPrFields(texts)` reads labeled lines from the `done` summaries of a PR's steps, in step order. A line starts (after optional spaces and one `- ` or `* `) with exactly one label and a colon: `Title`, `Area`, `Problem`, `Cause`, `Fix`, `Change`, `Result`, `This PR`, `Verdict`, `Case` or `File`. A later line replaces an earlier line with the same label. `Case: INPUT | BEFORE | AFTER | EXPECTED` gives a cases row; 3 cells are `INPUT | BEFORE | EXPECTED` and 2 cells `INPUT | EXPECTED`; other cell counts and an empty input are ignored. The Case rows of the latest text that has any replace all earlier rows, at most 12. `File: PATH — NOTE` (or `-`, `–` or `:` as the separator, the path optionally in backticks) gives one short note for a changed file. It returns `{title?, area?, problem?, cause?, fix?, change?, result?, thisPr?, verdict?, cases, notes}`.

## User story

`userStory(text)` returns the first "As a …, I want …, so that …" statement of a Story file as one line, or null. The statement may start after `> `, a list marker or bold marks, and may wrap over following lines of its paragraph (it ends at a blank line, a heading, a list item, a fence, a table row or HTML). It needs "As a" or "As an", then ", I want" and "so that".

## Area and title

`prArea({area, files, workflow})`: the agent's `Area` field when it has a usable name, else the first changed `*.prompt.md` (its name without `.prompt.md` and a language suffix such as `_python`), else the first changed Story under `user_stories/` (not `PLAN.md` or `README.md`), else the first changed source file (a common source extension such as `.js`, `.ts`, `.py` or `.go`) outside test, fixture, doc, Story and prompt folders, else the first other such file that is not Markdown, JSON, a lock file or text, else the workflow name. The result is lowercase letters, digits, `.`, `_` and `-`, at most 40 characters.

`readablePrTitle({layout, workflow, area, statement, number, part})`: `spec(AREA): STATEMENT (#N · part 1: spec)` for PR 1, `fix(AREA): STATEMENT (#N · part 2: fix)` for a bug code PR, `feat(AREA): STATEMENT (#N · part 2: feat)` for a feature code PR and `fix(AREA): STATEMENT (#N)` for a one-PR run (`part` null). STATEMENT is the agent's `Title` field (PR 1: what must be true; PR 2: what is true after the merge), else the issue title, on one line. GitHub refuses a title over 256 UTF-16 code units: cut only the statement, at a Unicode character boundary, and show ` …`; the type, area and suffix always stay.

## The readable part

`readablePrTop(facts, {fileLimit = 40})` returns `{text, notes}`. `notes` are lines for Details, for example "User story: … has no "As a …, I want …, so that …" line, so this PR has no User story section." Top to bottom:

1. One status line, computed only from the records below: `⛔ Blocked: REASON; REASON` when any record shows a problem, else `⏳ Waiting for X, Y and Z` when a record is not finished, else `✅ Ready to merge`. Reasons: prompt tests fail, lint fails, N draft prompts to approve, N approved cases fail on the new code, replay evidence is blocked or incomplete, the old code (feature: the planted mistake) fails no case, formal check failed at INPUT, an old-code proof problem (the changed tests fail on the new code, also pass on the old code, fail on the old code for another reason, a setup error, a stop, a time-out or too much output), review has N must-fix, CI fails, the checker says FAIL or is not sure. Waiting: the source to be published (while a push is pending), CI, the checker (not in a manual run) and, for a code PR stacked on an open PR 1 that it does not carry, PR 1 (#N).
2. `## User story`: each Story line (at most 3), else no section and a note.
3. `## Summary`: PR 1 bullets **Problem**, **This PR** (the agent's field, else pdd's own "no code change. It holds the prompt `x.prompt.md`, the Story and N test files."), **Verdict**; a code PR **Problem**, **Cause**, **Fix**, **Result**; a one-PR run (`single`, such as small-change) **Problem**, **Change** (else its Fix field), **Result**. Missing fields are left out; with no bullet there is no section.
4. Cases: PR 1 `## Expected behavior` with Input, Today (when any row has a before value) and Expected; a code PR `## Before / after` with Input, Before (when any row has one), After and Expected, where Expected shows ` ✓` when After equals it and ` ✗` when it differs. No section without rows. No acceptance criteria list.
5. `## What changed (+A −D, N files)`: the Git numbers; one bullet per file with its agent note, else its own `(+a −d)` (or `(binary)`), at most `fileLimit` files, then "…and N more files (see the Files tab)."
6. `## Checks` (PR 1, columns Check and Result) or `## Proof` (code PR, columns Check, New code and Old code; a feature run says Planted mistake instead of Old code). Rows come only from pdd's records, never from agent words:
   - PR 1: Prompt tests (`pdd test`) with its result and one report link, "(older source)" when the saved source is not current, else "no pdd result (`pdd:no-verdict`)"; Lint (`pdd lint`); Prompts approved only when draft prompts remain; Full test suite (CI); Independent checker.
   - Code PR: Approved cases on real code (vectors) from the validated replay evidence: `✓ P of T` or `✗ F of T fail`, and in the second column `✗ N fail (as expected)` from the semantic mutation control; a blocked or not replayed record shows its reason. Formal check (SCOPE) from the replay evidence: `Proved (bounded)`, `Proved (solver)`, `Failed at INPUT` (the counterexample), `Not run: REASON` or `Not applicable: REASON`, never "Proved" otherwise; without a formal record in a workflow with a formal step, `Not recorded: …`. Changed tests (old-code proof) from the judged `pdd workflow prove` record, with the native test counts when known. Full test suite (CI) on this commit. Fresh review from the first line of review.md (`no must-fix` or `✗ N must-fix`, else not recorded) when the area has a review step. Independent checker.
   - A row that is not finished shows `⏳ pending` (CI that is pending, unknown or not yet read; a checker without a verdict). A manual run's checker row without a verdict says `— (a person reviews)`.
7. PR 1: one `**Approval:**` line. An automatic run: `Automatic approval: Autopilot \`auto\` mode, started by LOGIN on DATE. No person was asked.` (`observe` for that mode; without a login "started on DATE"; when a person also approved in the terminal, that sentence replaces "No person was asked."). A manual run: the person's recorded words on one line, each in a code span with where and when ("in chat, 2026-11-06"), the last 3, then "(N earlier in Details)".
8. PR 1: `**Next:**` In an automatic run: "PR 2 (the code) started by itself: #N." when PR 2 exists, else "PR 2 (the code) starts by itself (Autopilot `MODE` mode)." In a manual run: "PR 2 (the code): #N." or "The code PR starts when you ask for it." Then the issue reference ("Part of #N.").
9. Code PR: `**Merge:** automatic when every check above is green (Autopilot \`auto\` mode). Closes #N.` in an automatic auto-mode run that is not a draft; else "waiting for a person to merge" (with "(draft PR)" for a draft). The issue reference is the runner's (`Closes #N` or `Refs #N`). When the code PR carries PR 1 (GitHub shows its base as the run's base while PR 1 is open), add "This PR also merges PR 1 (#N)."; when it is stacked on an open PR 1, add "Builds on PR 1 (#N): merge it first."

`readableNextLines(facts)` returns the lines of step 8 or 9 alone, so the runner can replace PR 1's Next line when PR 2 opens.

Links appear once in the readable part: one report link, `#N` references for PRs and issues. No internal words (no run IDs, batches, "agent note", handoff or overlay words).

## Inert agent words

`inertText(value, max)` makes agent words one safe Markdown line: control and bidi characters go, whitespace collapses, the text is cut at a word end with ` …` (at most `max` code points). Outside code spans, `<` and `>` become `&lt;` and `&gt;`; `pdd-workflow:` and `pdd-product:` never appear (the colon is escaped), so an agent cannot add HTML, close the Details section or forge an ownership marker. An `@name` gets a zero-width space after `@` (no notification). A closing keyword before an issue reference (`fixes #5`) gets a zero-width space after the keyword, so merging never closes another issue. Table cells also escape `|`; an empty cell is `—`. `codeSpan(value)` puts a path or the person's words in a code span longer than any backtick run inside.

## The whole description

`DETAILS_OPEN` is `<details><summary>Details for tools and audits</summary>`. `readablePrBody(top, details)` returns the readable part, a blank line, `DETAILS_OPEN`, a blank line, the details text, a blank line and `</details>`. `detailsOf(body)` returns `{details, after}` when the first `<details` line of a description is exactly `DETAILS_OPEN` (the text up to the last `</details>` line, and any text after it), else null (a description that an older pdd wrote).

## Dependencies

- [Workflow runner](workflow-runner.prompt.md): required authoring/generation/verification/testing context. It gathers the facts, keeps the pdd body inside Details, fits the whole description in its 60,000-character budget and publishes it.
- [Workflow replay](workflow-replay.prompt.md): required context for the replay result fields (counts, mutation, formal result, scope, reason and control outcome).
- [Committed proof](workflow-prove.prompt.md): required context for the old-code proof outcomes.

<details>
<summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"","entries":[{"operation":"readablePrTitle","input_schema":{"type":"object","properties":{"layout":{"enum":["spec","code"]},"workflow":{"type":"string"},"area":{"type":"string"},"statement":{"type":"string"},"number":{"type":"integer","minimum":1},"part":{"type":["integer","null"]}},"required":["layout","workflow","area","statement","number"]},"result_schema":{"type":"string","maxLength":256},"errors":[]},{"operation":"readablePrTop","input_schema":{"type":"object"},"result_schema":{"type":"object","properties":{"text":{"type":"string"},"notes":{"type":"array","items":{"type":"string"}}},"required":["text","notes"]},"errors":[]},{"operation":"readPrFields","input_schema":{"type":"array","items":{"type":"string"}},"result_schema":{"type":"object"},"errors":[]},{"operation":"userStory","input_schema":{"type":"string"},"result_schema":{"type":["string","null"]},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":1,"max_model_calls":0},"conventions":[]}
```

</details>
