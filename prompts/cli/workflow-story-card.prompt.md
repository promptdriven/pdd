# Workflow Story card

Own `src/workflow-story-card.mjs`. It reads one run's real files and pdd's own saved check results. It never calls GitHub, Herdr, the PDD interpreter or a model, and it never writes a file. The [workflow runner](workflow-runner.prompt.md#normal-run-gates) decides when the card shows and what the gates do with the results of this module.

## The card

`storyCard({run, root, changed, prompts, results, changes, through})` returns the card as one text: plain lines, no colors and no Markdown headings. The same files and inputs always give the same text. `changed` is the list of repository-relative paths that the run changes against its base (the runner reads it from Git). `prompts` is one row `{path, added, removed}` for each changed `*.prompt.md`. `results` is an optional list of `Prompt tests` lines. `changes` is an optional list of change lines from `fingerprintChanges`. `through` is `code`, `prompt-pr` or absent.

The card has these lines, in this order:

1. `Story card: OWNER/REPO#N "TITLE"`, then `Issue: URL`.
2. `Asked: "…"`: what the reporter asked, from the issue text that the run saved at start (`run.issue.asked`). Remove HTML comments. Use the first quoted block (its `>` lines) when the text has one; else use the first paragraph that is not a heading. Join its lines with one space and cut it at about 300 characters at a word end, with `…`. When the run has no saved issue text, write `Asked: not saved in this run; read the issue.`
3. The verdict line: the first `Verdict: …` sentence in the run's step summaries, newest summary first. A run with none shows `Verdict: not recorded yet.`
4. For each Story file that the run changes (`*.md` under a `user_stories` folder, except `PLAN.md` and `README.md`), and each Story that a changed test file names in `story_path`, in path order: `Story: ABSOLUTE PATH`, then these parts, each indented by two spaces:
   - `Acceptance criteria:` and the numbered lines under `## Acceptance criteria`.
   - `Must not change:` and the lines under `## What must not change` (also `## Must not change`; any letter case). When there is no such section: `Must not change: not stated.`
   - `Rules to check:` and the lines under `## Rules to check`. When there is no such section: `Rules to check: none.`
   - For each changed test file whose `story_path` names this Story: `Test cases (ABSOLUTE PATH):` and a table `| Case | Input | Expected |`, one row for each step. Case is the `step_id`. Input is the compact JSON of `input`. Expected is `error CODE` when the step has `expected_error`, then each check as `CRITERION PATH OP VALUE` (VALUE as compact JSON), joined with `; `. Cut the Case cell at about 60 characters, the Input cell at about 70 and the Expected cell at about 140, each with `…`, and write a `|` in a cell as `\|`.
   A part shows at most 12 lines and a table at most 8 rows. A longer part ends with `… N more lines in PATH`; a longer table ends with `… N more cases in PATH`.
5. A changed test file that names no changed Story shows its table under `Tests:`.
6. `Prompts that change:` and one line for each row of `prompts`: `ABSOLUTE PATH (+ADDED −REMOVED lines)`. With no row: `Prompts that change: none.`
7. `Plan: ABSOLUTE PATH` when the run changes a `user_stories/PLAN.md`.
8. When `changes` is not empty: `Changed since your approval:` and one line for each change.
9. When `results` is not empty: `Prompt tests:` and its lines.
10. The next step. A run with an `ask-code` area and `through` `code`: `Next step: when the check passes in full, pdd opens PR 1, then makes the code PR.` With another value: `Next step: when the check passes in full, pdd opens PR 1 and stops. Say so if you want the code PR too.` A run with no `ask-code` area: `Next step: pdd opens the PR when the check passes in full.`
11. `Try: you can ask to try it in the Simulator before you approve.`
12. `Approve, or tell me what to change.`

The card has at most 160 lines. Cap each list of Stories, plans, tests, prompts, results and changes at 20 entries with an omitted count. Truncate any remaining overflow with an omitted-line count before the final three lines. The card keeps these final lines even for large batches. When the Stories need more, show the first Stories in full while they fit. Each later Story shows only `Story: ABSOLUTE PATH (not shown in full: N criteria, M cases)`. The last Story line is followed by `… K more Stories not shown in full. Read their files.` Lines 10 to 12 always show.

A file that cannot be read, or a test file that is not valid JSON, shows `(cannot read PATH)` in its place. The card never stops for one bad file. A path outside the physical run root, including a symlink target outside it, is unreadable; never show its content.

## The Story fingerprint

`storyFingerprint({root, changed})` returns `{stories, tests}` for the Story files and test files that the run changes (the same selection as the card, including Stories named by the changed tests, and also `PLAN.md`):

- Each Story row is `{path, sha256, criteria}`: the SHA-256 of the exact bytes (null if unreadable), and the numbered lines under `## Acceptance criteria`.
- Each test row is `{path, sha256, cases}`. The SHA-256 covers only what the person decides: the canonical JSON of `{criteria, cases}`. Each case is `{case, error, expected}`: the `step_id`, the `expected_error` or null, and the sorted list of `[criterion_id, target, op, value]` of its checks. The input and the check path are not part of it: RUNBOOK §11 lets the agent fix an input or a check path. `cases` keeps each case's expected text as the card shows it. A test file that cannot be read or parsed gets the SHA-256 of its bytes (or of an empty text) and no cases.

`fingerprintChanges(saved, current)` returns a list of plain change lines; an empty list means no change:
- `Story added: PATH`, `Story removed: PATH`, `Story changed: PATH`, and after a changed Story each criterion line that is new (`  + LINE`) or gone (`  − LINE`).
- `Test added: PATH`, `Test removed: PATH`, and for a changed test each case whose expected values changed: `  case CASE: expected was OLD; now NEW` (`none` for a missing case). A changed test with no changed case shows `Test changed: PATH (criteria)`.
- At most 20 lines, then `… N more changes`.

## Full check pass

`fullCheckPass({root, since, tests, prompts}, ports)` decides from pdd's own saved check results whether the prompt check passed in full on the current files. It reads the `pdd test` batches in `ports.env.PDD_STATE_DIR`, else `HOME/.pdd/runtime`, folder `batches/<batch>`, with the same batch-name rule as [workflow results](workflow-results.prompt.md). It uses a batch only when its `batch.json` has `intent` `check`, the same real `root`, and `created_at` at or after `since`. It reads the row states and criteria counts from the batch's `summary.json`.

The tests to judge are the given `tests` (the run's changed test files) and every test of these batches. For each test, the newest batch that has it decides (newest `created_at`, then batch name). The test passes only when:
- its summary row has `state` `passed`, and its `criteria` has `total` above 0, equal to the current test file's number of criteria, and `passed` equal to `total`; and
- its source did not change after the check: the batch's saved `contract_snapshots` row for its Story equals the same row of `captureSource(root, {tests: ROW TESTS, appMap: null})` today, including its test selection, files and reference provenance. Equal file hashes alone cannot replace this row comparison. A nonempty snapshot list with no row for the selected test is unavailable and never falls back. A batch with no snapshots instead needs its `source_sha256` to equal today's capture of all its tests.

Every given prompt path (all of the run's selected changed prompts) must be in the files of a passing test's snapshot row (or of its batch `files` without snapshots).

Return `{pass, tests, problems}`. `tests` is one row `{path, batch, state}` for each judged test. Each problem is `{kind, path, detail}` with one of these kinds:
- `failed`: the state is `failed`, or a criterion did not pass.
- `no-verdict`: the state is `refused`, `not_run`, `unknown`, `queued` or `running`, or the summary has no row for the test. This includes an AI-service failure; it is not a failed check.
- `changed`: a file of the check changed after the check.
- `missing`: no saved check has this test.
- `prompt-not-checked`: no passing check reads this prompt.
- `unavailable`: a batch or the current source cannot be read.

`pass` is true only with at least one judged test and no problem. The result never counts an agent's typed `Prompt tests` line as evidence.

## Dependencies

- [Runtime preflight](runtime-preflight.prompt.md): `captureSource` and `interfaceBlocks`.
- [Workflow results](workflow-results.prompt.md): the batch folder and name rule for pdd's own results.
- RUNBOOK §2 (Story, test and prompt files), §4 (expected values) and §11 (what an agent may fix).
