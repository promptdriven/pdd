# Workflow Story card

Own `src/workflow-story-card.mjs`. It reads one run's real files and pdd's own saved check results. It never calls GitHub, Herdr, the PDD interpreter or a model, and it never writes a file. The [workflow runner](workflow-runner.prompt.md#normal-run-gates) decides when the card shows and what the gates do with the results of this module.

## The card

`storyCard({run, root, changed, prompts, results, changes, through})` returns the card as one text: plain lines, no colors and no Markdown headings. The same files and inputs always give the same text. `changed` is the list of repository-relative paths that the run changes against its base (the runner reads it from Git). `prompts` is one row `{path, added, removed}` for each changed `*.prompt.md`. `results` is an optional list of `Prompt tests` lines. `changes` is an optional list of change lines from `fingerprintChanges`. `through` is `code`, `prompt-pr` or absent.

The card has these lines, in this order:

1. `Story card: OWNER/REPO#N "TITLE"`, then `Issue: URL`.
2. `Asked: "…"`: what the reporter asked, from the issue text that the run saved at start (`run.issue.asked`). Remove HTML comments. Use the first quoted block (its `>` lines) when the text has one; else use the first paragraph that is not a heading. Join its lines with one space and cut it at about 300 characters at a word end, with `…`. When the run has no saved issue text, write `Asked: not saved in this run; read the issue.`
3. The verdict line: the first `Verdict: …` sentence in the run's step summaries, newest summary first. A run with none shows `Verdict: not recorded yet.`
4. For each Story file that the run changes (`*.md` under a `user_stories` folder, except `PLAN.md` and `README.md`), and each Story that a changed test file names in `story_path`, in path order: `Story: ABSOLUTE PATH`, then these parts, each indented by two spaces:
   - `Acceptance criteria:` and the complete numbered criterion blocks under `## Acceptance criteria`, including continuation lines. Keep their line order and apply the part line bound with an explicit omitted-line count.
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

Read each test file with the [exact scenario number](runtime-seam.prompt.md) (`parseScenarioJson`, `stringifyScenarioJson`) rules, and write every JSON value of the card and the fingerprint (Input, VALUE and the canonical JSON) with them. A whole number above 2^53 then shows and hashes with its exact digits, so the person approves the value that the file holds, and a change in its last digit is a changed expected value. For a test without such a number, the text and hashes are the same as with `JSON.stringify`.

A file that cannot be read, or a test file that is not valid JSON, shows `(cannot read PATH)` in its place. The card never stops for one bad file. A path outside the physical run root, including a symlink target outside it, is unreadable; never show its content.

## The Story fingerprint

`storyFingerprint({root, changed})` returns `{stories, tests}` for the Story files and test files that the run changes (the same selection as the card, including Stories named by the changed tests, and also `PLAN.md`):

- Each Story row is `{path, sha256, criteria}`: the SHA-256 of the exact bytes (null if unreadable), and the complete numbered criterion blocks under `## Acceptance criteria`, including continuation lines joined by newlines. This stored list is not truncated.
- Each test row is `{path, sha256, cases}`. The SHA-256 covers only what the person decides: the canonical JSON of `{criteria, cases}`. Each case is `{case, error, expected}`: the `step_id`, the `expected_error` or null, and the sorted list of `[criterion_id, target, op, value]` of its checks. The input and the check path are not part of it: RUNBOOK §11 lets the agent fix an input or a check path. `cases` keeps each case's expected text as the card shows it. A test file that cannot be read or parsed gets the SHA-256 of its bytes (or of an empty text) and no cases.

`fingerprintChanges(saved, current)` returns a list of plain change lines; an empty list means no change:
- `Story added: PATH`, `Story removed: PATH`, `Story changed: PATH`, and after a changed Story each criterion line that is new (`  + LINE`) or gone (`  − LINE`).
- `Test added: PATH`, `Test removed: PATH`, and for a changed test each case whose expected values changed: `  case CASE: expected was OLD; now NEW` (`none` for a missing case). A changed test with no changed case shows `Test changed: PATH (criteria)`.
- At most 20 lines, then `… N more changes`.

## Full check pass

`fullCheckPass({root, since, tests, prompts, stories, scoped}, ports)` decides from pdd's own saved check results whether the prompt check passed in full on the current files. `scoped` defaults to `false`. Canonicalize paths with `realpathSync` (falling back to `resolve`). Read the `pdd test` batches in `ports.env.PDD_STATE_DIR`, else `HOME/.pdd/runtime`, folder `batches/<batch>`, with the same batch-name rule as [workflow results](workflow-results.prompt.md). Exclude batches whose `batch.json` lacks `intent` `check` or valid `rows`, or whose `created_at` is invalid or before `since`. When `ports.workspace` is supplied (`readEvidenceEligibility`), ask `ports.workspace({root, producerRoot: batch.root, tests: BATCH TESTS, source_sha256: batch.source_sha256, runId: batch.association?.runId ?? null, stage: batch.association?.stage ?? null})`: admit an `eligible` batch only when its resolved `stage` is `current` (never `pr1` or `before`); when `ports.workspace` is not `eligible`, admit only an ordinary same-worktree batch (`real(batch.root) === real(root)`, no `batch.association`, and not a historical `before` association) so drifted same-worktree checks still report `changed`. Without `ports.workspace`, admit only `real(batch.root) === real(root)` with no `batch.association`. Reconcile the authoritative rows in `batch.json` with the batch's `summary.json` only when its `batch` equals the batch folder name, its canonical `repo` equals the canonical `batch.root`, and its `source_sha256` equals the batch source hash. A missing or mismatched identity is unavailable, not a pass.

Partition unique sorted `prompts` using `loadRuntimeWorkspace({root})`, `allowsRuntimePath`, `readPrompt`, `promptRefusal`, `parsePromptFrontmatter` and `interfaceBlocks`, with `found.visible` from test discovery and repository Git-visible files from `gitFiles(root)` (falling back to readable prompt files under `root`):
- When `workspace` is unconfigured or `allowsRuntimePath(workspace, path)` is true, inspect `readPrompt(root, visible, path, workspace)` and `promptRefusal(parsed, 'prompt')`: a prompt with no read error, no prompt refusal, `interface.kind === "native-only"`, and a nonblank trimmed `interface.reason` is a verified native-only prompt `{path, reason}` in `nativeOnly`.
- When `workspace.configured` is true and `!allowsRuntimePath(workspace, path)` (a prompt outside `pdd-workspace.json` `allowed_paths`), read `path` directly when it is a Git-visible `*.prompt.md` file inside `root` and inspect `parsePromptFrontmatter(text)` and `interfaceBlocks(text)`: when `frontmatter.hasFrontmatter` is true, add `{path, reason}` to `nativeOnly` only if `interfaceBlocks(text)` is empty, `!frontmatter.error`, `frontmatter.kind === "native-only"`, and `frontmatter.reason` is nonblank when trimmed; otherwise keep `path` in `checkablePrompts` and record the corresponding refusal detail (`pdd-two-interfaces`, `native-reason-missing`, or `interface-kind-invalid`).
- Every other prompt — including plain-Markdown prompts, malformed `native-only` frontmatter, or unreadable/invalid workspace state — stays a checkable prompt so invalid frontmatter never bypasses checks.

When `scoped` is `false`, the tests to judge are the given `tests` (the run's changed test files), all scenarios independently discovered by runtime preflight `findTests({root, excludeFixtureProjects: true})` in the current project (the same scope as default `pdd test`, excluding nested fixture projects), and every still-present test of these batches; every current project Story reported as untested, and every required `stories` path without an associated scenario, adds a `missing` problem naming that Story. When `scoped` is `true`, scope selection to the run's affected Stories and consumer reach:
1. All given `tests`;
2. Every discovered scenario whose Story (`storyPath`, `storyPaths` or scenario `story_path`) is in `stories`;
3. Every discovered consumer scenario whose dependency closure in `source.identity({root, tests: [test.path], appMap: null, allowMissingInterfaces: true})` reaches at least one checkable prompt. If capture throws on a scenario, fail open for unrelated broken scenarios and include `test.path` only when its parsed scenario JSON directly names a checkable prompt in `entry_path`, `entry_paths`, `steps[*].entry_path` or `context`.
When `scoped` is `true`, require scenario coverage for `[...new Set([...found.untested.filter(path => stories.includes(path)), ...stories])].sort()` so pre-existing unrelated repository Stories do not block the run, while any Story in `stories` (an approved Story with acceptance criteria) always requires a scenario test even when every prompt in the run is `nativeOnly` (a `0`-Story pure `native-only` run already has empty `stories`). Discovery failure is `unavailable`. Missing tests within the active scope still block the automatic full-pass route.

Keep the newest result per test so a selective recheck can reuse still-current results from an earlier check. For each test, the newest batch that has it decides (newest `created_at`, then batch name). The test passes only when:
- exactly one authoritative batch row and exactly one summary row name this test; both have `state` `passed`, neither has refusals, unchecked criteria, a broken-test reason or an unsent flag, and any batch criterion counts agree with the summary; the summary row's `criteria` has `total` above 0, equal to the current test file's number of criteria, and `passed` equal to `total`; and
- its source did not change after the check: the batch's saved `contract_snapshots` row for its Story equals the same row of `source.identity({root, tests: ROW TESTS, appMap: null, allowMissingInterfaces: true})` (`captureSource`) today on `root`, including its test selection, files and reference provenance. Equal file hashes alone cannot replace this row comparison. A nonempty snapshot list with no row for the selected test is unavailable and never falls back. A batch with no snapshots instead needs its `source_sha256` to equal today's capture of all its tests on `root` with `allowMissingInterfaces: true`.

Every checkable prompt path must be in the files of a passing test's snapshot row (or of its batch `files` without snapshots), with one narrow scoped exception: when `scoped` is `true`, at least one scenario test was judged (`judged.length > 0`), no Story or scenario problem occurred (`problems.length === 0`), and every other checkable prompt is covered, omit `prompt-not-checked` for a plain unreferenced module prompt — a readable Git-visible `*.prompt.md` file with no YAML frontmatter, zero embedded `Runtime interface` blocks, no prompt refusal, and no reference in any `pdd-boundary` fence block of `stories` (or of a selected scenario's `story_path`) or in any selected scenario's direct prompt fields or captured dependency closure. Verified `nativeOnly` prompts do not require scenario coverage. Prompts with an embedded `Runtime interface` block, frontmatter, or a Story/scenario reference, as well as `0`-test runs (`judged.length === 0`) and unscoped calls (`scoped === false`), always require `covered`. If a checkable prompt carries frontmatter with a prompt refusal, use that refusal message as its `prompt-not-checked` detail.

Return `{pass, tests, problems, nativeOnly}`. `tests` is one row `{path, batch, state}` for each judged test, and `nativeOnly` is the ordered `{path, reason}` list of verified native-only prompts. Each problem is `{kind, path, detail}` with one of these kinds:
- `failed`: the state is `failed`, or a criterion did not pass.
- `no-verdict`: the state is `refused`, `not run`, `partial`, `waiting` or `sent` (also their legacy `not_run`, `unknown`, `queued` or `running` spellings), or the summary has no row for the test. This includes an AI-service failure; it is not a failed check.
- `changed`: a file of the check changed after the check.
- `missing`: no saved check has this test, or a required Story in scope has no test.
- `prompt-not-checked`: no passing check reads this checkable prompt.
- `unavailable`: a batch or the current source cannot be read.

`pass` is true only with at least one judged test and no problem; a `native-only` declaration records why a Runtime check cannot run and never makes `pass` true without a judged test. The result never counts an agent's typed `Prompt tests` line as evidence.

## Dependencies

- [Runtime seam](runtime-seam.prompt.md#public-contract): `allowsRuntimePath`, `source.identity` (`captureSource`), `findTests`, `gitFiles`, `interfaceBlocks`, `loadRuntimeWorkspace`, `parsePromptFrontmatter`, `promptRefusal`, `readPrompt`, and exact scenario numbers (`format.parseScenario` / `parseScenarioJson`, `format.stringifyScenario` / `stringifyScenarioJson`) for test values.
- [Workflow results](workflow-results.prompt.md): the batch folder, batch name rule, and optional supplied `ports.workspace` (`readEvidenceEligibility`) callback contract for pdd's own results.
- RUNBOOK §2 (Story, test and prompt files), §4 (expected values), §11 (what an agent may fix) and §21 (`kind: native-only` declarations).
