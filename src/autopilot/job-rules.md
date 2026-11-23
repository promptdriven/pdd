# Autopilot core job rules

Read this file before starting a headless Autopilot job (`pdd autopilot start`). Load `$PDD_SKILLS/pdd/SKILL.md` and its references (`prompting.md`, `stories.md`, `verification.md`, and `formal.md` only for invariant-heavy work) on demand. Read very large files in parts so tool outputs stay crisp.

These rules govern the Autopilot core engine. Each job opens one PR. Autopilot's harness runs `pdd prove`, the full test suite, and the mechanical evidence contract independently and stamps its own harness receipt — PR body `Runtime:` and `Evidence:` lines are audited against harness records and never self-attest proof.
Do not self-spawn a Fresh Verifier subagent during build or repair: Autopilot runs its own independent Blind Fresh Reviewer next.

## Scope and mode (extending `$PDD_SKILLS/pdd/SKILL.md`)

- Follow mode selection in `$PDD_SKILLS/pdd/SKILL.md`: use `small-change` only when every planned file is an unowned **non-product file** (docs, guides, CI, lockfiles, packages, non-behavior config/metadata, or test-only maintenance — never `*.prompt.md`, `user_stories/*.md`, or product code), including docs-only issues framed as bugs.
- Write no new Story and no new prompt for a non-product file. A repair on a non-product-only PR stays non-product without adding a Story or prompt.
- For product or prompt-owned code, use `bug` or `feature` mode and follow the 100% Truth Rule in `prompting.md` (update existing owning prompts before code; for unowned legacy code, either adopt/extract a clean PDD module with a `// Prompt:` header or apply a surgical brownfield fix verified with Red→Green TDD).
- If a `small-change` run already touched owned or product code, rerun under `bug` or `feature` mode with its Story test, replay, and `Runtime:` evidence.

## Changed scope

- **Changed** means changed against the PR base (`git diff --name-only origin/BASE...HEAD`), never just since the previous commit. Files brought in by merging `BASE` are not changed.
- A changed Story is any Story whose `.md` or scenario test file changed, or whose test reaches a changed prompt.

## Runtime lines (audited against harness records)

- Commit every change, then batch changed Stories in `pdd test STORY STORY ...`.
- Write one `Runtime:` line per changed Story, verdict first, Story path first in parentheses:
  ```text
  Runtime: PASS (user_stories/format-bytes.md, 19/19 checks)
  Runtime: FAIL (user_stories/format-bytes.md, 2 of 19 checks failed: steps format-10, zibi)
  Runtime: not run (user_stories/package-repository.md: native-only prompt, no Runtime test)
  ```
- A single `Runtime: PASS` without a Story path is valid only when the PR changes at most one Story. Duplicate lines for one Story or claiming PASS for an unchanged Story fail audit. A FAIL line blocks merge.
- **A failed check inside `no verdict` is still a FAIL:** if a `no verdict` run (exit 3, 4, or 5) reports fewer passed checks than total, read the report; any step showing `expected X, got Y` is a FAIL to fix, never `not run`.
- **When `not run` is allowed:** only for causes this PR cannot fix (`kind: native-only` prompt, `no verdict` with zero failed steps, interpreter maintenance, or a refusal with no pdd fix). Always include the exact cause: `Runtime: not run (STORY: CAUSE)`.
  - `real-binding-unavailable`, expired external logins, stopped daemons, or missing real E2E tests are never a silent skip or pass (in `auto` or `observe`). Autopilot parks outages without burning repair rounds and resumes on the same commit once healthy.
  - A refusal with a pdd fix (e.g., `impossible-result-value-pointer`) must be fixed and re-checked.
- **Maintenance:** if `pdd` prints `The interpreter is in maintenance until HH:MM UTC (…)` before sending, stop and record `Runtime: not run (STORY: maintenance until HH:MM UTC)`; Autopilot re-runs after maintenance. Never cut short an already-sent check.

## Real end-to-end tests, large numbers, and Evidence line

- Follow `verification.md` for real unmocked E2E coverage (subprocess CLI, real local HTTP/DB, real browser, real host bindings; `pdd prove --base origin/BASE --test ... --expect ...` on bug fixes; never `test.skip` or `real-binding-unavailable` local-skip bypasses). Docs-only PRs need no E2E run.
- **Large whole numbers in scenario JSON:** represent IEEE-754 Numbers outside `±(2^53−1)` with JS `String(n)` / `n.toExponential()`, never Python `json.dumps` of huge integers (refused by `scenario-integer-out-of-range`). Values no Number holds (`2^53 + 1`, BigInt) stay in native vector tests.
- **`Evidence:` line counts (exact observed native runner counts only):**
  - `vectors=` counts changed/linked replay test files (`*.vectors.test.*`, `test_vectors*.py`, `*_vectors_test.go`, `tests/*vectors*.rs`).
  - `formal=` uses `proved_solver_code` (or `bounded`) ONLY when the formal suite imports/executes production code and passes a production-code mutation control (never for disconnected Z3 spec models — report `proved_spec_model` or `not-applicable`).
  - Report exact native runner counts (`passed/total`), e.g. `vectors=pass (36/36)`, never step/check counts.

## After merging from base

- Verify the fix is still needed by running the PR's changed tests against `git merge-base origin/BASE HEAD` in a throwaway worktree (`pdd prove --base origin/BASE ...`). Drop redundant changes that base already holds and note it in the PR body.

## Choices and human blockers (takes precedence over generic headless defaults)

- When a safe, backward-compatible fix exists, take it and record it under `Choices Autopilot made:` (`- CHOICE (REASON)`, adding `(changes public behavior: WHAT)` when user-visible).
- `bug` and `small-change` runs never ask choice questions; when a bug fix must update an approved prompt rule, update it and record `(changes approved rule: OLD -> NEW)`.
- Under `decisions: decide` (default), decide choices and list big ones first marked `(big)`. Under `decisions: ask`, ask (`"kind":"choice"`, max 1 per issue) only when every reasonable fix breaks existing users or a `feature` alters product direction, core contracts, security/privacy policy, or cost.
- **Always escalate real blockers as `"kind":"blocker"`:** contradicting a person's recorded earlier answer, changing merge blockers/gates/CI policy, or missing access/secrets/contradictory issue.
- Return a needs-person decision as JSON with 2–3 lettered options:
  ```json
  {"outcome":"needs-person","kind":"blocker|choice","question":"<one plain question>","options":["<answer A>","<answer B>"],"recommended":"<the letter you recommend>"}
  ```

## For the Blind Read-Only Reviewer

- Inspect strictly the diff, owning prompts/Stories, and harness evidence (never trust PR prose; never edit files). Run `git diff --stat` and inspect the changed files, then end your summary with `Read: FILE, FILE, ...`.
- Verify every touched user-facing surface is backed by real unmocked execution (`pdd prove`, `verify.paths` Feature Map, real CLI/HTTP/DB/browser/host probes — not mocked-only stubs) and confirm non-trivial changes include a failing-on-mutation Deliberate-Break Probe result from the builder/verifier.
- Audit `Runtime:` lines against changed Stories (`no verdict` containing a failed step is a FAIL; `not run` requires an allowed cause; adding a prompt/Story for a non-product file is a must-fix).
- Audit `Choices Autopilot made:` for unsettled choices and approved-rule updates; contradicting a recorded human answer or altering merge blockers is a P1 must-fix (undo or return `"kind":"blocker"`).
