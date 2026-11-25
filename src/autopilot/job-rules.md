# Autopilot core job rules

Read this file before starting a headless Autopilot job (`pdd autopilot start`). Load `$PDD_SKILLS/pdd/SKILL.md` and its references (`prompting.md`, `stories.md`, `verification.md`, and `formal.md` whenever touching rules/state transitions, parsers/validators, auth/trust, math/metrics/money, locking/scheduling, `## Rules to check` / `## Domain decisions`, or formal-tested modules; skip as `not-applicable` on docs/UI/glue/simple CRUD) on demand. Read very large files in parts so tool outputs stay crisp.

These rules govern the Autopilot core engine. Each job opens one PR. Autopilot's harness runs `pdd prove`, the full test suite, and the mechanical evidence contract independently and stamps machine verification receipts, `Path:`, `Runtime:`, and `Evidence:` deterministically from real tool checks and git state — do not hand-type or police machine metadata prose in the PR body.
Do not self-spawn a Fresh Verifier subagent during build or repair: Autopilot runs its own independent Blind Read-Only Reviewer next.

## Scope and mode (extending `$PDD_SKILLS/pdd/SKILL.md`)

- Follow mode selection in `$PDD_SKILLS/pdd/SKILL.md`: use `small-change` only when every planned file is an unowned **non-product file** (docs, guides, CI, lockfiles, packages, non-behavior config/metadata, or test-only maintenance — never `*.prompt.md`, `user_stories/*.md`, or product code), including docs-only issues framed as bugs.
- Write no new Story and no new prompt for a non-product file. A repair on a non-product-only PR stays non-product without adding a Story or prompt.
- For product or prompt-owned code, use `bug` or `feature` mode and follow the 100% Truth Rule in `prompting.md` (update existing owning prompts before code; for unowned legacy code, either adopt/extract a clean PDD module with a `// Prompt:` header or apply a surgical brownfield fix verified with Red→Green TDD).
- Protected policy, workflow, and package files (`pdd.json`, `package.json`, `.github/workflows/**`, `CODEOWNERS`, gate scripts) always hold for manual human review and merge on GitHub — Autopilot never auto-merges protected-path edits.

## Changed scope

- **Changed** means changed against the PR base (`git diff --name-only origin/BASE...HEAD`), never just since the previous commit. Files brought in by merging `BASE` are not changed.
- A changed Story is any Story whose `.md` or scenario test file changed, or whose test reaches a changed prompt.

## Runtime checks and result reporting

- Commit every change, then batch changed Stories in `"$PDD_CLI" test STORY STORY ...`. Report focused test counts in your JSON result's `"tests"` field and any unfixable runtime cause in `"runtime"`; Autopilot's harness audits and stamps receipts from its own records.
- **A failed check inside `no verdict` is still a FAIL:** if a `no verdict` run (exit 3, 4, or 5) reports fewer passed checks than total, read the report; any step showing `expected X, got Y` is a failure to fix, never `not run`.
- **When `not run` is allowed:** only for causes this PR cannot fix (`kind: native-only` prompt, `no verdict` with zero failed steps, interpreter maintenance, or a refusal with no pdd fix).
  - `real-binding-unavailable`, expired external logins, stopped daemons, or missing real E2E tests are never a silent skip or pass (in `auto` or `observe`). Autopilot parks outages without burning repair rounds and resumes on the same commit once healthy.
  - A refusal with a pdd fix (e.g., `impossible-result-value-pointer`) must be fixed and re-checked.
- **Maintenance:** if `pdd` prints `The interpreter is in maintenance until HH:MM UTC (…)` before sending, stop and report `maintenance until HH:MM UTC` in `runtime.cause`; Autopilot re-runs after maintenance. Never cut short an already-sent check.

## Real end-to-end tests, Deliberate-Break Probe, and large numbers

- Follow `verification.md` for real unmocked E2E coverage (subprocess CLI, real local HTTP/DB, real browser, real host bindings; `"$PDD_CLI" prove --base origin/BASE --test ... --expect ...` on bug fixes; never `test.skip` or `real-binding-unavailable` local-skip bypasses). Whenever a PR touches `kind: native-only` boundaries, include executable non-mocked **adversarial** real-host probes for every applicable surface (HTTP/Auth/Browser/MCP, Binary/File Parsers, Storage/DR, CLI/Day-0) — happy-path smoke and `simulated_vectors` never substitute for `adversarial_real_host` proof. Docs-only PRs need no E2E run.
- **Builder Deliberate-Break Probe (before final commit on non-trivial code changes):** temporarily flip 1–3 changed logic conditions or returns in a scratch edit, run your focused tests to confirm at least 1 assertion fails (not a syntax crash), then revert and re-verify green.
- **Large whole numbers in scenario JSON:** represent IEEE-754 Numbers outside `±(2^53−1)` with JS `String(n)` / `n.toExponential()`, never Python `json.dumps` of huge integers (refused by `scenario-integer-out-of-range`). Values no Number holds (`2^53 + 1`, BigInt) stay in native vector tests.
- **Formal checks & claims:** When touching rules/state transitions, parsers/validators, auth/trust, math/metrics/money, locking/scheduling, explicit `## Rules to check` / `## Domain decisions`, or any module with an existing formal test, add/update a code-bound formal/property test (using an installed property library OR a zero-install deterministic seeded PRNG / finite exhaustive grid directly against production code) and report `"formal":{"state":"bounded|proved_solver_code|proved_spec_model|not-applicable","reason":"..."}` in your JSON result. Report `proved_solver_code` ONLY with code-bound solver evidence + a failing production-code mutation control (never for disconnected spec models — report `proved_spec_model` or `not-applicable` for docs/UI/glue/simple CRUD).

## After merging from base

- Verify the fix is still needed by running the PR's changed tests against `git merge-base origin/BASE HEAD` in a throwaway worktree (`"$PDD_CLI" prove --base origin/BASE ...`). Drop redundant changes that base already holds and note it in the PR summary.

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
- Inspect every changed Story in full, including fenced code blocks: flag pasted implementation code or internal plumbing as must-fix before approval (move implementation details to the owning `.prompt.md` and large sample fixtures to `tests/` or `fixtures/`; exact values and short examples are fine when they define what the user actually sees).
- Verify every touched user-facing surface is backed by real unmocked execution (`pdd prove`, `verify.paths` Feature Map, real CLI/HTTP/DB/browser/host probes — not mocked-only stubs) and verify assertions actually bind the changed logic (could an empty stub or weakened test still pass?). For touched `kind: native-only` boundaries, verify `adversarial_real_host` probes (not `simulated_vectors` or happy-path smoke alone) cover every applicable boundary surface.
- Flag adding a prompt or Story for a non-product file, missing Runtime/native coverage on changed Stories, or bypassing a fixable refusal.
- When the diff changes rules/state transitions, parsers/validators, auth/trust, math/metrics/money, locking/scheduling, explicit `## Rules to check` / `## Domain decisions`, or a module with an existing formal test, flag missing code-bound formal/property coverage (unless genuinely `not-applicable`), and flag any disconnected spec model claimed as code-proved (`proved_solver_code` or `bounded`).
- Audit `Choices Autopilot made:` for unsettled choices and approved-rule updates; contradicting a recorded human answer or altering merge blockers is a P1 must-fix (undo or return `"kind":"blocker"`).
