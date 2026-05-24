# PR Bug-Fix Loop Process

Reusable runbook for shipping bug fixes through an adversarial review loop in `promptdriven/pdd`. Adapted from the Generative-Video-Studio version; tuned for this repo's Python toolchain (pytest + pylint), GitHub Actions CI (`unit-tests` + `auto-heal`), and `/heal` trigger.

## When to use

Any non-trivial bug that needs to ship as a PR. Especially when:
- The fix touches correctness-sensitive code (LLM invocation, sync determination, prompt processing, fingerprinting, async state).
- You can't easily eyeball the fix yourself.
- You want an independent second opinion before merging.

## Three actors

1. **Implementer** — Claude subagent working in an isolated worktree.
2. **Reviewer** — Codex CLI (`codex review` / `codex exec review`) for independent adversarial perspective.
3. **Orchestrator** — you (or top-level Claude) triaging Codex findings and dispatching next rounds.

## Worktree invariant

All implementation, test, review, rebase, and PR-branch commands happen inside the PR worktree. The main clone is only for orchestration and the final `gh pr merge`.

## The loop

### 1. Implementer round

Dispatch a Claude subagent with `subagent_type: "general-purpose"` and `isolation: "worktree"`. The agent prompt should include:

- The bug context (live evidence, reproduction signal).
- The fix design at a high level (or the choice space if multiple approaches).
- TDD discipline:
  - Write a failing test FIRST that reproduces the bug.
  - Commit it as a SEPARATE commit with a `test(...)` conventional-commit prefix.
  - Push the failing-test commit BEFORE pushing the fix.
  - Implement the fix.
  - Run targeted pytest + `pylint` on the touched modules until clean. Prefer direct `pylint pdd/<module>.py tests/test_<module>.py` over `make lint` — the `make` target re-runs `pip install -e ".[dev]"` via `ensure-dev-deps`, which fails offline or in network-restricted sandboxes.
  - Commit the fix as a SEPARATE commit with a `fix(...)` prefix.
- Open the PR with `gh pr create` (must be non-draft, or transitioned to ready-for-review, for `unit-tests` to run). Unit tests run automatically on PR open/sync — no special comment marker required for the merge gate. (If you want the prompt-healing CI pass too, comment `/heal` on the PR after opening.)
- Post the red-output from the failing-test commit as a PR comment for TDD evidence.
- Output their result early (don't iterate silently — that's how subagents stall).

### 2. Codex review

Use `codex exec review` — same review engine as plain `codex review`, but inside the `exec` runner that has shell access. This lets Codex post its own PR comment via `gh` AND lets you customize the review prompt to demand exhaustive findings instead of one-at-a-time.

From inside the agent's worktree:

```bash
cd /path/to/.claude/worktrees/agent-<id>
git fetch origin <pr-branch> main

# PRECONDITION: `git reset --hard` below will destroy local work. Confirm
# the worktree has no uncommitted changes AND no unpushed commits first.
test -z "$(git status --short)" || { echo "uncommitted changes — abort"; exit 1; }
test -z "$(git log origin/<pr-branch>..HEAD --oneline)" || { echo "unpushed commits — abort"; exit 1; }

git reset --hard origin/<pr-branch>

codex exec review --base origin/main --title "PR #<N> @ <sha>" --skip-git-repo-check "$(cat <<'EOF'
Adversarial code review of the diff vs origin/main. Find EVERY correctness issue, security issue, or significant design flaw in the diff. Be EXHAUSTIVE — list ALL findings in this single pass, not just the most important one. Do not stop at the first issue you find.

Categorize each finding as:
- P1: blocking correctness / silent corruption / security
- P2: would-be-nice / edge case / robustness

When done, POST the findings as a single PR comment using:

  gh pr comment <PR_NUMBER> --body "<<<MARKDOWN>>>"

Use this exact comment structure:

## Codex adversarial review — PR #<N> @ <sha>

**Verdict:** MERGE | DON'T MERGE
**Findings:** <count> total (<n> P1, <n> P2)

### P1 (blocking)
- [P1] <one-line title> — `<file>:<line-range>`
  <one-paragraph description of the bug>
  **Suggested fix:** <one-sentence concrete suggestion>

### P2 (non-blocking)
- [P2] ... (same shape)

### Notes
- <optional context, accepted trade-offs, etc.>

If you find NO issues, post a comment that just says "MERGE — no findings."

You MUST end your session by successfully running the `gh pr comment` command. Don't just print the review to stdout — post it. If `gh pr comment` fails, retry once. If it still fails, print the comment body so the orchestrator can post manually.
EOF
)"
```

Replace `<PR_NUMBER>` literally in the prompt before invoking, since Codex won't know the PR number from context.

**Tradeoffs of exhaustive single-pass:**

- Pros: typically converges in 1-2 rounds instead of 5-13. Orchestrator sees ALL findings at once and can dispatch one implementer round to fix everything.
- Cons: longer wall clock per pass (~5-15 min vs 2-5 min for single-finding). Higher chance of false positives mixed with real ones — orchestrator triage is more important.

**Heuristic: Codex often returns one issue at a time unless pushed.** This is anecdotal — the CLI doesn't document a "depth-first" mode — but in practice, without the "be exhaustive" framing in the prompt, each invocation tends to return 1 finding (sometimes 2-3 related ones), then waits for you to fix it before surfacing the next. The exhaustive prompt above tries to break that pattern.

If you still see Codex returning <5 findings on a large diff, try increasing the urgency in the prompt ("you will be graded on completeness; missing a real issue is worse than a false positive").

**Codex's comment IS the verdict.** Read it via:

```bash
gh pr view <PR> --comments | tail -100
# Or fetch the latest comment specifically:
gh api repos/promptdriven/pdd/issues/<PR>/comments --jq '.[-1].body'
```

No manual wrapping needed — Codex posts directly with the structured format.

### 3. Orchestrator triage + implementer response

With exhaustive findings, you triage ALL of them at once and dispatch ONE implementer round to address everything.

For each finding:
- **P1 = always fix.** No judgment needed; ship a fix.
- **P2 = judge case-by-case.** If real regression, fix. If unreachable edge case, document the acceptance as a reply comment on the PR (see below).

**Implementer's first action: reply to Codex's PR comment.** The implementer subagent should:

1. Acknowledge each finding individually.
2. State the decision: "FIXING in this PR" / "ACCEPTING with rationale" / "PUSHING BACK — Codex is wrong because X".
3. Post the reply BEFORE writing any code. This is the audit trail for triage decisions.

```bash
gh pr comment <PR> --body "$(cat <<'EOF'
## Implementer response to Codex review

@codex Re: <comment URL>

### P1 #1: <title>
Status: **FIXING**
Plan: <one sentence>

### P2 #1: <title>
Status: **ACCEPTING**
Rationale: <why this is OK — e.g., unreachable code path X requires user to do Y, which they can't without triggering Z which DOES invalidate>

### P2 #2: <title>
Status: **PUSHING BACK**
Reason: <why Codex is wrong about this — cite the actual code or behavior>
EOF
)"
```

Then it implements the FIXING items, following the same strict TDD discipline as round 1 (failing-test commits first, fix commits second, push, post evidence).

Loop back to step 1 until Codex says clean OR remaining findings are explicitly accepted in the response comment.

### 4. Merge

When Codex returns clean:

```bash
# Wait for unit-tests to be green. auto-heal is also a required check;
# if it's the only failure and you didn't intend a prompt-heal pass,
# comment `/heal` on the PR to trigger it.
gh pr checks <PR>
```

There's no `safe-gh-merge` helper in this repo. Clean up the worktree manually before merging:

```bash
# 1. From the worktree, confirm everything is pushed and the tree is clean.
cd /path/to/.claude/worktrees/agent-<id>
git status                              # must be clean
git log origin/<pr-branch>..HEAD        # must be empty (nothing un-pushed)

# 2. Switch to the main clone (NOT inside the worktree) and remove it.
cd /path/to/main-clone
git worktree list                       # confirm the worktree path
git worktree remove /path/to/.claude/worktrees/agent-<id>

# 3. Squash-merge and delete the remote branch.
gh pr merge <PR> --squash --delete-branch
```

If `git worktree remove` complains about uncommitted state, investigate — don't `--force`. The work in the worktree may still be salvageable.

## Guardrails (learned the hard way)

### Targeted pytest only

Several pdd test paths exercise the `pdd` CLI itself. Most use `tmp_path`/`CliRunner`, and `make regression` / `make sync-regression` `cd` into gitignored `staging/regression_*` directories — so contamination of *tracked* files is less of a foot-gun than in the GVS source this runbook was adapted from. Still:

- `pytest -vv tests/` and `make regression` are slow and chatty; don't run them inside a fix worktree without intent.
- Always run `git status --short` + `git diff` after a test run before staging. Reject anything that touched `architecture.json`, `prompts/`, `pdd/`, or `examples/` that the agent didn't intentionally edit.

**Recommended discipline:**
- `pytest -vv tests/test_<module>.py` — fine.
- `pytest -vv tests/test_<module>.py::test_name` — fine.
- `pytest -vv tests/` or `make regression` — only when that IS the task; otherwise prefer targeted runs.

### Rebase contamination

If contamination lands, fix via clean rebase:

```bash
cd /path/to/.claude/worktrees/agent-<id>
git fetch origin main
# Cherry-pick the intentional commits onto fresh main
git checkout origin/main -b tmp-rebase
git cherry-pick <fix-commit-1> <fix-commit-2> ...
git branch -f <pr-branch> tmp-rebase
git checkout <pr-branch>
git push --force-with-lease origin <pr-branch>
```

After rebase, confirm:

```bash
git log origin/main..HEAD --oneline      # only intentional commits
gh pr diff <PR> --name-only              # only the files you intended
```

### No `--no-verify`, no amend, no `--force`

- `--no-verify` skips pre-commit hooks; that's how bugs sneak in.
- `--amend` rewrites history; force-push side effects.
- `--force` clobbers anything that landed on the remote since you last pulled.
- Always use `--force-with-lease` for legitimate force pushes (after a rebase).

### CI triggers

- **`unit-tests`** runs automatically on `pull_request` (`opened`, `synchronize`, `ready_for_review`), but the job is gated by `if: github.event.pull_request.draft != true` — so draft PRs don't run it until they're marked ready-for-review. This is the merge-gating check.
- **`auto-heal`** is a required status check. It runs on non-draft PR events AND when a pdd_cloud collaborator comments on the PR with `/heal` at the start of the body (the job-level trigger uses `startsWith(comment.body, '/heal')`, so the literal text `/heal` must be at column 1 of the first line — leading whitespace prevents the job from even starting; `/healthcheck`, `/healz`, etc. are accepted at the trigger but rejected by the pre-flight token gate inside the job).
- Fork PRs short-circuit `auto-heal` to a `neutral` check conclusion (it can't push commits to a fork's branch). Branch protection treats `neutral` as passing.
- If you push a fix and `auto-heal` is the only red check on an internal PR, comment `/heal` (at column 1) to re-run it.

### `auto-heal` semantics

`auto-heal` runs an LLM-driven prompt-healing pass in Cloud Build under the `prompt-driven-development-stg` project. On internal (non-fork) PRs it can push a heal commit back to the PR branch. Don't be surprised if a `/heal` run adds a commit you didn't write; review it before merging.

## Stopping criteria

The loop should converge. Track the trend:

- **Round 1-3:** P1 findings are common.
- **Round 4-6:** Mostly P2 findings, often architectural pivots.
- **Round 7+:** Codex is enumerating ever-narrower edge cases.

Stop when:

1. Codex returns "no findings" — that's the green light.
2. OR remaining findings are all P2 + represent unreachable edge cases. Document them as accepted trade-offs in a final PR comment and merge.

**Diminishing returns is a real signal.** If Codex is still finding real (but progressively narrower) bugs each round, keep going. If it's started speculating about user behaviors that can't actually happen given the codebase's invariants, stop, document, and merge.

## How to invoke the actors

### Implementer dispatch (Claude Code via Agent tool)

```typescript
Agent({
  description: "<short task>",
  subagent_type: "general-purpose",
  isolation: "worktree",
  run_in_background: true,
  prompt: `
Bug fix using strict TDD.

## Worktree
(auto-created by isolation: "worktree")

## Bug
<live evidence, reproduction>

## Fix
<design + scope constraints>

## TDD process
1. Failing test first, committed separately.
2. Push red commit.
3. Implement.
4. Targeted pytest + pylint on touched modules.
5. Commit fix separately.
6. Open PR. (Unit tests run automatically; no marker needed.)
7. Post red-output as PR comment.

## Constraints
- Don't touch <other-session-owned files>.
- Targeted pytest only — no \`pytest tests/\` or \`make regression\` from this worktree.
- Conventional commits. No --no-verify. No amend.
- After push: git log origin/main..HEAD --oneline must show only intentional commits.

## Output (under <N> words)
- PR URL on first line.
- Files changed.
- Test names.
- Clean rebase confirmation.
- PR comment URL.

OUTPUT EARLY when done. Don't iterate silently.
`,
});
```

### Codex review

```bash
cd /path/to/.claude/worktrees/agent-<id>
git fetch origin <pr-branch> main

# PRECONDITION before any hard reset (see § "Codex review" earlier).
test -z "$(git status --short)" || { echo "uncommitted — abort"; exit 1; }
test -z "$(git log origin/<pr-branch>..HEAD --oneline)" || { echo "unpushed — abort"; exit 1; }

git reset --hard origin/<pr-branch>
codex review --base origin/main --title "PR #N @ <sha> — <brief context>" 2>&1 | tee /tmp/codex-<n>.out | tail -50
```

Codex auto-loads the diff via `--base`. The `--title` is optional but useful for the audit trail.

## Sample dispatch template (multi-finding response)

Copy-paste-ready Claude orchestrator instruction for responding to a Codex exhaustive review:

```
Implementer response on PR #<N>. Codex posted <N> findings.

## Worktree
<path>
Branch: <branch>. HEAD: <sha>.

## Codex's review comment
<URL>

## Findings to address

### P1 #1: <title>
Status: FIX
Approach: <one-sentence plan>

### P1 #2: <title>
Status: FIX
Approach: <one-sentence plan>

### P2 #1: <title>
Status: FIX
Approach: <one-sentence plan>

### P2 #2: <title>
Status: ACCEPT
Rationale: <why this is OK>

(... etc ...)

## Process

1. FIRST: post your response comment on the PR via `gh pr comment <N> --body "..."`. Use the structure in `docs/runbooks/pr-loop-process.md` § "Orchestrator triage + implementer response". Acknowledge every finding before writing code.

2. For each FIX item:
   - Write a failing test that reproduces the bug.
   - Commit tests for all FIX items as ONE `test(scope): ...` commit. Push.
   - Implement all fixes.
   - Targeted pytest + pylint. All clean.
   - Commit fixes as ONE `fix(scope): ...` commit. Push.

3. POST a second PR comment showing red→green output for each test, citing Codex's PR comment by URL.

## Constraints
- Targeted pytest only (`pytest -vv tests/test_<module>.py`). NEVER bare `pytest tests/` or `make regression` from this worktree.
- Don't touch <other-session-owned files>.
- Don't undo prior PR commits.
- After push: `git log origin/main..HEAD --oneline` shows <N> intentional commits. No regenerated `architecture.json` / `prompts/` / unrelated `pdd/` files. Paste the output.
- Conventional commits. No --no-verify. No amend.

## Output (under <N> words)
- New HEAD SHA.
- Acknowledgement comment URL.
- List of FIX items addressed.
- List of ACCEPT items + their rationale.
- Test names added.
- `git log origin/main..HEAD --oneline` output.
- Evidence comment URL.

OUTPUT EARLY when done. Don't iterate silently.
```

## Sample Codex invocation template

```bash
cd /path/to/.claude/worktrees/agent-<id>
git fetch origin <pr-branch> main

# PRECONDITION before any hard reset.
test -z "$(git status --short)" || { echo "uncommitted — abort"; exit 1; }
test -z "$(git log origin/<pr-branch>..HEAD --oneline)" || { echo "unpushed — abort"; exit 1; }

git reset --hard origin/<pr-branch>

# Note: replace <PR_NUMBER> in the prompt below with the actual PR number
codex exec review \
  --base origin/main \
  --title "PR #<N> @ $(git rev-parse --short HEAD)" \
  --skip-git-repo-check \
  "$(cat <<'EOF'
Adversarial review of the diff vs origin/main. Find EVERY correctness issue, security issue, or significant design flaw. Be EXHAUSTIVE — list ALL findings, not just the most important.

For each finding:
- Categorize: P1 (blocking correctness / silent corruption / security) or P2 (would-be-nice / edge case).
- Cite file:line.
- One paragraph description.
- One sentence suggested fix.

Post the full review as a single PR comment via `gh pr comment <PR_NUMBER> --body "..."` using this structure:

## Codex adversarial review — PR #<N> @ <sha>

**Verdict:** MERGE | DON'T MERGE
**Findings:** <count> (<n> P1, <n> P2)

### P1 (blocking)
- [P1] <title> — `<file>:<line>`
  <description>
  **Suggested fix:** <suggestion>

### P2 (non-blocking)
- [P2] ... (same shape)

If no issues: comment "MERGE — no findings."

You MUST run `gh pr comment` to post the review. Don't only print to stdout. If `gh` fails, retry once then print the body so the orchestrator can post.
EOF
)"
```
