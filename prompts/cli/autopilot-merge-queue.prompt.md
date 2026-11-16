# Autopilot serialized FIFO landing queue

Own `src/autopilot-merge-queue.mjs`. Serialize landing and base-branch synchronization for verified Autopilot pull requests in deterministic first-in, first-out (FIFO) order so parallel worker branches never race each other on `origin/<baseBranch>`, stale PDD header hashes refresh automatically without AI calls, real conflicts run one bounded conflict-resolution pass before fast verification, and genuinely conflicting PRs eject cleanly without blocking later PRs.

## Domain decisions

- **Why a serialized FIFO queue instead of concurrent rebases:** When multiple worker slots finish verification around the same time, rebasing them in parallel causes later PRs to go stale the moment the first PR lands. Persisting a deterministic FIFO queue in `merge-queue.json` inside the Autopilot state directory (ordered by `(readyAt, pr)` under an exclusive file lock `merge-queue.lock`) ensures at most one head PR rebases, verifies, and lands against `origin/<baseBranch>` at a time.
- **Unified `auto` and `observe` queue progression:**
  - In `auto` mode, when the queue head PR already contains `origin/<baseBranch>` and GitHub does not report `CONFLICTING` or `DIRTY`, land the PR immediately, mark it `merged`, refresh `origin/<baseBranch>`, and advance to the next queued PR in the same pass. When post-rebase external CI is still pending before GitHub permits merge, hold the head PR in `synced` state at `syncedBaseSha` without recording a failure attempt.
  - In `observe` mode, never merge; instead keep queued `would-merge` PRs rebased and verified against the latest `origin/<baseBranch>` tip in FIFO order (`state: "synced"`, `syncedBaseSha`), skipping redundant work while `origin/<baseBranch>` remains at `syncedBaseSha` and automatically re-syncing waiting PRs as humans merge earlier PRs.
- **Zero-AI PDD header-hash refresh:** Parallel edits to a `.prompt.md` and its owned module frequently collide only on the `Generated from <prompt.prompt.md> (sha256: ...)` comment line or leave a stale header digest after Git merges disjoint prompt sections cleanly. Resolve header-only conflict blocks during `git rebase` and refresh stale owned-file header digests post-rebase directly with `promptHeaderHash` (`0` AI calls), scoped strictly to files and prompts touched by the PR or base advance.
- **Bounded conflict-resolution agent pass:** When real non-header Git conflict markers remain during `git rebase`, run at most one bounded conflict-resolution agent pass per attempt through an injected runner port supporting `codex`, `claude`, `gemini`, and `agy`, supplying the conflicted file paths, conflict hunks, `origin/<baseBranch>` diff, and PR diff. If any Git conflict markers remain afterward, immediately run `git rebase --abort` so the worktree is never left mid-rebase.
- **Fast post-rebase verification and safe push:** Before pushing a rebased head, verify PDD file ownership and header currency (`pdd owner` rules via `findOwners`) and run focused tests for touched files. Push exclusively with `git push --force-with-lease=refs/heads/<branch>:<expectedRemoteSha> origin HEAD:refs/heads/<branch>`, restricted strictly to Autopilot `pdd/core-*` PR branches—never `main`, never `baseBranch`, and never plain `--force`.
- **Per-base-tip two-strike ejection (never clog the train):** Track failed rebase/verification attempts per `origin/<baseBranch>` commit in `attemptsByBase` so earlier PRs landing ahead in the queue never penalize waiting PRs. Only when a PR fails conflict resolution or post-rebase verification twice (`MAX_ATTEMPTS_PER_BASE = 2`) against the exact same `origin/<baseBranch>` tip does the queue mark `state: "ejected"`, emit a clear human-facing note with all commit hashes, SHA-256 digests, receipt IDs, and UUIDs removed, and immediately advance to process the next queued PR. Pushing a new commit on an ejected PR branch re-admits it cleanly on enqueue.

## Public contract

Export:

- `MERGE_QUEUE_SCHEMA = "pdd.merge-queue.v1"` and `MAX_ATTEMPTS_PER_BASE = 2`.
- `isAllowedMergeQueueBranch(branch, baseBranch = "main")`: return `true` only for safe Autopilot `pdd/core-<issue>-*` branch names distinct from `baseBranch`, `main`, `master`, `trunk`, `develop`, `HEAD`, option flags, and `refs/*` or `origin/*`.
- `sanitizePublicQueueNote(text)`: strip control characters, hexadecimal commit or SHA-256 digests, UUIDs, and receipt tokens from person-facing queue notes and comments.
- `hasGitConflictMarkers(text)`: detect line-start Git conflict markers (`<<<<<<< `, `||||||| `, `=======`, `>>>>>>> `).
- `buildConflictAgentInvocation(agent = {})`: return `{kind, command, args}` for `codex`, `claude`, `gemini`, or `agy` headless execution with optional `model`, throwing on unsupported agent kinds.
- `resolveGeneratedHeaderConflicts(content, {worktree, fs})`: resolve conflict blocks in `content` when every conflict block touches only `Generated from <prompt.prompt.md>` header lines for an existing conflict-free prompt in `worktree`, returning `{resolved, content, prompts}`.
- `refreshOwnedPromptHeaders({worktree, touchedFiles, fs})`: update stale `Generated from <prompt.prompt.md> (sha256: ...)` headers on owned files in `worktree` whose file or owning prompt is in `touchedFiles`, returning `{refreshedFiles}`.
- `discoverFocusedTestFiles(worktree, touchedFiles, {fs} = {})`: return sorted repository-relative focused test files (`*.test.{mjs,js,cjs}`) in `worktree` matching `touchedFiles` directly or by stem under `test/` and `tests/` (excluding `*.e2e.test.*` unless directly touched).
- `readMergeQueue(stateDir, ports = {})`: read `merge-queue.json` from `stateDir` and return `{schema, updatedAt, items}` sorted in deterministic FIFO `(readyAt, pr)` order.
- `enqueueMergeQueueItem(input, ports = {})`: atomically insert or update `{pr, issue, issues, branch, baseBranch, headSha, readyAt, syncedBaseSha}` under `merge-queue.lock`, preserving existing `readyAt` FIFO order for active entries and re-admitting `ejected` entries only when `headSha` changed from `ejectedHeadSha`.
- `processMergeQueue(input, ports = {})`: process queued PRs one head at a time against `origin/<baseBranch>` using injected or default `fs`, `now`, `warn`, `git`, `getPullRequest`, `mergePullRequest`, `runConflictAgent`, `execAgent`, `verifyOwners`, `runFocusedTests`, `commentOnPr`, and `onEject` ports, returning `{processed, merged, synced, ejected, retried, queue}`.
- `mergeQueueStatusLine(stateDir, ports = {})`: return a concise hash-free status line summarizing queued, synced, and ejected PRs, or `""` when no active or ejected entries exist.

## Failure and safety boundaries

- Always release `merge-queue.lock` and remove temporary isolated worktrees under `<stateDir>/merge-queue-worktrees/` in `finally` blocks, aborting any unfinished `git rebase` before removal.
- Never execute `git push` when `isAllowedMergeQueueBranch` returns `false`, when conflict markers remain, or when `verifyOwners` or `runFocusedTests` fails.
- Treat already-merged PRs as `merged` and closed-unmerged PRs as `closed`, advancing immediately to the next FIFO entry without counting failure strikes.

## Dependencies

- [File owner lookup](file-owner.prompt.md): required for `findOwners`, `headerEntries`, `headerHashState`, `isTestOwnedPath`, `isTestPromptPath`, and `promptHeaderHash`.
