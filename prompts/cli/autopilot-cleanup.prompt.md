# Remove ended run worktrees safely

Own `src/autopilot-cleanup.mjs`. Export async `cleanupWorktrees({cwd,repository},ports={})`
returning `{removed, kept}` arrays of run IDs. Use injectable listRuns, lookup,
readRun, lock and execute ports; defaults use existing run listing (including
cancelled archives), allocator identity lookup, saved records, existing run lock
and bounded native subprocesses. Each failure keeps the worktree and continues.
For an archived cancelled record whose saved runDir points to a replacement,
resolve the existing RUN_DIR-cancelled-RUN_ID_PREFIX folder (first eight run ID
characters). Require the full ended identity to match, then lock and re-read that
archive. Do not lock or mutate the replacement run.
Only same-repository completed/cancelled runs with no gate and with root, branch,
runDir and runId may qualify. Never remove the invoking checkout or any root
referenced by a waiting/running/paused/stuck/question run. Lock the candidate run
and re-read the same ended identity before inspection and immediately before
removal. Verify original allocation via lookupIssueWorktree and require matching
root, branch and runId. Require at least one PR for this exact head branch in the
same repository and every PR closed or merged (read-only gh pr list --state all,
--head branch). Unknown or open means keep.

Require git status --porcelain=v1 --untracked-files=all empty, an upstream, and
rev-list --count @{upstream}..HEAD equal zero. Check the branch still matches and
HEAD equals the remote-tracking upstream commit immediately before removal.
A branch behind its upstream is conservatively retained. Do not fetch or push.
Remove only through git worktree remove ROOT from the owning source checkout,
without force. Do not delete branches, claims, run records or allocation evidence.
Keep locked, dirty, untracked, unpushed, detached, replaced or unknown worktrees.

## Dependencies

- [Run records](workflow-runs.prompt.md): native generation and verification context for listRuns and readRun.
- [Allocator](workflow-worktree.prompt.md): native generation and verification context for lookupIssueWorktree identity.
- [Workflow runner](workflow-runner.prompt.md): native generation and verification context for acquireRunLock.
- [Agent adapters](agent-adapters.prompt.md): native generation and verification context for bounded process execution.

<details><summary>Runtime interface</summary>

```json
{
  "kind": "native-only",
  "status": "draft",
  "prose_sha256": "90dae89f95ba35245b8627cee58f736f3e1bd2cd38cb5bb09a3db708c4bcd930",
  "reason": "Deletion safety depends on real locks, worktree identity and Git effects. Native evidence owners: test/autopilot-cleanup.test.mjs."
}
```
</details>
