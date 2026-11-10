# Ended run worktree cleanup ports

I can check `prompts/cli/autopilot-cleanup.prompt.md` with declared run-record, allocator, lock and subprocess ports.

```pdd-boundary
prompts/cli/autopilot-cleanup.prompt.md
```

## Acceptance criteria

1. `cleanupWorktrees` removes an ended run worktree (`run-10000001`) only after locking and re-reading the run, verifying original allocation, confirming all PRs are closed or merged, and verifying a clean worktree at the upstream commit.
2. `cleanupWorktrees` retains a candidate run worktree (`run-20000002`) in `kept` without calling `git worktree remove` when its PR is still open or verification fails.
