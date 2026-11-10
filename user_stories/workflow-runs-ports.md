# Persist, update and select workflow run records through Runtime ports

I can read, write and update workflow `status.json` records under `.ordinary-owner` custody, inspect ownership snapshots, update cost-only metrics while preserving `progressAt`, and select runs across active and archived worktrees through declared ports.

```pdd-boundary
prompts/cli/workflow-runs.prompt.md
```

## Acceptance criteria

1. `writeRun` acquires and releases `.ordinary-owner`, increments `journalSeq`, records `updatedAt`, writes `status.json` under `runDir` and `runs.json` under `stateDir`, and fails with `invalid_run_record` when `record.runDir` is empty.
2. `readRun` reads `status.json` under `runDir` and fails with `invalid_run_dir` when `runDir` is empty.
3. `updateRun` applies an ordinary state update while clearing `progressAt` when `preserveProgress` is false, and fails with `run_ownership_busy` when `.ordinary-owner` acquisition is refused.
4. `readRunOwnership` reads `.ordinary-owner` under `runDir` without acquiring or writing, and fails with `invalid_run_dir` when `runDir` is empty.
5. `updateRunCosts` updates `suiteMinutes` and sets `progressAt` to the prior file `mtimeMs` without advancing `journalSeq`, updating `updatedAt` or calling `metrics.journalRunMutation`, and fails with `run_missing` when `status.json` is absent.
6. `gitContext` resolves `toplevel` and `commonDir` through `git.revParse` and `fs.realpath`, and fails with `invalid_cwd` when `cwd` is empty.
7. `runForWorktree` selects an archived `-cancelled-` worktree run before a replacement active run on the same issue and fails with `invalid_cwd` when `cwd` is empty.
8. `resolveRun`, `listRuns` and `allRuns` resolve and enumerate runs across repositories and `runs.json` under `stateDir` (including archived cancelled folders when `cancelled: true`), and fail on empty `cwd` or `stateDir`.
