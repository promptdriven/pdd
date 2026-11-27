# Prove changes honestly across project environments and long test runs

As a developer verifying a branch with `pdd prove`, I want environment-aware runner discovery, honest missing-runner verdicts, warning-safe summaries, and progress-aware streaming execution, so that healthy suites finish cleanly and environment gaps never masquerade as test failures.

## Acceptance criteria

1. Running `pdd prove --json` on a Python repository whose local `.venv/bin/pytest` is absent and where `pytest` is not on `PATH` exits with code 3 (`Not proved`) with fix guidance, never exit 1 (`Failed`).
2. When a passing test suite prints `=== 12 passed in 0.42s ===` followed by `PytestWarning: (rm_rf) error removing /tmp/x`, `pdd prove --json` exits with code 0 (`Proved`) and reports the passing summary line rather than the warning line.
3. On a repository without `verify.test`, `pdd prove` prefers local project environments (such as `.venv/bin/pytest`, `uv run pytest`, `poetry run pytest`, or lockfile-matched Node package managers) before bare global binaries, and runs fast lint, diff, matched verify paths, and formal checks before the full test suite.
4. Without `--timeout`, a slow test suite that continues emitting new output lines completes without hitting a 10-minute cutoff, while a silent or looping hung run stops cleanly as `Not proved` (exit 3) naming the aborted phase, completed phases, and frozen output tail.
5. Running `pdd prove --base main --test CMD --expect TEXT` without `--setup` reuses unchanged local dependency directories (`node_modules`, `.venv`, `venv`) inside disposable worktrees via temporary symlinks without mutating the caller checkout, and skips symlinking when manifests or lockfiles changed.

## What must not change

- Explicit `pdd.json` `verify.test`, merge-base trust checks, shadow-binary blocking, and explicit `--timeout MIN` (1 to 120 whole minutes) limits keep their existing semantics.
- Actual failing tests still exit with code 1 (`Failed`).
