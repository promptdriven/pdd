# Autopilot Post-Merge Regression Scan

As an Autopilot operator, I want the shared regression scanner to inspect pull requests merged after auto, observe, and stopped runs so that reverts, reopened issues, and follow-up regression issues are detected without false positives.

```pdd-boundary
prompts/cli/autopilot-regressions.prompt.md
```

## Acceptance criteria

1. Scanning core history and supplied candidates includes pull requests merged after auto, observe, and stopped runs, and skips unmerged observe or stopped pull requests with no error.
2. A later default-branch revert commit naming the exact merge commit hash marks that pull request as a proven revert regression.
3. A later follow-up issue labeled regression or explicitly blaming the merged pull request marks it as a proven regression reference, while an unlabeled mention stays suspect.
4. A human reopen event on the merged issue after merge is recorded as a reopened signal, while a machine-marked reopen is ignored.
