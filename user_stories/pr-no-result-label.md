# Find PRs with no pdd result

As a person filtering pull requests, I can find runs with no pdd test or lint result by the `pdd:no-verdict` GitHub label.

## Acceptance criteria

1. A published PR with no saved pdd test or lint result has the `pdd:no-verdict` label, even if an agent claims a result.
2. When a saved pdd test or lint result exists, including a failed result, publication or PR 1 refresh removes the label and keeps other labels.
3. A missing repository label is created; an existing label is left unchanged. A label update failure is reported as a warning.
