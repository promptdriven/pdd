# Use an associated workspace check

As a developer running a Story check in an associated workspace, I want its current passing result to count at the PR 1 gate, so that the gate agrees with the run's recorded result.

## Acceptance criteria

1. A complete current passing check from an eligible associated workspace counts as a full pass.
2. A passing check from a workspace that is not eligible for current evidence does not count as a full pass.

## What must not change

- Changed files and incomplete or failed checks still block the full-pass route.

```pdd-boundary
prompts/cli/workflow-story-card.prompt.md
```
