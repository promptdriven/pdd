# Make the change

Change only the agreed scope. If an existing prompt owns changed behavior, update it before code. A new prompt is not required for an unrelated typo, configuration edit or similar contained maintenance.

For behavior changes, add a meaningful native test through the public boundary with an independent expected outcome. Preserve existing expectations unless the accepted requirement changes. Avoid unrelated refactors and dependencies.

When launched as a runner stage, follow its exact handoff request. Prepare an intended topic branch and commit only the agreed work before a later PR stage. Preserve existing work; never force checkout, reset, stash or overwrite unrelated changes. If a safe committed topic branch cannot be established, report that limit instead of pushing or creating a PR yourself.
