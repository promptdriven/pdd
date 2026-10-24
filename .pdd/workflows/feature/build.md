# Implement the agreed behavior

Implement only the agreed Story, using the current prompt and its required dependencies as the behavior source. Read affected callers before changing a public interface. Retain independent expected values; do not rewrite them just to match a surprising implementation result.

Exercise changed behavior through the public code boundary with the project's real test tools. Keep changes reviewable, explain material design choices and avoid unrelated dependencies or refactoring.

When launched as a runner stage, follow its exact handoff request. Prepare an intended topic branch and commit only the agreed work before a later PR stage. Preserve existing work; never force checkout, reset, stash or overwrite unrelated changes. If a safe committed topic branch cannot be established, report that limit instead of pushing or creating a PR yourself.
