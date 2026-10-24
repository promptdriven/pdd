# Implement the fix

Make the smallest change that satisfies the agreed correction and preserves unaffected behavior. Use the accepted prompt and loaded dependencies. Add a regression through the public code boundary using independently authored expectations. Do not modify those expectations merely to fit the fix.

If the observed failure reveals a different contract or broader impact, explain it before expanding scope.

When launched as a runner stage, follow its exact handoff request. Prepare an intended topic branch and commit only the agreed work before a later PR stage. Preserve existing work; never force checkout, reset, stash or overwrite unrelated changes. If a safe committed topic branch cannot be established, report that limit instead of pushing or creating a PR yourself.
