# Check Stories with nested fixtures

I can check my repository's Stories when it ships a nested example project, while still seeing real missing dependencies.

## Acceptance criteria

1. Checking all repository Stories skips a project under `test/fixtures` with its own `user_stories` and `tests` directories, and reports the skipped project root.
2. A missing dependency of a selected repository test remains an actionable refusal.
3. An explicitly selected fixture test is not silently skipped and still reports a missing dependency.
4. A folder named `fixtures` or `examples` alone does not cause its Stories or tests to be skipped.
5. Without such a nested fixture project, discovery and selection behave as before.
6. The nested example fixture remains present and usable.

## Rules to check

A nested project qualifies only when both direct directories contain Git-visible files. Skip only its descendants for an unqualified all-Story selection. Do not remove the fixture or silently accept a missing dependency.
