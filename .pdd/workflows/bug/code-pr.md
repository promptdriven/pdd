# Prepare and review the Code PR

The `publish-code-pr` stage publishes a Code PR with the fix, regression test, accepted vector replay when supported, and check limitations. Link the approved Story and current prompt.

The person reviews the current diff and decides whether it is ready. The linked wait stage pauses until the person merges the current revision. Recheck affected evidence after any change to the PR revision; do not report missing checks as passes.
