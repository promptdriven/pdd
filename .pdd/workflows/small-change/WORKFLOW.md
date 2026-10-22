# Small-change workflow

Use this recipe for a contained, reversible change with a clear effect and limited impact. It does not require prompt-space adoption or separate prompt and code PRs. If an existing prompt owns the changed behavior, update that prompt first, then include the prompt, code, and checks in the same PR.

1. [Confirm the scope](scope.md)
2. [Make the change](change.md)
3. [Run focused checks](verify.md)
4. [Review one PR and leave merge to the person](review.md)

If impact is broad, difficult to reverse, or unclear, stop expanding this recipe and use the feature or bug workflow with the person's agreement.
