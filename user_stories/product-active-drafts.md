# Try connected product drafts

As a product builder, I want to try my unmerged part drafts in one Simulator, so that I can explore the connected product before generating code.

## Acceptance criteria

1. `pdd simulate --product` includes my active phone and server drafts in one connected product, and a phone tap runs the declared server work against the same shared world.
2. Shared contracts and unrelated files come from my product checkout; each draft supplies only its declared part and referenced views.
3. Missing draft inputs, multiple active runs for one part and conflicting view ownership stop setup with the affected part and paths.
4. Without active part drafts, whole-product exploration uses the product checkout as before.

## What must not change

- Source files, worktrees, branches, approvals, part-start prerequisites and journey prerequisites remain unchanged.
