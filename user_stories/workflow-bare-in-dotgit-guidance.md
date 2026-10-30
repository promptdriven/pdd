# Understand an unsupported bare repository layout

As a workflow user, I can understand why a run from linked worktrees of a bare repository stored in `.git` refuses, and how to continue with an independent normal clone without changing my repository configuration.

## Acceptance criteria

1. Running `pdd workflow run small-change 17 --agent codex --base main` from this layout exits 1, names a bare repository stored in `.git` with linked worktrees, and tells me to make an independent normal clone and run the workflow there.
2. The refusal saves no workflow run, allocation record or issue claim, attempts no new worktree, and does not suggest changing `core.bare`.
3. A normal clone and a canonical bare repository with a linked checkout still allocate an issue worktree.
4. Another repository or allocation metadata identity failure before an allocation intent is saved retains "Cannot establish repository or allocation metadata identity." and the existing explanation that no allocation record or issue claim was saved and no new worktree is confirmed; an existing saved intent keeps its unconfirmed-allocation diagnostic.

## Rules to check

- The specific guidance applies only to a bare primary registration at canonical path P whose absolute Git directory, common directory and invoking common directory all equal `P + "/.git"`, with `core.bare=true`.
- Keep every repository, origin and allocation identity check. Recognizing this layout must never permit allocation or recommend changing `core.bare`.
