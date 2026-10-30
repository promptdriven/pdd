# Retry a workflow in another checkout

As a person working in more than one clone, I want to start and reopen my workflow in the clone I chose, so that another clone's workflow does not block mine or change its workspaces.

## Acceptance criteria

1. Starting my workflow from inside another Herdr session or a plain shell opens its story chat in my assigned worktree, even when another clone of the same repository already owns a Herdr workspace.
2. Reopening a failed startup keeps my existing run and worktree; it starts the story chat once without changing the other clone's workspaces or agents.
3. Canceling my run closes only my owned chat and idle workspaces; a new run and an open work while the other clone's run stays available.
4. A changed workspace identity or an uncertain launch still refuses a blind replacement; matching a repository name alone never authorizes adoption or closure.

5. A new clone uses the short repository name when that label is free, even if another clone still has an ownership record or a qualified workspace.
6. When a different repository has the same short name, only PDD-owned repository workspaces are renamed to available qualified labels; another workspace holding a label stays untouched, and an already qualified peer keeps its label.
