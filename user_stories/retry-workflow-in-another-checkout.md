# Retry a workflow in another checkout

I can start and reopen my bug workflow from a separate clone while another clone of the same repository already has a workflow in Herdr.

## Acceptance criteria

1. Starting my workflow from inside another Herdr session or a plain shell opens its story chat in my assigned worktree, even when another clone of the same repository already owns a Herdr workspace.
2. Reopening a failed startup keeps my existing run and worktree; it starts the story chat once without changing the other clone's workspaces or agents.
3. Canceling my run closes only my owned chat and idle workspaces; a new run and an open work while the other clone's run stays available.
4. A changed workspace identity or an uncertain launch still refuses a blind replacement; matching a repository name alone never authorizes adoption or closure.
