# Allocate, recover and close Herdr repository and run layouts through Runtime ports

I can validate Herdr inventories, enforce layout locks, open and recover run workspaces and area tabs, and close idle PDD-created workspaces through declared filesystem, worktree, compute and Herdr ports.

```pdd-boundary
prompts/cli/workflow-herdr-layout.prompt.md
```

## Acceptance criteria

1. `samePath` resolves canonical paths via `fs.realpath` so symlink aliases compare equal, and fails with `invalid_path_input` when either path is empty.
2. `validateHerdrInventory` accepts valid scoped `workspace_list`, `tab_list` and `pane_list` replies and fails with `invalid_tab_inventory` when a scoped tab row belongs to another workspace.
3. `withHerdrLayoutLock` acquires and releases the layout lock for an available directory and fails immediately with `herdr_layout_busy` when a live owner holds the lock.
4. `recoverHerdrRunLayout` refreshes `restartTerminal: true` when a verified workspace's root terminal ID changed after a server restart, and fails with `herdr_layout_identity_changed` when the root tab has split into multiple panes.
5. `openHerdrRunLayout` opens the assigned worktree from a verified parent workspace, reserves missing panes via `herdr.beforeCreate`, creates the area tab, checkpoints custody, and fails with `repository_parent_unverified` when the parent lookup is unverified.
6. `closeHerdrRunLayout` verifies creation custody (`createdWorkspaceId === workspaceId`), caller pane protection and idle shell occupancy before closing the run workspace, and fails with `run_shell_caller` when `callerPaneId` matches the root pane.
7. `closeHerdrRepoLayoutIfIdle` retains an adopted parent workspace (`createdByPdd: false`) returning `closed: false`, and fails with `invalid_herdr_layout_input` when `repository` or `commonDir` is empty.
