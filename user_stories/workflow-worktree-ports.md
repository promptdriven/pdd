# Manage issue workflow worktrees through Runtime ports

I can validate repository origins and parents, allocate and look up issue worktrees, and release issue claims through declared Git and filesystem ports.

```pdd-boundary
prompts/cli/workflow-worktree.prompt.md
```

## Acceptance criteria

1. `githubOriginRepository` returns `promptdriven/pdd` for an ordinary GitHub SSH origin and `null` for a non-GitHub origin.
2. `lookupRepositoryParent` returns `ready` with the primary checkout root when the common directory and origin match, and `recovery_required` when they do not.
3. `allocateIssueWorktree` returns `ready` with the verified assignment for a valid unclaimed issue, and `conflict` when the requested repository disagrees with the checkout origin.
4. `lookupIssueWorktree` returns `ready` with the saved assignment when the worktree registration matches, and `recovery_required` when the run record is missing.
5. `releaseIssueClaim` returns `released` when the claim belongs to the cancelled run, and `conflict` when the claim belongs to another run.
