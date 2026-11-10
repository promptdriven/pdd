# Discover and format workflow areas through Runtime ports

I can resolve workflow skill precedence, validate `workflow.json` shape and approval advisories, and format workflow listings through declared file and directory ports.

```pdd-boundary
prompts/cli/workflow-areas.prompt.md
```

## Acceptance criteria

1. Reading a bundled workflow skips any home copy with the same name, returns the package definition with `before`, `then` and `replay_evidence` preserved, and reading a custom home single-area `pr` workflow adds the missing-approve-gate advisory.
2. Reading an unknown workflow fails with `workflow_unknown`.
3. Listing workflows across project, home and package skill folders returns them sorted by name with project overrides winning over bundled workflows.
4. Listing workflows fails with `workflow_invalid` when a winning `workflow.json` violates the version or area gate rules.
5. Formatting a workflow list renders plain-text area gates (`approve → pr` for `before: "approve"`), advisories and the no-work footer, and rejects a workflow record with no areas with `invalid_workflow_list`.
