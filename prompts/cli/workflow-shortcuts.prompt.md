# Resolve a saved workflow by issue

Own `src/workflow-shortcuts.mjs`. Module functions `discoverRuns`, `resolveRun`,
`formatStatus` and `formatAmbiguous` provide read-only selection and display.
Preserve full UUID selection while adding issue numbers, #N, repo#N,
owner/repo#N, GitHub issue URLs and unique hexadecimal prefixes of at least eight
characters. An exact issue-number match takes priority over a decimal ID prefix.

A bare number or absent operand inside any checkout is scoped to its Git common
directory, including subfolders and linked worktrees for other issues. A missing local
match must never fall back to another repository. Explicit qualified references
or UUIDs may select a machine-indexed run. Outside any repository, use the machine
index. One match selects; zero reports no match; multiple matches refuse and list
issue titles and exact commands. Never select a latest run arbitrarily.

Use repo#N for disambiguation, expanding to owner/repo#N only when short repository
names collide. Status/watch next-step commands retain the canonical owner/repo#N
when no local repository scope is supplied: displayed rows may omit collisions
elsewhere in the machine index. Commands displayed in a known local repository
can use bare N. Compact row labels do not determine command selectors.
`resolveRun(ref,{cwd,records?,all?,repository?,waiting?,fs?})` returns
`{run,runs,local,reason?}`; selected run retains its saved root and runDir so the
runner can validate the original assignment. Waiting selection considers actual
person gates when their decisions are known. A merge wait with no person decisions
suggests resume. Status --all includes only waiting/running runs; each row names
issue, title, workflow, current stage, state and the next supported issue command.
Discovery never authorizes a decision or writes workflow state.

## Dependencies

- [Run records](workflow-run-records.prompt.md): required generation/runtime/testing
  for journal-derived discovery, machine index and Git common-directory identity.
