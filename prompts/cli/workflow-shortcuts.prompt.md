# Find the saved run a person means

Own `src/workflow-shortcuts.mjs`. Preserve W4's local issue selectors and finite
status formatting. This module resolves identity and displays choices; it never
confirms or admits a decision. All person checks belong to the shared decide seam.

Module functions `discoverRuns({cwd,all,records,fs})` and
`resolveRun(ref,{cwd,all,records,repository,waiting,fs})` read saved run records.
Use repository discovery, including linked worktrees and arbitrary subfolders via gitCommonDir, inside a checkout; use the
machine index outside it or for all. A reference may be a UUID, an unambiguous
UUID prefix of at least eight hexadecimal characters, an issue number, GitHub
issue URL, or repo#number. An omitted reference chooses only a single eligible
run. Bare numbers stay scoped to the current repository; ambiguous matches never
choose silently. With waiting true, only waiting runs qualify. Return
`{run,runs,local}` or `{run:null,runs,local,reason:'ambiguous'|'not_found'}`.
Missing journals produce unknown display state, never permission to advance.

`formatAmbiguous(runs,command)` lists repository, issue, title and the exact
issue-form command for each choice. `formatStatus(runs,{repository,all})` returns
finite text with issue, workflow, state, stage and a useful next command. Remove
terminal control characters from titles. Working runs suggest watch; failed or
uncertain runs suggest resume. Waiting gates suggest approve only if their
actual choices include approve. A merge wait suggests resume to observe the
person's normal GitHub merge, never another approval. No runs yields a plain
empty-state message. Formatting creates no journal, process or approval effect.

## Dependencies

- [Run records](workflow-run-records.prompt.md): required generation/runtime/testing
  discovery, last-journal and shared projection interfaces.
- [Shared decisions](workflow-decide.prompt.md): navigation to the admission owner;
  this selector does not load or call it.
- Node fs/promises and path: runtime read-only checkout detection.
