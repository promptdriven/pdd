# Local workflow listing

Follow `public-boundary.prompt.md` for shared public naming and closed-source boundaries.

Own `src/workflow-list.mjs`. Export `listLocalWorkflows({ cwd, readDir, stat })` and `formatLocalWorkflows(catalog, { json })`. Inspect only project `.pdd/workflows` directories with a regular `WORKFLOW.md`; do not traverse symlinked `.pdd`, workflow roots, workflow directories, or workflow files. Return sorted `{ workflows, default: null }`, and treat a missing workflow directory as an empty catalog. Propagate other filesystem errors. JSON formatting returns one JSON string; human formatting lists relative file paths and reminds people to review, commit, and push workflow changes before starting work.
