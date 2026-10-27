# Workflow areas

Own `src/workflow-areas.mjs`. A workflow is a skill folder `pdd-NAME/` with a `workflow.json` file:

`{"version":2,"areas":[{"name":"plan","steps":["scope"],"optional":[],"gate":"approve"},{"name":"build","steps":["change","verify"],"optional":[],"gate":"pr"}]}`

pdd looks for `pdd-NAME/workflow.json` in these skill folders, in this order, and the first one wins:
1. `<project>/.agents/skills`
2. `<project>/.claude/skills`
3. `<home>/.agents/skills`
4. `<home>/.claude/skills`
5. `<packageRoot>/skills`

A home skill folder never overrides a workflow that the package ships (same `pdd-NAME` with a `workflow.json` in `<packageRoot>/skills`): such a copy comes from `npx skills add` or `pdd setup` and may be old, with or without pdd's `.pdd-skill.json` marker. Only a project folder overrides a bundled workflow. Home folders add workflows that the package does not have (a person's own `pdd-docs`).

`<project>` is the nearest folder at or above `cwd` that has a `.git` entry; outside a repository there is no project folder. A person can copy a bundled workflow skill to `pdd-docs` in one of these folders and run `pdd workflow run docs N`.

- `readWorkflowAreas({packageRoot, name, cwd, home})` returns `{name, skill, dir, source, areas}`. `skill` is `pdd-NAME`, `dir` is the skill folder that won, `source` is project, home or package. Each area is `{name, steps, optional, gate}`.
- `listWorkflowAreas({packageRoot, cwd, home})` returns every workflow found with the same lookup, sorted by name.
- `formatWorkflowList(list, {json})` returns text. JSON is `{"workflows":[{"name","skill","source","dir","areas"}],"default":null}`. Plain text is one line per workflow with its areas, gates (a `before` approval shows as `approve → pr`) and source, then "Listing starts no work. Use pdd workflow run NAME ISSUE."

Check the shape: version 2; at least one area; names and steps are lowercase words joined by single hyphens; `optional` steps are in `steps`; the last area has gate `pr`; every other area has gate `approve`, or gate `pr` with `"then":"ask-code"` (pdd opens PR 1 there and asks whether to go on to the code area). Keep `then` in the returned area. A `pr` area may also have `"before":"approve"`: the person approves the area before pdd opens its PR (0.1.4: Try before PR 1). Keep `before` in the returned area; any other `before` is invalid. An invalid file that wins the lookup throws an error that names the workflow and the file. An unknown name throws an error that lists the known workflows.
