# Workflow areas

Own `src/workflow-areas.mjs`. A workflow is a skill folder `pdd-NAME/` with a `workflow.json` file:

`{"version":2,"areas":[{"name":"plan","steps":["scope"],"optional":[],"gate":"approve"},{"name":"build","steps":["change","verify"],"optional":[],"gate":"pr"}]}`

pdd looks for `pdd-NAME/workflow.json` in these skill folders, in this order, and the first one wins:
1. `<project>/.agents/skills`
2. `<project>/.claude/skills`
3. `<home>/.agents/skills`
4. `<home>/.claude/skills`
5. `<packageRoot>/skills`

A home skill folder that holds pdd's install marker `.pdd-skill.json` is a copy that pdd installed, not an override: skip it, so an old installed copy never shadows the running package. A hand-made home skill (no marker) still wins.

`<project>` is the nearest folder at or above `cwd` that has a `.git` entry; outside a repository there is no project folder. A person can copy a bundled workflow skill to `pdd-docs` in one of these folders and run `pdd workflow run docs N`.

- `readWorkflowAreas({packageRoot, name, cwd, home})` returns `{name, skill, dir, source, areas}`. `skill` is `pdd-NAME`, `dir` is the skill folder that won, `source` is project, home or package. Each area is `{name, steps, optional, gate}`.
- `listWorkflowAreas({packageRoot, cwd, home})` returns every workflow found with the same lookup, sorted by name.
- `formatWorkflowList(list, {json})` returns text. JSON is `{"workflows":[{"name","skill","source","dir","areas"}],"default":null}`. Plain text is one line per workflow with its areas, gates and source, then "Listing starts no work. Use pdd workflow run NAME ISSUE."

Check the shape: version 2; at least one area; names and steps are lowercase words joined by single hyphens; `optional` steps are in `steps`; the last area has gate `pr`; every other area has gate `approve`, or gate `pr` with `"then":"ask-code"` (pdd opens PR 1 there and asks whether to go on to the code area). Keep `then` in the returned area. An invalid file that wins the lookup throws an error that names the workflow and the file. An unknown name throws an error that lists the known workflows.
