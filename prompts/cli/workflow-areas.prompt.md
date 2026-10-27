# Workflow areas

Own `src/workflow-areas.mjs`. A workflow is a skill folder `<packageRoot>/skills/pdd-NAME/` with a `workflow.json` file:

`{"version":2,"areas":[{"name":"plan","steps":["scope"],"optional":[],"gate":"approve"},{"name":"build","steps":["change","verify"],"optional":[],"gate":"pr"}]}`

- `readWorkflowAreas({packageRoot, name})` returns `{name, skill, areas}`. `skill` is `pdd-NAME`. Each area is `{name, steps, optional, gate}`.
- `listWorkflowAreas({packageRoot})` returns the valid workflows, sorted by name.
- `formatWorkflowList(list, {json})` returns text. JSON is `{"workflows":[{"name","skill","areas"}],"default":null}`. Plain text is one line per workflow with its areas and gates, then "Listing starts no work. Use pdd workflow run NAME ISSUE."

Check the shape: version 2; at least one area; names and steps are lowercase words joined by single hyphens; `optional` steps are in `steps`; every gate is `approve` except the last, which is `pr`. A missing or invalid file throws an error that names the workflow. Read only the package; a project cannot change the areas in 0.2.
