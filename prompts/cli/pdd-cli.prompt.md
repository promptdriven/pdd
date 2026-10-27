# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Help, version, guidance, completion and recipe discovery operate using public local files only. Parse before reading guidance or workflows; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

`--skill` must make the entire canonical `docs/prompting-guide.md` available FIRST, then `skills/pdd/SKILL.md` and every Markdown reference under `skills/pdd/references/`, with installed absolute file locations so other bundled docs and recipe links can be read in the same package. Do not duplicate or rewrite the guide on disk. Tell the agent to read all of it and summarize the relevant method BEFORE ANY Story drafting. A link or claimed schema check is not loaded guidance. Read the required files before printing success; missing/unreadable guidance returns1 without claiming a complete bundle. References are sorted deterministically and ordinary regular files only; do not follow symlinked reference directories/files.

Use the package-root metadata version. For `--version`, print only that version followed by one newline, without the package name or any prefix. `workflow list` reads the bundled workflow areas only; it does not start work. Preserve stdout for successful values and stderr for errors. Explicit session invokes the public native-session launcher with full bundled guidance and the parsed user request; native inherits the existing environment and terminal. Keep imports and injection defaults self-contained, with no private transport/backend dependency.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

For a named workflow plan, use the existing session branch/native launcher with workflowName selecting only that provided recipe. No new process/approval/permission/transport path. Session without a named recipe retains all-recipes context.

The runner routes (run, done, approve, changes, cancel, status, open) call the matching export of `src/workflow-runner.mjs` (startRun, stepDone, approveRun, changeRun, cancelRun, runStatus, openRun) with the parsed values, cwd and packageRoot. Tests may inject the runner module. Print the returned message once: stdout when exitCode is 0, stderr otherwise. Return the exitCode. A missing export, an invalid reply or a thrown error prints one finite line and returns 1; never retry.

workflow list uses `listWorkflowAreas({packageRoot,cwd,home})` (home from the HOME environment value) and `formatWorkflowList` from [workflow areas](workflow-areas.prompt.md). A read failure returns 1. Local help/version/skill/completion do not import the runner.

## Help contract

The first help line is exactly `PDD: prompt-driven development for your coding agent.` Help lists the catalog forms, then says: read the Prompting guide with pdd --skill; session and named workflows open a chat in this terminal; `workflow run` starts the first area chat in Herdr session pdd and exits; the person approves each area, and pdd pushes the branch and opens a real PR after the last step; pdd never merges. Help is exit 0 and local, with no runner, native, network or auth effects.
