# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Help, version, completion and recipe discovery operate using public local files only. pdd prints no guide; the agent loads the pdd-prompting skill. Parse before reading skills or workflows; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

Use the package-root metadata version. For `--version`, print only that version followed by one newline, without the package name or any prefix. `workflow list` reads the bundled workflow areas only; it does not start work. Preserve stdout for successful values and stderr for errors. Explicit session renders the short [session intro](session-intro.prompt.md) from packageRoot, cwd and the request words joined by one space, then invokes the public native-session launcher with that message; native inherits the existing environment and terminal. If the intro cannot be rendered, write `The PDD skills could not be read. Use a complete PDD package.` to stderr and return 1 before any launch. Keep imports and injection defaults self-contained, with no private transport/backend dependency.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

For a named workflow plan, use the same session branch and pass workflowName to the intro, which then names the pdd-NAME skill. No new process/approval/permission/transport path.

The runner routes (run, done, approve, changes, cancel, status, open) call the matching export of `src/workflow-runner.mjs` (startRun, stepDone, approveRun, changeRun, cancelRun, runStatus, openRun) with the parsed values, cwd and packageRoot. Tests may inject the runner module. Print the returned message once: stdout when exitCode is 0, stderr otherwise. Return the exitCode. A missing export, an invalid reply or a thrown error prints one finite line and returns 1; never retry.

workflow list uses `listWorkflowAreas({packageRoot})` and `formatWorkflowList` from [workflow areas](workflow-areas.prompt.md). A read failure returns 1. Local help/version/completion do not import the runner.

## Help contract

The first help line is exactly `PDD: prompt-driven development for your coding agent.` Help lists the catalog forms, then says: session and named workflows open a chat in this terminal; `workflow run` starts the first area chat in Herdr session pdd and exits; the person approves each area, and pdd pushes the branch and opens a real PR after the last step; pdd never merges. Help is exit 0 and local, with no runner, native, network or auth effects.
