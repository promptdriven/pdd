# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Help, version, completion and recipe discovery operate using public local files only. pdd prints no guide; the agent loads the pdd-prompting skill. Parse before reading skills or workflows; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

Use the package-root metadata version. For `--version`, print only that version followed by one newline, without the package name or any prefix. `workflow list` reads the bundled workflow areas only; it does not start work. Preserve stdout for successful values and stderr for errors. `setup` calls [project setup](project-setup.prompt.md) `setupProject({cwd, packageRoot})`. It prints `pdd setup: wrote the PDD block in FILE.` or `pdd setup: FILE already has this PDD block. No change.` and returns 0. On an error it prints `pdd setup: ` and the error message to stderr and returns 1. pdd starts no chat itself outside `workflow run`. Keep imports and injection defaults self-contained, with no private transport/backend dependency.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

The runner routes (run, done, approve, changes, cancel, status, open) call the matching export of `src/workflow-runner.mjs` (startRun, stepDone, approveRun, changeRun, cancelRun, runStatus, openRun) with the parsed values, cwd and packageRoot. Tests may inject the runner module. Print the returned message once: stdout when exitCode is 0, stderr otherwise. Return the exitCode. A missing export, an invalid reply or a thrown error prints one finite line and returns 1; never retry.

workflow list uses `listWorkflowAreas({packageRoot,cwd,home})` (home from the HOME environment value) and `formatWorkflowList` from [workflow areas](workflow-areas.prompt.md). A read failure returns 1. Local help/version/skill/completion do not import the runner.

## Help contract

The first help line is exactly `PDD: prompt-driven development for your coding agent.` Help lists the catalog forms, then says: open Codex or Claude as usual and call a PDD skill (/pdd-feature, /pdd-bug, /pdd-small-change or /pdd-prompting); `workflow run` starts the first area chat in Herdr session pdd and exits; the person approves each area, and pdd pushes the branch and opens a real PR after the last step; pdd never merges. Help is exit 0 and local, with no runner, network or auth effects.

## Runtime commands

For the `runtime-check` and `runtime-try` plans, import the [runtime client](runtime-client.prompt.md) dynamically and call `runCheck` or `runTry` with the operands, the options and cwd, plus stdout and stderr. Return its exit code unchanged. Help for check and try stays local. If the client throws, write `pdd stopped with an internal error. If it sent checks, read them with pdd check --read. Do not send them again.` to stderr and return 3, because checks may have been sent.
