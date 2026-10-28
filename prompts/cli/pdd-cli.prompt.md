# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Help, version, completion and recipe discovery operate using public local files only. pdd prints no guide; the agent loads the pdd-prompting skill. Parse before reading skills or workflows; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

Use the package-root metadata version. For `--version`, print only that version followed by one newline, without the package name or any prefix. `workflow list` reads the bundled workflow areas only; it does not start work. Preserve stdout for successful values and stderr for errors. `setup` does two things, in this order. First it calls [skills install](skills-install.prompt.md) `setupSkills({packageRoot, cwd, home, claudeConfigDir})` with home from the HOME environment value (else `os.homedir()`) and `CLAUDE_CONFIG_DIR`. For each agent result it prints `Updated N PDD skills in ROOT: NAMES` when it updated copies, then, when found, `PDD skills found in FOLDER`, or when `stale` is set `PDD skills in FOLDER are older than pdd VERSION. To update them, run: npx skills update SCOPE` (`differ from the skills of pdd VERSION` for `'differs'`; VERSION from the package metadata; SCOPE `-p` when FOLDER is `<cwd>/.agents/skills` or `<cwd>/.claude/skills`, else `-g`), else `Installed N PDD skills to ROOT: NAMES` when it copied any. NAMES are the skill folder names, joined by `, `, in the order of `PDD_SKILL_NAMES`. Use `skill` instead of `skills` when N is 1. An agent error prints `pdd setup: the PDD skills could not be installed in ROOT (REASON).` to stderr. Then it calls [project setup](project-setup.prompt.md) `setupProject({cwd, packageRoot})` and prints `Wrote the PDD block in FILE.` or `FILE already has this PDD block. No change.`; its error prints `pdd setup: ` and the message to stderr. Each part runs even when the other fails. Exit 1 if any part failed, else 0. No other command installs skills. pdd starts no chat itself outside `workflow run`. Keep imports and injection defaults self-contained, with no private transport/backend dependency.

For setup, version reporting and workflow startup, use [PATH diagnostics](path-diagnostic.prompt.md). Print the returned lines to stderr. Setup uses the full report; `--version` uses its conflict-only mode while stdout remains exactly the package version and newline; `workflow run` uses its compact shadowing warning before dispatch. Other commands, help and invalid syntax do not discover or probe PATH. A diagnostic failure must not prevent the requested command. No installer script is part of this package; setup is the supported install check.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

The runner routes (run, done, ask, approve, changes, cancel, status, open) call the matching export of `src/workflow-runner.mjs` (startRun, stepDone, askPerson, approveRun, changeRun, cancelRun, runStatus, openRun) with the parsed values, cwd and packageRoot. For startRun, pass `base` only when `--base` was given, using its text unchanged; the runner owns branch validation and selection. For status, pass `all`, `cancelled` and `json` only when their flag is given. Tests may inject the runner module. Print the returned message once: stdout when exitCode is 0, stderr otherwise. Return the exitCode. A missing export, an invalid reply or a thrown error prints one finite line and returns 1; never retry.

workflow list uses `listWorkflowAreas({packageRoot,cwd,home})` (home from the HOME environment value) and `formatWorkflowList` from [workflow areas](workflow-areas.prompt.md). A read failure returns 1. Local help/version/skill/completion do not import the runner.

## Help contract

The first help line is exactly `PDD: prompt-driven development for your coding agent.` Help lists the catalog forms, then says: `Open Codex or Claude as usual and call a PDD skill: $pdd-feature in Codex, /pdd-feature in Claude Code (also pdd-bug, pdd-small-change, pdd-prompting).` (Codex calls a skill with `$name`, Claude Code with `/name`); `workflow run` starts the first area chat in Herdr session pdd and exits; the person approves each area, and pdd pushes the branch and opens a real PR after the last step; pdd never merges. Help is exit 0 and local, with no runner, network or auth effects.

## Runtime commands

For the `prompt-approve` plan, import [prompt approve](prompt-approve.prompt.md) dynamically and return `runApprove({words, cwd}, {stdout, stderr})` unchanged.

For the `runtime-check` and `runtime-try` plans, import the [runtime client](runtime-client.prompt.md) dynamically and call `runCheck` or `runTry` with the operands, the options and cwd, plus stdout and stderr. Return its exit code unchanged. Help for check and try stays local. If the client throws, write `pdd stopped with an internal error. If it sent checks, read them with pdd check --read. Do not send them again.` to stderr and return 3, because checks may have been sent.

For `workflow-view`, dynamically import [read-only review](workflow-view.prompt.md) and call `viewRun({ref: operands[0], cwd})`. Print the result once (stdout on success, stderr on failure) and return its exit code. This route must not import the workflow runner, inspect Herdr, or execute PATH version probes.

Route workflow-evidence to workflow runner recordEvidence with issue ref and required --summary file path; missing summary is a CLI input error. It records evidence only, not workflow progression.
