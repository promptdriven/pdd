# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Help, version, guidance, completion and recipe discovery operate using public local files only. Parse before reading guidance or workflows; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

`--skill` must make the entire canonical `docs/prompting-guide.md` available FIRST, then `skills/pdd/SKILL.md` and every Markdown reference under `skills/pdd/references/`, with installed absolute file locations so other bundled docs and recipe links can be read in the same package. Do not duplicate or rewrite the guide on disk. Tell the agent to read all of it and summarize the relevant method BEFORE ANY Story drafting. A link or claimed schema check is not loaded guidance. Read the required files before printing success; missing/unreadable guidance returns1 without claiming a complete bundle. References are sorted deterministically and ordinary regular files only; do not follow symlinked reference directories/files.

Use the package-root metadata version. For `--version`, print only that version followed by one newline, without the package name or any prefix. `workflow list` inspects the caller's project only; it does not execute or install recipes. Preserve stdout for successful values and stderr for errors. Explicit session invokes the public native-session launcher with full bundled guidance and the parsed user request; native inherits the existing environment and terminal. Keep imports and injection defaults self-contained, with no private transport/backend dependency.

## Dependencies

- [Issue selection](workflow-shortcuts.prompt.md), [run records](workflow-run-records.prompt.md) and [read-only reopening](workflow-session-open.prompt.md) are required for generation/runtime/testing of history commands.

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

For a named workflow plan, use the existing session branch/native launcher with workflowName selecting only that provided recipe. No new process/approval/permission/transport path. Session without a named recipe retains all-recipes context.

Workflow run/resume binds the DISTINCT public `src/workflow-runner.mjs` exports, with injection only for tests: runWorkflow({name,issue,agent,cwd,packageRoot},ports), resumeWorkflow({runId,cwd,packageRoot,decision},ports). Both resolve {exitCode,state,runId,stage,message}. ports contains exact existing loadGuidance/launchNativeSession plus stdout/stderr. Do not preload guessed context or saved agent; runner owns that and fresh native invocation per agent stage. Do not edit runner/definitions or their owning prompts.

`workflow runs [ISSUE]` is a read-only local journal view, using the shared
[issue resolver](workflow-shortcuts.prompt.md). Without an operand, show all
local runs and their stages; with one, resolve exactly one run or explain the
missing/ambiguous match. Show issue/title, workflow, worktree, each stage's result,
local start/end clock, human duration, agent and native session id (or unknown).
Never print epoch milliseconds. `--json` returns the same versioned information.
Finished stages with a proven session suggest `pdd workflow open ISSUE STAGE`,
using an issue reference rather than a run UUID or an unguarded native command.

`workflow open ISSUE STAGE` resolves through that same selector. A running stage
points to `pdd workflow attach ISSUE`. A missing, skipped, unfinished or unknown-session
stage refuses without launching. Finished stages require a real input/output TTY;
ask a default-no y/N question naming repo, issue, title and stage, saying this is
read-only inspection and **typing could change files after the stage was accepted**.
Only an explicit y/yes launches the saved native session through
[read-only reopening](workflow-session-open.prompt.md), in its saved worktree.
Decline is successful without effects. No workflow advancement, journal writes,
approval, fresh agent prompt or model request is sent. Native exit status is returned.
`workflow attach` also resolves issue forms through the shared selector and then
uses the existing runner with the resolved run id and saved cwd. Full UUID attachment retains the existing direct runner lookup.

Print the actual returned message ONCE, never dump result objects/private DTOs; return exitCode. Runner-owned mapping completed0, waiting2, failed/recovery_required1; pass the actual exitCode unchanged; waiting is not completion or pass. Missing module/export, invalid result or thrown failure is finite1 with no retry/private fallback. No native0-as-completion inference, direct journal/GitHub/approval action, same-command resume, new status flag, or automatic next stage. The runner's explicit resume owns identity/reconciliation/decisions. Existing guidance/native APIs/process behavior unchanged.

Help must distinguish manual/session recipe use from the explicit local workflow run/resume stages and actual PR effects, not claim the whole package never runs workflows.

Bind the four workflow-stage-herdr exports into workflow run/resume/attach ports alongside unchanged loadGuidance/launchNativeSession/stdout/stderr. Test injection may supply this transport module, no public flag. Public `workflow attach RUN_ID` invokes existing main `attachWorkflow({runId,cwd,packageRoot},ports)` and uses the same returned-message-once/actual-exit contract; The runner retains authority over active stage attachment; history reopening follows its separate read-only contract. Workflow run/resume keeps PDD's controller in the foreground while actual stage agents use owned background Herdr. Help must say progression stops if the controller exits; explicit resume reconciles originals. Session and direct conversation shortcuts remain foreground with existing native settings. Do not instruct stage agents to exit the foreground controller or claim native readiness is acceptance or the controller runs automatically in the background.

workflow list delegates to authoritative listWorkflowDefinitions({cwd,packageRoot}), producing {workflows:[{name,source}],default:null}; no native/runner start. Use dynamic loader import (injectable in tests), no duplicate schema or silent fallback to legacy Markdown-only files. Invalid/missing loader returns finite1. Local help/version/skill/completion rendering do not import or call loader/backend unnecessarily.


## Help contract

The first help line is exactly `PDD: prompt-driven development for your coding agent.` Root, workflow group and exact workflow run/resume/attach help describe the commands without preview labels or a claim that real workflow PRs are unproven. Retain command syntax, the real push/PR side-effect warning, foreground controller/explicit resume and saved active attachment facts. Help is exit0/local, with no runner/native/loader/network/auth effects and no added refusal, gate, flag or success claim.
