# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Help, version, completion and recipe discovery operate using public local files only. There is no `--skill` command; pdd prints no guide. Parse before reading skills or workflows; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

Use the package-root metadata version. For `--version`, print only that version followed by one newline, without the package name or any prefix. `workflow list` inspects the caller's project only; it does not execute or install recipes. Preserve stdout for successful values and stderr for errors. Explicit session renders the short [session intro](session-intro.prompt.md) from packageRoot, cwd and the request words joined by one space, then invokes the public native-session launcher with that message; native inherits the existing environment and terminal. If the intro cannot be rendered, write `The PDD skills could not be read. Use a complete PDD package.` to stderr and return 1 before any launch. Keep imports and injection defaults self-contained, with no private transport/backend dependency.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

For a named workflow plan, use the same session branch and pass workflowName to the intro, which then names the pdd-NAME skill. No new process/approval/permission/transport path.

Workflow run/resume binds the DISTINCT public `src/workflow-runner.mjs` exports, with injection only for tests: runWorkflow({name,issue,agent,cwd,packageRoot},ports), resumeWorkflow({runId,cwd,packageRoot,decision},ports). Both resolve {exitCode,state,runId,stage,message}. ports contains exact existing loadGuidance/launchNativeSession plus stdout/stderr. Do not preload guessed context or saved agent; runner owns that and fresh native invocation per agent stage. Preserve runner authority and definition semantics.

Print the actual returned message ONCE, never dump result objects/private DTOs; return exitCode. Runner-owned mapping completed0, waiting2, failed/recovery_required1; pass the actual exitCode unchanged; waiting is not completion or pass. Missing module/export, invalid result or thrown failure is finite1 with no retry/private fallback. No native0-as-completion inference, direct journal/GitHub/approval action, same-command resume, new status flag, or automatic next stage. The runner's explicit resume owns identity/reconciliation/decisions. Existing guidance/native APIs/process behavior unchanged.

Help must distinguish manual/session recipe use from the explicit local workflow run/resume stages and actual PR effects, not claim the whole package never runs workflows.

Bind the four workflow-stage-herdr exports into workflow run/resume/attach ports alongside unchanged loadGuidance/launchNativeSession/stdout/stderr. Test injection may supply this transport module, no public flag. Public `workflow attach RUN_ID` invokes existing main `attachWorkflow({runId,cwd,packageRoot},ports)` and uses the same returned-message-once/actual-exit contract; CLI does not resolve journals/agent IDs or start a conversation on archived history. Workflow run/resume keeps PDD's controller in the foreground while actual stage agents use owned background Herdr. Help must say progression stops if the controller exits; explicit resume reconciles originals. Session and direct conversation shortcuts remain foreground with existing native settings. Do not instruct stage agents to exit the foreground controller or claim native readiness is acceptance or the controller runs automatically in the background.

workflow list delegates to authoritative listWorkflowDefinitions({cwd,packageRoot}), producing {workflows:[{name,source}],default:null}; no native/runner start. Use dynamic loader import (injectable in tests), no duplicate schema or silent fallback to legacy Markdown-only files. Invalid/missing loader returns finite1. Local help/version/completion rendering do not import or call loader/backend unnecessarily.


## Help contract

The first help line is exactly `PDD: prompt-driven development for your coding agent.` Root, workflow group and exact workflow run/resume/attach help describe the commands without preview labels or a claim that real workflow PRs are unproven. Retain command syntax, the real push/PR side-effect warning, foreground controller/explicit resume and saved active attachment facts. Help is exit0/local, with no runner/native/loader/network/auth effects and no added refusal, gate, flag or success claim.

## Live foreground workflow output

For workflow run/resume, print a short starting/inspection line immediately after parsing (a bare issue number is shown as `#N`), before dynamic imports, repository or provider work. State that the terminal stays busy until a gate. Create the [progress renderer](workflow-progress.prompt.md) and pass its observe function as the runner's optional onProgress port. Keep the runner's final returned message exactly once and unchanged, except that a waiting result whose gate the renderer already printed (gateShown) is not repeated. Attach, sessions and discovery keep their existing behavior.

While run/resume is active, handle SIGINT by printing the renderer's truthful interruption guidance and exiting 130. The foreground controller stops; the agent may keep working in Herdr, and an inspection-only resume does not advance it. Explain the exact inspection command and subsequent explicit approve command. Never claim the whole run progresses in the background, cancel/kill a Herdr agent, invent an ID, or change run allocation. Remove the signal listener on every ordinary return/error. signalSource and exit dependencies may be injected for tests; production uses process and process.exit.

For resume, retain the already parsed UUID in the progress renderer before lookup so an early interruption can still name the exact saved-run commands. This is display state only; do not pass a generated run ID into runWorkflow.

Supply closeHerdrRun from the stage adapter to the workflow runner so terminal runs can close their owned Herdr worktree workspace.
