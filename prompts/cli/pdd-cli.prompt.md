# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Help, version, guidance, completion and recipe discovery operate using public local files only. Parse before reading guidance or workflows; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

`--skill` must make the entire canonical `docs/prompting-guide.md` available FIRST, then `skills/pdd/SKILL.md` and every Markdown reference under `skills/pdd/references/`, with installed absolute file locations so other bundled docs and recipe links can be read in the same package. Do not duplicate or rewrite the guide on disk. Tell the agent to read all of it and summarize the relevant method BEFORE ANY Story drafting. A link or claimed schema check is not loaded guidance. Read the required files before printing success; missing/unreadable guidance returns1 without claiming a complete bundle. References are sorted deterministically and ordinary regular files only; do not follow symlinked reference directories/files.

Use the package-root metadata version. For `--version`, print only that version followed by one newline, without the package name or any prefix. `workflow list` inspects the caller's project only; it does not execute or install recipes. Preserve stdout for successful values and stderr for errors. Explicit session invokes the public native-session launcher with full bundled guidance and the parsed user request; native inherits the existing environment and terminal. Keep imports and injection defaults self-contained, with no private transport/backend dependency.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

For a named workflow plan, use the existing session branch/native launcher with workflowName selecting only that provided recipe. No new process/approval/permission/transport path. Session without a named recipe retains all-recipes context.

Workflow run/resume binds the DISTINCT public `src/workflow-runner.mjs` exports, with injection only for tests: runWorkflow({name,issue,agent,chat,cwd,packageRoot},ports), resumeWorkflow({runId,cwd,packageRoot,decision},ports). Both resolve {exitCode,state,runId,stage,message}. ports contains exact existing loadGuidance/launchNativeSession plus stdout/stderr. Do not preload guessed context or saved agent; runner owns context and the saved stage/area mode. Preserve runner authority and definition semantics.

Print the actual returned message ONCE, never dump result objects/private DTOs; return exitCode. Runner-owned mapping completed/running0, waiting2, failed/recovery_required1; pass the actual exitCode unchanged; waiting is not completion or pass. Missing module/export, invalid result or thrown failure is finite1 with no retry/private fallback. No native0-as-completion inference, direct journal/GitHub/approval action, same-command resume, new status flag, or automatic next stage. The runner's explicit resume owns identity/reconciliation/decisions. Existing guidance/native APIs/process behavior unchanged.

Help must distinguish manual/session recipe use from the explicit local workflow run/resume stages and actual PR effects, not claim the whole package never runs workflows.

Bind the four workflow-stage-herdr exports into workflow run/resume/attach ports alongside unchanged loadGuidance/launchNativeSession/stdout/stderr. Test injection may supply this transport module, no public flag. Public `workflow attach RUN_ID` invokes existing main `attachWorkflow({runId,cwd,packageRoot},ports)` and uses the same returned-message-once/actual-exit contract; CLI does not resolve journals/agent IDs or start a conversation on archived history. Default stage-mode workflow run/resume keeps PDD's controller in the foreground while actual stage agents use owned background Herdr. Help must say progression stops if the controller exits; explicit resume reconciles originals. Session and direct conversation shortcuts remain foreground with existing native settings. Do not instruct stage agents to exit the foreground controller or claim native readiness is acceptance or the controller runs automatically in the background.

workflow list delegates to authoritative listWorkflowDefinitions({cwd,packageRoot}), producing {workflows:[{name,source}],default:null}; no native/runner start. Use dynamic loader import (injectable in tests), no duplicate schema or silent fallback to legacy Markdown-only files. Invalid/missing loader returns finite1. Local help/version/skill/completion rendering do not import or call loader/backend unnecessarily.

Short decision commands resolve saved runs through the local repository's run records, including linked worktrees. Outside a repository they use the machine runs index; `--all` shows every waiting or running run. A bare issue number is scoped to the current repository. If multiple repositories share the number, refuse and list each `<repo>#N "<title>"` with its exact issue-form command. Approve, changes and skip delegate person evidence to the shared decide seam. A terminal approval requires a TTY; `--yes` never supplies authority to a non-TTY call. Agent-marked and non-TTY relays require W11 USER-message evidence after the gate. The confirmation question includes repository, issue and title. `workflow changes` submits the person's text to the same decide seam and starts its supported revision path. Every printed next-step command uses an issue reference rather than a UUID. All three decisions call one small decision seam.


## Help contract

The first help line is exactly `PDD: prompt-driven development for your coding agent.` Root, workflow group and exact workflow run/resume/attach help describe the commands without preview labels or a claim that real workflow PRs are unproven. Retain command syntax, the real push/PR side-effect warning, foreground controller/explicit resume and saved active attachment facts. Help is exit0/local, with no runner/native/loader/network/auth effects and no added refusal, gate, flag or success claim.

## Live foreground workflow output

For workflow run/resume, print a short starting/inspection line immediately after parsing (a bare issue number is shown as `#N`), before dynamic imports, repository or provider work. For default stage mode state that the terminal stays busy until a gate; --chat states that the command returns after delivery. Create the [progress renderer](workflow-progress.prompt.md) and pass its observe function as the runner's optional onProgress port. Keep the runner's final returned message exactly once and unchanged. Attach, sessions and discovery keep their existing behavior.

While run/resume is active, handle SIGINT by printing the renderer's truthful interruption guidance and exiting 130. The foreground controller stops; the agent may keep working in Herdr, and an inspection-only resume does not advance it. Explain the exact inspection command and subsequent explicit approve command. Never claim the whole run progresses in the background, cancel/kill a Herdr agent, invent an ID, or change run allocation. Remove the signal listener on every ordinary return/error. signalSource and exit dependencies may be injected for tests; production uses process and process.exit.

For resume, retain the already parsed UUID in the progress renderer before lookup so an early interruption can still name the exact saved-run commands. This is display state only; do not pass a generated run ID into runWorkflow.

Area startup passes chat:true only for --chat and accepts running replies. workflow report calls reportWorkflowStage and prints one JSON result; native test output goes to stderr. Supply inspectHerdrChat and closeHerdrRun only when exported. All short decisions call W1b decideWorkflow directly, including chat relays; it owns confirmation/evidence. Never pre-confirm separately or implement another person check.

`pdd step done STAGE RUN_ID ATTEMPT` is the area-report alias and emitted form; both forms bind the same saved run/stage/attempt and return the same JSON.

`workflow decide` is the bound public adapter described by [shared decisions](workflow-decide.prompt.md). It returns one validated finite result or one v1 JSON line; malformed replies fail. Short commands resolve identity via W4 discovery, call the runner's readWorkflowDecision, and pass its gate binding to the same module. Legacy resume with --decision also uses that seam. Phone options --via phone --phone ID --approval TOKEN only forward to its signature/ledger verifier; never authenticate in the CLI.

A composed clientAdapter.lookupPhone may supply the trusted phone ledger port.
Forward the adapter with its receiver intact to shared decide; no CLI argument
creates or installs it, and absence still refuses phone verification.
