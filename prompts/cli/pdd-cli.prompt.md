# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Help, version, guidance, completion and recipe discovery operate using public local files only. Parse before reading guidance or workflows; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

`--skill` must make the entire canonical `docs/prompting-guide.md` available FIRST, then `skills/pdd/SKILL.md` and every Markdown reference under `skills/pdd/references/`, with installed absolute file locations so other bundled docs and recipe links can be read in the same package. Do not duplicate or rewrite the guide on disk. Tell the agent to read all of it and summarize the relevant method BEFORE ANY Story drafting. A link or claimed schema check is not loaded guidance. Read the required files before printing success; missing/unreadable guidance returns1 without claiming a complete bundle. References are sorted deterministically and ordinary regular files only; do not follow symlinked reference directories/files.

Use the package-root metadata version. `workflow list` inspects the caller's project only; it does not execute or install recipes. Preserve stdout for successful values and stderr for errors. Explicit session invokes the public native-session launcher with full bundled guidance and the parsed user request; native inherits the existing environment and terminal. No private Host/transport/backend dependency may remain, including an unused import or injection default.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

For a named workflow plan, use the existing session branch/native launcher with workflowName selecting only that provided recipe. No new process/approval/permission/transport path. Session without a named recipe retains all-recipes context.

Workflow run/resume binds the DISTINCT public `src/workflow-runner.mjs` exports, with injection only for tests: runWorkflow({name,issue,agent,cwd,packageRoot},ports), resumeWorkflow({runId,cwd,packageRoot,decision},ports). Both resolve {exitCode,state,runId,stage,message}. ports contains exact existing loadGuidance/launchNativeSession plus stdout/stderr. Do not preload guessed context or saved agent; runner owns that and fresh native invocation per agent stage. Do not edit runner/definitions or their owning prompts.

Print the actual returned message ONCE, never dump result objects/private DTOs; return exitCode. Runner-owned mapping completed0, waiting2, failed/recovery_required1; pass the actual exitCode unchanged; waiting is not completion or pass. Missing module/export, invalid result or thrown failure is finite1 with no retry/private fallback. No native0-as-completion inference, direct journal/GitHub/approval action, same-command resume, new status flag, or automatic next stage. The runner's explicit resume owns identity/reconciliation/decisions. Existing guidance/native APIs/process behavior unchanged.

Help must distinguish manual/session recipe use from the explicit local workflow run/resume stages and actual PR effects, not claim the whole package never runs workflows.

Editable/background successor: bind FOUR exact workflow-stage-herdr exports into workflow run/resume/attach ports alongside unchanged loadGuidance/launchNativeSession/stdout/stderr. Test injection may supply this transport module, no public flag. Public `workflow attach RUN_ID` invokes existing main `attachWorkflow({runId,cwd,packageRoot},ports)` and uses the same returned-message-once/actual-exit contract; CLI does not resolve journals/agent IDs or start a conversation on archived history. Workflow run/resume keeps PDD's controller in the foreground while actual stage agents use owned background Herdr. Help must say progression stops if the controller exits; explicit resume reconciles originals. Session and direct conversation shortcuts remain foreground with existing native settings. Remove foreground-only stage exit instruction from runner help; do not claim native readiness or automatic background controller.

workflow list delegates to authoritative listWorkflowDefinitions({cwd,packageRoot}), producing {workflows:[{name,source}],default:null}; no native/runner start. Use dynamic loader import (injectable in tests), no duplicate schema or silent fallback to legacy Markdown-only files. Invalid/missing loader returns finite1. Local help/version/skill/completion rendering do not import or call loader/backend unnecessarily.


## Publication: truthful preview help without behavior changes

Global/root help, workflow group help and exact workflow run/resume/attach help must visibly identify the workflow runner as PREVIEW and plainly state that a real workflow PR is not yet proven. Keep existing command syntax, real push/PR side-effect warning, foreground controller/explicit resume and saved active attachment facts. Preview is a release label, not a new refusal/gate/flag or readiness claim. Help stays exit0/local, with no runner/native/loader/network/auth effects. Other commands remain supported normally; no guidance/native/controller/dispatch semantics change in this slice. Source review/full and publication follow the existing designated route, without waiting for real-workflow-PR proof for this preview release.
