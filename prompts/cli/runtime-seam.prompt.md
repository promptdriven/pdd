# PDD to Runtime seam

Own `src/runtime-seam.mjs` and the stable launcher entry `src/try-doors.mjs`. `src/runtime-seam.mjs` is the sole module in pdd outside `src/runtime/` permitted to import `src/runtime/`. Every pdd module in `src/`, `bin/`, and `scripts/` accesses Runtime commands, local format and workspace readers, check-plan and outcome helpers, and constants exclusively through `./runtime-seam.mjs`.

The seam keeps stable pdd-owned file paths for anything pdd writes into a user's files or passes to a child process:

- `src/try-doors.mjs` re-exports `runShim` from `./runtime-seam.mjs` so `.pdd/try/bin/<program>` launchers keep a stable pdd-owned module path across upgrades and package extraction.
- `runTry(input, ports)` in `src/runtime-seam.mjs` defaults `ports.tryLauncherUrl` to the `file:` URL of `src/try-doors.mjs` before delegating to `src/runtime/index.mjs`, preserving an explicit `ports.tryLauncherUrl` when provided.

## Request metadata and host ports

Because `src/runtime/` imports nothing outside `src/runtime/`, `src/runtime-seam.mjs` builds caller request metadata and host ports lazily on invocation (preserving explicit caller overrides):

- `runJobs(input, ports)`: supplies `client.commands` (`{ test, lint, simulate }`) from `src/command-catalog.mjs` (`NAMES`).
- `buildCheckPlan(input, ports)`: supplies `ports.headerPrompts` from `src/file-owner.mjs`.
- `runCheck(input, ports)`: supplies `client.version` from `package.json`, `ports.workflowBaseSha` from `src/workflow-runs.mjs` (`allRuns`), `ports.headerPrompts` from `src/file-owner.mjs`, `ports.rememberSecrets` from `src/secret-redaction.mjs`, `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`), `ports.allRuns`, `ports.assessNativeEvidence`, `ports.usableResult`, and `ports.resultLines` from `src/workflow-runs.mjs` and `src/workflow-results.mjs` (when `--lint` is set), `ports.lintSvgLayouts` from `src/svg-layout.mjs` (when `--lint` is set), and `ports.compareScreen` and `ports.formatScreenComparison` from `src/screen-compare.mjs` (when `--screen` or `--drawing` is set).
- `runTry(input, ports)`: supplies `ports.tryLauncherUrl`, `ports.rememberSecrets` from `src/secret-redaction.mjs`, `ports.loadAgentDefinitions` from `src/agent-config.mjs`, `ports.discoverAgents` and `ports.askAgent` from `src/agent-adapters.mjs`, `ports.evidenceEligibility` from `src/workflow-runner.mjs`, and `ports.askApproval`, `ports.lineReader`, and `ports.promptPath` from `src/prompt-approve.mjs`.
- `createAgentBridge(context, test, tryId, options, link)`: supplies default `loadAgentDefinitions`, `discoverAgents`, `askAgent`, and `guidePorts.evidenceEligibility` without cloning `context`.
- `runShim(descriptorPath, argv, ports)`: supplies `ports.lineReader` from `src/prompt-approve.mjs` for `--save-last` interactive editor handoff.
- `runContracts(input, ports)`: supplies `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`).
- `migrateRuntimeWorkspace(input, ports)`: supplies `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`).
- `runAutomaticApproval(input, ports)`: supplies `readApprovalPolicy`, `approvalActor`, `readPromptApprovals`, and `recordPromptApproval` from `src/approval-policy.mjs`, `approvePromptText` and `promptPath` from `src/prompt-approve.mjs`, and seam check ports (`client`, `headerPrompts`, `workflowBaseSha`, `rememberSecrets`, `evidenceEligibility`, `lintSvgLayouts`).
- `checkRuntimeHealth(input, ports)` and `loadRuntimeClient()`: supply `ports.rememberSecrets` from `src/secret-redaction.mjs`.

## Public contract

Expose every public binding of [`src/runtime/index.mjs`](runtime-entry.prompt.md), preserving lazy loading, synchronous vs async signatures, parameter handling, return values, thrown errors, and port forwarding:

- `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `loadRuntimeClient`, `runCheck`, `runTry`
- `LIMITS`, `captureSource`, `checkInput`, `findTests`, `gitFiles`, `interfaceBlocks`, `interfaceSchemaProblems`, `isSecretPath`, `isStoryPath`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `sha256`, `sourceFilePort`
- `PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`, `causeText`, `cleanText`, `storyLines`
- `outcomeText`, `resultOutcome`
- `buildCheckPlan`, `checkPlanResultLines`, `checkPlanResults`
- `allowsRuntimePath`, `loadRuntimeWorkspace`, `requireRuntimePath`
- `exactIntegerLeaves`, `jsonSafe`, `parseScenarioJson`, `stringifyScenarioJson`, `withExactIntegers`
- `loadInterfaceDraft`, `runAutomaticApproval`, `runInterfaceDraft`
- `createAgentBridge`
- `migrateRuntimeWorkspace`
- `runContracts`
- `runJobs`
- `runMcp`
- `runShim`
- `buildAgentInput`

The seam holds no mutable request state and loads zero additional pdd modules at startup beyond the static leaf exports of `src/runtime/index.mjs`; port providers and command modules load only when invoked. Both static imports and dynamic `import('./runtime-seam.mjs')` callers receive the same namespace.

## Dependencies

- [Runtime package entry](runtime-entry.prompt.md): required generation context for the exported Runtime package bindings and their contracts.
- [Command catalog](command-catalog.prompt.md): required generation context for `NAMES` (`client.commands`).
- [File owner lookup](file-owner.prompt.md): required generation context for `headerPrompts`.
- [Shared secret redaction](secret-redaction.prompt.md): required generation context for `rememberSecrets`.
- [Agent configuration](agent-config.prompt.md) and [Agent adapters](agent-adapters.prompt.md): required generation context for `loadAgentDefinitions`, `discoverAgents`, and `askAgent`.
- [Prompt approval](prompt-approve.prompt.md) and [Approval policy](approval-policy.prompt.md): required generation context for Try and automatic-approval ports.
- [Workflow runner](workflow-runner.prompt.md), [Workflow runs](workflow-runs.prompt.md), and [Workflow results](workflow-results.prompt.md): required generation context for evidence eligibility, workflow base SHA, and native Story lint assessment ports.
- [SVG layout lint](svg-layout.prompt.md) and [Screen comparison](screen-compare.prompt.md): required generation context for local drawing check ports.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256":"c28ce9ef9cfde5815465611c16a259b6fba11443c2a0913f579f5b249b107010","reason":"Re-exports live JavaScript ESM module bindings from src/runtime/index.mjs as pdd's sole import seam, which bound Runtime ports cannot fake."}
```
</details>
