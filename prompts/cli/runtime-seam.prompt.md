# PDD to Runtime seam

Own `src/runtime-seam.mjs` and the stable launcher entry `src/try-doors.mjs`. `src/runtime-seam.mjs` is the sole module in pdd outside `src/runtime/` permitted to import `src/runtime/`. Every pdd module in `src/`, `bin/`, and `scripts/` accesses Runtime commands, local format and workspace readers, check-plan and outcome helpers, and constants exclusively through `./runtime-seam.mjs`.

The seam keeps stable pdd-owned file paths for anything pdd writes into a user's files or passes to a child process:

- `src/try-doors.mjs` re-exports `runShim` from `./runtime-seam.mjs` so `.pdd/try/bin/<program>` launchers keep a stable pdd-owned module path across upgrades and package extraction.
- `runTry(input, ports)` in `src/runtime-seam.mjs` defaults `ports.tryLauncherUrl` to the `file:` URL of `src/try-doors.mjs` before delegating to `src/runtime/index.mjs`, preserving an explicit `ports.tryLauncherUrl` when provided.

## Request metadata and host ports

Because `src/runtime/` imports nothing outside `src/runtime/`, `src/runtime-seam.mjs` builds caller request metadata and host ports lazily on invocation. Legacy and canonical port spellings (`readEvidenceEligibility` and `evidenceEligibility`; `rememberSecrets` / `redactSecrets` and `redaction`; `agents.{loadDefinitions,list,ask}` and `{loadAgentDefinitions,discoverAgents,askAgent}`) are normalized before installing seam defaults so an explicit caller override under either name wins, and every seam default uses nullish fallback (`??`) so an own `undefined` property never erases a default. A single shared host `redaction` port (`{ remember, redact, known }`) backed by `src/secret-redaction.mjs` keeps host and Runtime redaction on one registry:

- `runJobs(input, ports)`: loads the host client companion graph (`src/product.mjs` and `src/command-catalog.mjs`) inside the guarded call and supplies `client.commands` (`{ test, lint, simulate }`) from `src/command-catalog.mjs` (`NAMES`).
- `buildCheckPlan(input, ports)`: supplies `ports.headerPrompts` from `src/file-owner.mjs`.
- `composeProductTry(input, ports)`: supplies `ports.parseProductDocuments` and `ports.parseProductWorldWriters` from `src/product.mjs`.
- `createTryGuide(options)`: supplies `ports.redaction` from `src/secret-redaction.mjs` and `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`).
- `buildProjectCard(input)`: supplies `evidenceEligibility` (`readEvidenceEligibility`) from `src/workflow-runner.mjs` when omitted.
- `runCheck(input, ports)`: loads all check port-provider and host companion modules (`src/secret-redaction.mjs`, `src/file-owner.mjs`, `src/workflow-runner.mjs`, `src/workflow-runs.mjs`, `src/workflow-results.mjs`, `src/svg-layout.mjs`, `src/screen-compare.mjs`, `src/product.mjs`) unconditionally when invoked and supplies on every call: `client.version` from `package.json` when omitted (direct `src/runtime/` callers without `client.version` or `ports.clientVersion` get `null`, never a hardcoded literal), a lazy `ports.workflowBaseSha({ root, env })` callback backed by `ports.allRuns` / `src/workflow-runs.mjs` (`allRuns`) evaluated inside `runBatch` at check-plan time (preserving an explicit `input.workflow` only when supplied by the caller), `ports.headerPrompts` from `src/file-owner.mjs`, `ports.redaction` from `src/secret-redaction.mjs`, `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`), `ports.allRuns`, `ports.assessNativeEvidence`, `ports.usableResult`, and `ports.resultLines` from `src/workflow-runs.mjs` and `src/workflow-results.mjs`, `ports.lintSvgLayouts` from `src/svg-layout.mjs`, and `ports.compareScreen` and `ports.formatScreenComparison` from `src/screen-compare.mjs`.
- `runTry(input, ports)`: supplies `ports.tryLauncherUrl`, `ports.redaction` from `src/secret-redaction.mjs`, `ports.loadAgentDefinitions` from `src/agent-config.mjs`, `ports.discoverAgents` and `ports.askAgent` from `src/agent-adapters.mjs`, `ports.evidenceEligibility` from `src/workflow-runner.mjs`, `ports.parseProductDocuments` and `ports.parseProductWorldWriters` from `src/product.mjs`, and `ports.askApproval`, `ports.lineReader`, and `ports.promptPath` from `src/prompt-approve.mjs`.
- `createAgentBridge(context, test, tryId, options, link, seamPorts)`: supplies default `redaction`, `loadAgentDefinitions`, `discoverAgents`, `askAgent`, and `guidePorts.evidenceEligibility` without cloning `context`.
- `readTryOwner(input, ports)`, `createTryTools(input, ports)`, and `runMcp(input, ports)`: supply `ports.tryLauncherUrl`, `ports.redaction` from `src/secret-redaction.mjs`, `ports.evidenceEligibility` from `src/workflow-runner.mjs`, and `ports.parseProductDocuments` and `ports.parseProductWorldWriters` from `src/product.mjs` so MCP owner tools and Try reopening support whole-product simulations.
- `openCli(context, test, sessionId, options)`, `runShim(descriptorPath, argv, ports)`, `saveLast(input)`, and `runDoorCall(descriptor, input, ports)`: `openCli` supplies `context.ports.tryLauncherUrl` when `context.ports` is present; `runShim` loads the host client companion graph (`src/product.mjs`, `src/secret-redaction.mjs`, `src/prompt-approve.mjs`) and supplies `ports.redaction` and `ports.lineReader`; `saveLast` supplies `ports.lineReader` when `ports` is present; `runDoorCall` supplies `ports.redaction`.
- `readContractHistory(input, ports)` and `runContracts(input, ports)`: supply `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`); `runContracts` also loads `src/product.mjs` and `runtimeClientSlice()` inside the guarded call so `pdd contracts` preserves its client companion module set and load-failure handling.
- `migrateRuntimeWorkspace(input, ports)`: supplies `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`).
- `runAutomaticApproval(input, ports)`: supplies `readApprovalPolicy`, `approvalActor`, `readPromptApprovals`, and `recordPromptApproval` from `src/approval-policy.mjs`, `approvePromptText` and `promptPath` from `src/prompt-approve.mjs`, and seam check ports (`client`, `headerPrompts`, lazy `workflowBaseSha`, `allRuns`, `redaction`, `evidenceEligibility`, `lintSvgLayouts`), preserving an explicit `workflow` only when supplied by the caller.
- `checkRuntimeHealth(input, ports)`, `loadRuntimeClient()`, `runtimeOrigin(env)`, and `runtimeClientSlice()`: `checkRuntimeHealth` and `loadRuntimeClient` supply `ports.redaction` from `src/secret-redaction.mjs`; `runtimeOrigin` delegates synchronously to `src/runtime/index.mjs`; `runtimeClientSlice()` loads `src/runtime/runtime-client.mjs` synchronously via `src/runtime/index.mjs` and returns `{ ...clientModule, checkRuntimeHealth, createSavedStoryEvidenceReader, runtimeOrigin }` without importing host modules from the seam at module-evaluation time.

## Public contract

Expose every public binding and scoped slice loader of [`src/runtime/index.mjs`](runtime-entry.prompt.md), preserving caller-scoped module evaluation, synchronous vs async signatures, parameter handling, return values, thrown errors, and port forwarding:

- `acquireCaseWriteOwnership`, `acquireRuntimeBatchLock`, `applyPendingCase`, `applyPendingCaseWithHandoff`, `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `loadRuntimeClient`, `readContractHistory`, `readTryOwner`, `runCheck`, `runDoorCall`, `runTry`, `runtimeOrigin`, `runtimeWorkspaceMigrationStore`, `saveDoorCase`, `saveDoorCaseResult`, `savedStoryEvidence`
- `runtimeAgentPacketSlice`, `runtimeCheckPlanSlice`, `runtimeClientSlice`, `runtimeOutcomeSlice`, `runtimeOutputSlice`, `runtimePreflightSlice`, `runtimeScenarioJsonSlice`, `runtimeWorkspaceSlice`
- `LIMITS`, `captureSource`, `checkInput`, `findTests`, `gitFiles`, `interfaceBlocks`, `interfaceSchemaProblems`, `isSecretPath`, `isStoryPath`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `sha256`, `sourceFilePort`
- `PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`, `causeText`, `cleanText`, `storyLines`
- `outcomeText`, `resultOutcome`
- `buildCheckPlan`, `checkPlanResultLines`, `checkPlanResults`
- `composeProductTry`, `productTapCallBound`, `selectJourneys`
- `allowsRuntimePath`, `loadRuntimeWorkspace`, `requireRuntimePath`
- `exactIntegerLeaves`, `jsonSafe`, `parseScenarioJson`, `stringifyScenarioJson`, `withExactIntegers`
- `loadInterfaceDraft`, `runAutomaticApproval`, `runInterfaceDraft`
- `buildProjectCard`, `createAgentBridge`, `createTryGuide`, `readAgentScenarios`
- `migrateRuntimeWorkspace`
- `runContracts`
- `runJobs`
- `createTryTools`, `runMcp`
- `openCli`, `runShim`, `saveLast`
- `buildAgentInput`

The seam holds no mutable request state and loads zero additional pdd or Runtime modules when `src/runtime-seam.mjs` itself evaluates; each caller loads only its requested slice or command graph. Both static imports and dynamic `import('./runtime-seam.mjs')` callers receive the same namespace.

## Dependencies

- [Runtime package entry](runtime-entry.prompt.md): required generation context for the exported Runtime package bindings and their contracts.
- [Command catalog](command-catalog.prompt.md): required generation context for `NAMES` (`client.commands`).
- [File owner lookup](file-owner.prompt.md): required generation context for `headerPrompts`.
- [Shared secret redaction](secret-redaction.prompt.md): required generation context for the shared host `redaction` port (`remember`, `redact`, `known`).
- [Agent configuration](agent-config.prompt.md) and [Agent adapters](agent-adapters.prompt.md): required generation context for `loadAgentDefinitions`, `discoverAgents`, and `askAgent`.
- [Prompt approval](prompt-approve.prompt.md) and [Approval policy](approval-policy.prompt.md): required generation context for Try and automatic-approval ports.
- [Workflow runner](workflow-runner.prompt.md), [Workflow runs](workflow-runs.prompt.md), and [Workflow results](workflow-results.prompt.md): required generation context for evidence eligibility, workflow base SHA, and native Story lint assessment ports.
- [Product workflow](product.prompt.md): required generation context for `parseProductDocuments` and `parseProductWorldWriters` ports.
- [SVG layout lint](svg-layout.prompt.md) and [Screen comparison](screen-compare.prompt.md): required generation context for local drawing check ports.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256": "7013093c0f9fa2095d66e9c81ea224a9c2bac540688c4cccb0e68470c6ff6ca6","reason":"Re-exports live JavaScript ESM module bindings from src/runtime/index.mjs as pdd's sole import seam, which bound Runtime ports cannot fake."}
```
</details>
