# PDD to Runtime seam

Own `src/runtime-seam.mjs` and the stable launcher entry `src/try-doors.mjs`. `src/runtime-seam.mjs` is the sole module in pdd outside `src/runtime/` permitted to import `src/runtime/`. Every pdd module in `src/`, `bin/`, and `scripts/` accesses Runtime commands, local format and workspace readers, check-plan and outcome helpers, and constants exclusively through `./runtime-seam.mjs`.

The seam keeps stable pdd-owned file paths for anything pdd writes into a user's files or passes to a child process:

- `src/try-doors.mjs` re-exports `runShim` from `./runtime-seam.mjs` so `.pdd/try/bin/<program>` launchers keep a stable pdd-owned module path across upgrades and package extraction.
- `runTry(input, ports)` in `src/runtime-seam.mjs` defaults `ports.tryLauncherUrl` to the `file:` URL of `src/try-doors.mjs` before delegating to `src/runtime/index.mjs`, preserving an explicit `ports.tryLauncherUrl` when provided.

## Request metadata and host ports

Because `src/runtime/` imports nothing outside `src/runtime/`, `src/runtime-seam.mjs` builds caller request metadata and host ports lazily on invocation (preserving explicit caller overrides), including a single shared host `redaction` port (`{ remember, redact, known }`) backed by `src/secret-redaction.mjs` so host and Runtime redaction never diverge:

- `runJobs(input, ports)`: supplies `client.commands` (`{ test, lint, simulate }`) from `src/command-catalog.mjs` (`NAMES`).
- `buildCheckPlan(input, ports)`: supplies `ports.headerPrompts` from `src/file-owner.mjs`.
- `composeProductTry(input, ports)`: supplies `ports.parseProductDocuments` and `ports.parseProductWorldWriters` from `src/product.mjs`.
- `createTryGuide(options)`: supplies `ports.redaction` from `src/secret-redaction.mjs` and `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`).
- `runCheck(input, ports)`: supplies `client.version` from `package.json`, `ports.workflowBaseSha` from `src/workflow-runs.mjs` (`allRuns`), `ports.headerPrompts` from `src/file-owner.mjs`, `ports.redaction` from `src/secret-redaction.mjs`, `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`), `ports.allRuns`, `ports.assessNativeEvidence`, `ports.usableResult`, and `ports.resultLines` from `src/workflow-runs.mjs` and `src/workflow-results.mjs` (when `--lint` is set), `ports.lintSvgLayouts` from `src/svg-layout.mjs` (when `--lint` is set), and `ports.compareScreen` and `ports.formatScreenComparison` from `src/screen-compare.mjs` (when `--screen` or `--drawing` is set).
- `runTry(input, ports)`: supplies `ports.tryLauncherUrl`, `ports.redaction` from `src/secret-redaction.mjs`, `ports.loadAgentDefinitions` from `src/agent-config.mjs`, `ports.discoverAgents` and `ports.askAgent` from `src/agent-adapters.mjs`, `ports.evidenceEligibility` from `src/workflow-runner.mjs`, `ports.parseProductDocuments` and `ports.parseProductWorldWriters` from `src/product.mjs`, and `ports.askApproval`, `ports.lineReader`, and `ports.promptPath` from `src/prompt-approve.mjs`.
- `createAgentBridge(context, test, tryId, options, link, seamPorts)`: supplies default `redaction`, `loadAgentDefinitions`, `discoverAgents`, `askAgent`, and `guidePorts.evidenceEligibility` without cloning `context`.
- `readTryOwner(input, ports)` and `runMcp(input, ports)`: supply `ports.tryLauncherUrl`, `ports.redaction` from `src/secret-redaction.mjs`, `ports.evidenceEligibility` from `src/workflow-runner.mjs`, and `ports.parseProductDocuments` and `ports.parseProductWorldWriters` from `src/product.mjs` so MCP owner tools and Try reopening support whole-product simulations.
- `runShim(descriptorPath, argv, ports)`: supplies `ports.redaction` from `src/secret-redaction.mjs` and `ports.lineReader` from `src/prompt-approve.mjs` for `--save-last` interactive editor handoff.
- `runContracts(input, ports)`: supplies `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`).
- `migrateRuntimeWorkspace(input, ports)`: supplies `ports.evidenceEligibility` from `src/workflow-runner.mjs` (`readEvidenceEligibility`).
- `runAutomaticApproval(input, ports)`: supplies `readApprovalPolicy`, `approvalActor`, `readPromptApprovals`, and `recordPromptApproval` from `src/approval-policy.mjs`, `approvePromptText` and `promptPath` from `src/prompt-approve.mjs`, and seam check ports (`client`, `headerPrompts`, `workflowBaseSha`, `redaction`, `evidenceEligibility`, `lintSvgLayouts`).
- `checkRuntimeHealth(input, ports)` and `loadRuntimeClient()`: supply `ports.redaction` from `src/secret-redaction.mjs`.

## Public contract

Expose every public binding of [`src/runtime/index.mjs`](runtime-entry.prompt.md), preserving lazy loading, synchronous vs async signatures, parameter handling, return values, thrown errors, and port forwarding:

- `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `loadRuntimeClient`, `readTryOwner`, `runCheck`, `runTry`
- `LIMITS`, `captureSource`, `checkInput`, `findTests`, `gitFiles`, `interfaceBlocks`, `interfaceSchemaProblems`, `isSecretPath`, `isStoryPath`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `sha256`, `sourceFilePort`
- `PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`, `causeText`, `cleanText`, `storyLines`
- `outcomeText`, `resultOutcome`
- `buildCheckPlan`, `checkPlanResultLines`, `checkPlanResults`
- `composeProductTry`, `productTapCallBound`, `selectJourneys`
- `allowsRuntimePath`, `loadRuntimeWorkspace`, `requireRuntimePath`
- `exactIntegerLeaves`, `jsonSafe`, `parseScenarioJson`, `stringifyScenarioJson`, `withExactIntegers`
- `loadInterfaceDraft`, `runAutomaticApproval`, `runInterfaceDraft`
- `createAgentBridge`, `createTryGuide`
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
- [Shared secret redaction](secret-redaction.prompt.md): required generation context for the shared host `redaction` port (`remember`, `redact`, `known`).
- [Agent configuration](agent-config.prompt.md) and [Agent adapters](agent-adapters.prompt.md): required generation context for `loadAgentDefinitions`, `discoverAgents`, and `askAgent`.
- [Prompt approval](prompt-approve.prompt.md) and [Approval policy](approval-policy.prompt.md): required generation context for Try and automatic-approval ports.
- [Workflow runner](workflow-runner.prompt.md), [Workflow runs](workflow-runs.prompt.md), and [Workflow results](workflow-results.prompt.md): required generation context for evidence eligibility, workflow base SHA, and native Story lint assessment ports.
- [Product workflow](product.prompt.md): required generation context for `parseProductDocuments` and `parseProductWorldWriters` ports.
- [SVG layout lint](svg-layout.prompt.md) and [Screen comparison](screen-compare.prompt.md): required generation context for local drawing check ports.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256": "afcfb0e4cb3c85b11d553ec0f6ae645774e42a61383f57172b8dbc8ae6f1517c","reason":"Re-exports live JavaScript ESM module bindings from src/runtime/index.mjs as pdd's sole import seam, which bound Runtime ports cannot fake."}
```
</details>
