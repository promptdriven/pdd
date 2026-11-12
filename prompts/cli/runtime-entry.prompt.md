# Runtime package entry

Own `src/runtime/index.mjs`. It is the single public entry of `src/runtime/`, exposing the Runtime commands, local format and workspace readers, check-plan, product-composition, and outcome helpers, agent bridge and workspace migration entries, constants, and agent packet builder consumed by pdd through [`src/runtime-seam.mjs`](runtime-seam.prompt.md).

No module under `src/runtime/` may import or address any relative path outside `src/runtime/`. Caller metadata (`client.version`, `client.commands`, `workflow.base_sha`) and host-owned capabilities (file-owner headers, approvals, local agent launchers, workflow evidence eligibility, native Story assessment, product Markdown document and world-writer parsers, SVG layout advisory, and screen comparison) arrive exclusively through request fields and `ports`. Direct `src/runtime/` functions require their host ports (failing with a descriptive unbound-port error when a required host capability is omitted); [`src/runtime-seam.mjs`](runtime-seam.prompt.md) is the compatible entry for pdd code and tests, supplying every host port with pdd's behavior.

## Public contract

Keep module loading faithful to callers: load zero `src/runtime/` submodules eagerly when `src/runtime/index.mjs` itself evaluates, expose scoped synchronous slice loaders so each static caller evaluates only the exact leaf or client slice it previously imported, and defer every individual function export until first call so light CLI commands and standalone leaf callers never load unrelated leaves or heavy Runtime modules and command load failures surface inside their callers' `try/catch` guards.

### Pure constants and scoped slice loaders

Expose these pure constants directly without loading any submodule (identical to their owner modules):

- `LIMITS`: frozen `{ bytes: 10_485_760, files: 10_000 }` (`src/runtime/runtime-preflight.mjs`).
- `TEST_SCHEMA`: `'prompt-runtime.program-scenario.v1'` (`src/runtime/runtime-preflight.mjs`).
- `DRAFT_SERVER_TEXT`: `'The server does not run draft prompts yet. Approve the prompt first, or wait for the server update.'` (`src/runtime/runtime-preflight.mjs`).
- `STALE_HINT`: `'the text changed after approval: set status to draft, run pdd test --fill-hash, ask the person'` (`src/runtime/runtime-preflight.mjs`), and `staleHint`: `` `pdd: ${STALE_HINT}.` ``.
- `PROVIDER_TEXT`: `'the AI provider failed during the run. It is not a failed check. Do not send it again yet.'` (`src/runtime/runtime-outcome.mjs`).
- `CHECK_STATES`: frozen `['waiting', 'sent', 'passed', 'failed', 'refused', 'partial', 'not run']` (`src/runtime/runtime-outcome.mjs`).
- `OPEN_STATES`: `new Set(['queued', 'running', 'sent'])` (`src/runtime/runtime-output.mjs`).

PDD file-name test selection (`isStoryPath`, `hasAcceptance`, `expectedTestPath`, `matchTests`, `orphanSummary`, `selectTests`, `whyNoTests`, `NO_TESTS`), PDD state-to-exit mapping (`STATE_EXIT_CODES`, `COMMAND_EXIT_CODE`, `exitFor`, `outcomeExitCode`, `exitCodeFor`), and PDD PR paste-line words (`PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`) live outside `src/runtime/` in [`src/test-selection.mjs`](test-selection.prompt.md), [`src/runtime-exit.mjs`](runtime-exit.prompt.md), and [`src/prompt-tests-words.mjs`](prompt-tests-words.prompt.md); `src/runtime/` functions receive them as ports.

Expose these synchronous slice loaders (each loading and caching only its target owner module via `createRequire(import.meta.url)` on first call):

| Slice loader | Target owner module |
|---|---|
| `runtimeScenarioJsonSlice()` | `src/runtime/scenario-json.mjs` |
| `runtimeWorkspaceSlice()` | `src/runtime/runtime-workspace.mjs` |
| `runtimeOutcomeSlice()` | `src/runtime/runtime-outcome.mjs` |
| `runtimeOutputSlice()` | `src/runtime/runtime-output.mjs` |
| `runtimePreflightSlice()` | `src/runtime/runtime-preflight.mjs` |
| `runtimeAgentPacketSlice()` | `src/runtime/agent-packet.mjs` |
| `runtimeCheckPlanSlice()` | `src/runtime/runtime-check-plan.mjs` |
| `runtimeClientSlice()` | `src/runtime/runtime-client.mjs` |

### Leaf and command exports

Load each owner module only when the exported function (or its slice loader) is called, preserving argument forwarding, return values, thrown errors, and port behavior:

| Owner module | Exported bindings | Loading rule |
|---|---|---|
| `src/runtime/scenario-json.mjs` | `exactIntegerLeaves`, `jsonSafe`, `parseScenarioJson`, `stringifyScenarioJson`, `withExactIntegers` | Load synchronously on first call via `runtimeScenarioJsonSlice()` |
| `src/runtime/runtime-workspace.mjs` | `allowsRuntimePath`, `loadRuntimeWorkspace`, `requireRuntimePath` | Load synchronously on first call via `runtimeWorkspaceSlice()` |
| `src/runtime/runtime-outcome.mjs` | `CHECK_STATES`, `PROVIDER_TEXT`, `hasProgress`, `outcomeDone`, `outcomeFor`, `outcomeOverall`, `outcomeText`, `progressText`, `resultOutcome`, `resultOverall` | Constants immediate; functions load synchronously on first call via `runtimeOutcomeSlice()` |
| `src/runtime/runtime-output.mjs` | `OPEN_STATES`, `PROVIDER_TEXT`, `causeText`, `cleanText`, `coverageText`, `jsonRow`, `progressTicker`, `projectAnswer`, `refusalView`, `renderJson`, `renderText`, `sinceText`, `stepTimeLimit`, `storyLines`, `summaryLine`, `tryUsage`, `tryUsageHeaders`, `tryUsageLine`, `validLink` | Constants immediate; functions load synchronously on first call via `runtimeOutputSlice()` |
| `src/runtime/runtime-preflight.mjs` | `DRAFT_SERVER_TEXT`, `LIMITS`, `PreflightError`, `STALE_HINT`, `TEST_SCHEMA`, `captureSource`, `checkInput`, `createStrictSourceAccess`, `defaultMaxCalls`, `discoveryRefusal`, `discoveryVisibleFiles`, `executableInterfaceText`, `fillHashes`, `findTests`, `formatSize`, `formatWarningLines`, `gitFiles`, `hasPromptInterface`, `interfaceBlocks`, `interfaceFormatWarnings`, `interfaceKindProblems`, `interfaceSchemaProblems`, `isSecretPath`, `numberWarnings`, `otherFiles`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `scenarioShapeRefusal`, `schemaKeywordWarningLines`, `sha256`, `sharedSourceFiles`, `sourceFilePort`, `staleHint`, `storyCriteria`, `tarFiles` | Constants immediate; `PreflightError` forwards constructor and `Symbol.hasInstance` lazily; functions load synchronously on first call via `runtimePreflightSlice()` |
| `src/runtime/agent-packet.mjs` | `buildAgentInput` | Load synchronously on first call via `runtimeAgentPacketSlice()` |
| `src/runtime/runtime-check-plan.mjs` | `buildCheckPlan`, `checkPlanResultLines`, `checkPlanResults` | Load synchronously on first call via `runtimeCheckPlanSlice()` |
| `src/runtime/product-composition.mjs` | `composeProductTry`, `productTapCallBound`, `selectJourneys` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `src/runtime/agent-guide.mjs` | `createTryGuide` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `src/runtime/agent-project.mjs` | `buildProjectCard`, `readAgentScenarios` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `src/runtime/contracts.mjs` | `runContracts` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `src/runtime/runtime-slots.mjs` | `runJobs` | `await import('./runtime-slots.mjs')` when called |
| `src/runtime/interface-draft.mjs` | `loadInterfaceDraft`, `runAutomaticApproval`, `runInterfaceDraft` | `await import('./interface-draft.mjs')` when called (`loadInterfaceDraft` resolves to `{ contractCoverage, coverageView, missingInterfaces }`) |
| `src/runtime/agent-chat.mjs` | `createAgentBridge` | `await import('./agent-chat.mjs')` when called |
| `src/runtime/runtime-workspace-migration.mjs` | `migrateRuntimeWorkspace` | `await import('./runtime-workspace-migration.mjs')` when called |
| `src/runtime/try-mcp.mjs` | `createTryTools`, `runMcp` | `createTryTools` loads synchronously on first call via `createRequire(import.meta.url)`; `runMcp` uses `await import('./try-mcp.mjs')` |
| `src/runtime/try-doors.mjs` | `openCli`, `runShim`, `saveLast` | `await import('./try-doors.mjs')` when called |
| `src/runtime/try-http.mjs` | `openServe` | `await import('./try-http.mjs')` when called |
| `src/runtime/runtime-client.mjs` | `acquireCaseWriteOwnership`, `acquireRuntimeBatchLock`, `applyPendingCase`, `applyPendingCaseWithHandoff`, `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `defaultLineReader`, `loadRuntimeClient`, `readContractHistory`, `readTryOwner`, `runCheck`, `runDoorCall`, `runTry`, `runtimeOrigin`, `runtimeWorkspaceMigrationStore`, `saveDoorCase`, `saveDoorCaseResult`, `savedStoryEvidence` | Synchronous helpers (`createSavedStoryEvidenceReader`, `defaultLineReader`, `readContractHistory`, `runtimeOrigin`, `runtimeWorkspaceMigrationStore`, `saveDoorCase`, `saveDoorCaseResult`) load on first call via `runtimeClientSlice()`; async entries use `await import('./runtime-client.mjs')` (`loadRuntimeClient` resolves to `{ DEFAULT_RUNTIME_URL, checkRuntimeHealth, runtimeOrigin }`, keeping `DEFAULT_RUNTIME_URL` defined in `src/runtime/runtime-client.mjs` alone) |

`runTry(input, ports)` forwards `ports.tryLauncherUrl` to `openCli` when supplied so the host CLI can pin a stable launcher module URL outside `src/runtime/`; when omitted, `openCli` falls back to `src/runtime/try-doors.mjs`.

## Dependencies

- [Exact scenario numbers](scenario-json.prompt.md): required generation context for `exactIntegerLeaves`, `jsonSafe`, `parseScenarioJson`, `stringifyScenarioJson`, and `withExactIntegers`.
- [Runtime workspace boundary](runtime-workspace.prompt.md): required generation context for `allowsRuntimePath`, `loadRuntimeWorkspace`, and `requireRuntimePath`.
- [Runtime outcome](runtime-outcome.prompt.md): required generation context for `CHECK_STATES`, `PROVIDER_TEXT`, `hasProgress`, `outcomeDone`, `outcomeFor`, `outcomeOverall`, `outcomeText`, `progressText`, `resultOutcome`, and `resultOverall`.
- [Runtime output](runtime-output.prompt.md): required generation context for `OPEN_STATES`, `causeText`, `cleanText`, `coverageText`, `jsonRow`, `progressTicker`, `projectAnswer`, `refusalView`, `renderJson`, `renderText`, `sinceText`, `stepTimeLimit`, `storyLines`, `summaryLine`, `tryUsage`, `tryUsageHeaders`, `tryUsageLine`, and `validLink`.
- [Runtime preflight](runtime-preflight.prompt.md): required generation context for `DRAFT_SERVER_TEXT`, `LIMITS`, `PreflightError`, `STALE_HINT`, `TEST_SCHEMA`, `captureSource`, `checkInput`, `createStrictSourceAccess`, `defaultMaxCalls`, `discoveryRefusal`, `discoveryVisibleFiles`, `executableInterfaceText`, `fillHashes`, `findTests`, `formatSize`, `formatWarningLines`, `gitFiles`, `hasPromptInterface`, `interfaceBlocks`, `interfaceFormatWarnings`, `interfaceKindProblems`, `interfaceSchemaProblems`, `isSecretPath`, `numberWarnings`, `otherFiles`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `scenarioShapeRefusal`, `schemaKeywordWarningLines`, `sha256`, `sharedSourceFiles`, `sourceFilePort`, `staleHint`, `storyCriteria`, and `tarFiles`.
- [Agent packet](agent-packet.prompt.md): required generation context for `buildAgentInput`.
- [Runtime check plan](runtime-check-plan.prompt.md): required generation context for `buildCheckPlan`, `checkPlanResultLines`, and `checkPlanResults`.
- [Product Simulator composition](product-composition.prompt.md): required generation context for `composeProductTry`, `productTapCallBound`, and `selectJourneys`.
- [Runtime slots](runtime-slots.prompt.md): required generation context for `runJobs`.
- [Shared contracts](contracts.prompt.md): required generation context for `runContracts`.
- [Interface drafting](interface-draft.prompt.md): required generation context for `contractCoverage`, `coverageView`, `missingInterfaces`, `runAutomaticApproval`, and `runInterfaceDraft`.
- [Agent chat](agent-chat.prompt.md), [Try guide](agent-guide.prompt.md), and [Project facts](agent-project.prompt.md): required generation context for `buildProjectCard`, `createAgentBridge`, `createTryGuide`, and `readAgentScenarios`.
- [Workspace migration](runtime-workspace-migration.prompt.md): required generation context for `migrateRuntimeWorkspace`.
- [Try MCP server](try-mcp.prompt.md): required generation context for `createTryTools` and `runMcp`.
- [Try doors](try-doors.prompt.md) and [Try HTTP server](try-http.prompt.md): required generation context for `openCli`, `openServe`, `runShim`, `saveLast`, and `tryLauncherUrl` forwarding.
- [Runtime client](runtime-client.prompt.md): required generation context for `DEFAULT_RUNTIME_URL`, `acquireCaseWriteOwnership`, `acquireRuntimeBatchLock`, `applyPendingCase`, `applyPendingCaseWithHandoff`, `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `defaultLineReader`, `readContractHistory`, `readTryOwner`, `runCheck`, `runDoorCall`, `runTry`, `runtimeOrigin`, `runtimeWorkspaceMigrationStore`, `saveDoorCase`, `saveDoorCaseResult`, and `savedStoryEvidence`.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256": "b8ac5b3e00534fae6105df5d39463534093747c9ec0dc4767114a44f7b67dd2b","reason":"Exposes live JavaScript ESM static and deferred dynamic-import bindings across src/runtime/ submodules, which bound Runtime ports cannot fake."}
```
</details>
