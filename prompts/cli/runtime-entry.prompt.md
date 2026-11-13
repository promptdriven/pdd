# Runtime package entry

Own `src/runtime/index.mjs`. It is the single public entry of `src/runtime/`, exposing the Runtime package contract (`lint`, `check`, `read`, `retry`, `simulate`, `jobs`, `health`, `mcp`, `local`, `draftInterfaces`, `contracts`, `exactValue`, `format`, `source`, `saved`, `workspace`, `render`, `causeText`, `cleanText`, `version`) together with the compatibility helpers, slice loaders, and constants consumed by host callers and compatibility seams.

No module under `src/runtime/` may import or address any relative path outside `src/runtime/`, and `src/runtime/index.mjs` itself has zero static `src/runtime/` submodule imports (importing only Node built-ins). Caller metadata (`client.version`, `client.commands`, `workflow.base_sha`) and host-owned capabilities (file-owner headers, approvals, local agent launchers, workflow evidence eligibility, native Story assessment, product Markdown document and world-writer parsers, SVG layout advisory, and screen comparison) arrive exclusively through request fields and `ports`. Direct `src/runtime/` functions require their host ports (failing with a descriptive unbound-port error when a required host capability is omitted); host compatibility seams supply default host ports for CLI callers and tests.

## Public contract

Keep module loading faithful to callers: load zero `src/runtime/` submodules eagerly when `src/runtime/index.mjs` itself evaluates, expose scoped synchronous slice loaders so each static caller evaluates only the exact leaf or client slice it previously imported, and defer every command wrapper, reader method, and individual function export until first call so light CLI commands and standalone leaf callers never load unrelated leaves or heavy Runtime modules and command load failures surface inside their callers' `try/catch` guards.

### Package API commands and readers

Expose these thin wrappers over the underlying owner functions with zero behavior change (streaming command output through `ports.stdout` / `ports.stderr` and returning the underlying exit code or status payload):

- `check(input = {}, ports)`: maps `cwd = input.cwd ?? input.root` (when defined), `words` from `input.words` else string or `{ path, story }` entries in `input.tests`, `options = { ...(input.options ?? {}) }` (plus `'--affected': true` when `input.affected === true` and `options['--affected'] === undefined`), `cache = input.cache ?? true`, and optional `client` and `workflow` to `runCheck`.
- `lint(input = {}, ports)`: delegates to `runCheck` with the same `cwd`/`words`/`cache`/`client`/`workflow` mapping and `options = { ...(input.options ?? {}), '--lint': true }` (plus `'--local': true` when `input.local === true` and `options['--local'] === undefined`).
- `read(input = {}, ports)`: maps `target = input.call_id ?? input.batch`, `words` from `input.words` else `[String(target)]` when `target` is nonblank, `options = { ...(input.options ?? {}), '--read': true }`, `cache = input.cache ?? false`, and optional `cwd`, `client`, and `workflow` to `runCheck`.
- `retry(input = {}, ports)`: maps `words` from `input.words` else `[]`, `retryTarget = input.batch ?? input.options?.['--retry']`, `options = { ...(input.options ?? {}), ...(retryTarget !== undefined ? { '--retry': retryTarget } : {}) }`, `cache = input.cache ?? false`, and optional `cwd`, `client`, and `workflow` to `runCheck`.
- `local(input = {}, ports)`: requires `input.what` in `'files'`, `'fill-hash'`, or `'explain-bindings'` (throwing `RangeError` otherwise) and delegates to `runCheck` with the corresponding `--files`, `--fill-hash`, or `--explain-bindings` option (plus `'--compact': true` when `input.compact === true`) and `cache: false`.
- `simulate(input = {}, ports)`: validates optional `input.mode` in `'open'`, `'cli'`, `'serve'`, `'save-last'`, or `'stop'` (throwing `RangeError` otherwise), sets the matching `--cli`, `--serve` (`input.port ?? true` when unset), `--save-last`, or `--stop` option on `options`, derives `words` from `input.words`, `input.test` (string or `{ path, story }`), or `input.tests`, and delegates to `runTry` with optional `cwd = input.cwd ?? input.root`.
- `jobs(input = {}, ports)`: forwards `env = input.env ?? ports?.env` and `input` to `runJobs`.
- `health(input = {}, ports)`: forwards `env = input.env ?? ports?.env` and `input` to `checkRuntimeHealth`.
- `mcp(input = {}, ports)`: maps optional `cwd = input.cwd ?? input.root`, `words` from `input.words` else `input.story ? [input.story] : []`, and `env = input.env ?? ports?.env` to `runMcp`.
- `draftInterfaces(input = {}, ports)`: maps optional `cwd = input.cwd ?? input.root`, `words` from `input.words` else `input.paths ?? []`, `all: Boolean(input.all)`, `json: Boolean(input.json)`, `contract: input.contract`, `extend: Boolean(input.extend)`, and `refresh: Boolean(input.refresh)` to `runInterfaceDraft`.
- `contracts(input = {}, ports)`: synchronous wrapper mapping optional `cwd = input.cwd ?? input.root`, `words` from `input.words` else `input.sync ? ['sync'] : []`, and `options` (`input.options` merged with `'--write': input.write` when `input.write !== undefined` and `options['--write'] === undefined`) to `runContracts`.
- `format`: frozen reader group whose methods load `runtimeScenarioJsonSlice()` or `runtimePreflightSlice()` only when called:
  - `parseScenario(text)` -> `parseScenarioJson(text)`; `stringifyScenario(doc, space)` -> `stringifyScenarioJson(doc, space)`; `exactValue(value)` -> `exactValue(value)` (also exported at top level).
  - `isScenario(text)`: returns `true` iff `typeof text === 'string'` and `parseScenarioJson(text)` parses without throwing to a plain object with `schema_version === TEST_SCHEMA` (returns `false` otherwise).
  - `interfaceBlocks(text)`: maps preflight `interfaceBlocks(text)` matches to `{ raw, json, status, prose_sha256, start, end }`, where `json` is the parsed plain object (else `null`) and `status` / `prose_sha256` are string fields of `json` (else `null`).
  - `proseSha256(text)` -> preflight `proseSha256(text)`; `interfaceProblems(json)` -> `interfaceSchemaProblems(json)` (`[{ code, pointer, rule }]`); `storyCriteria(text)` -> `storyCriteria(text)` (`[string]`).
  - `setInterfaceStatus(text, { status, prose_sha256 } = {})`: replaces unique top-level string `"status"` (and `"prose_sha256"` when supplied) in place inside the single Runtime interface block while keeping every other byte unchanged; returns `null` when `text` or `status` is not a string, `prose_sha256` is defined and not a string, `blocks.length !== 1`, the block is not a valid JSON plain object, top-level `"status"` or `"prose_sha256"` is missing, non-string, or duplicated, `proseSha256(next) !== proseSha256(text)`, `interfaceBlocks(next).length !== 1`, or the parsed block does not deep-equal the updated object.
- `source`: frozen `{ identity({ root, tests, ...options } = {}, ports) }` normalizing string or `{ path, story }` `tests` entries and delegating to `captureSource`.
- `saved`: frozen `{ results(input = {}, ports) }` delegating to `savedStoryEvidence`.
- `workspace`: frozen `{ policy(input), allows(policy, path) }` delegating to `loadRuntimeWorkspace` and `allowsRuntimePath`.
- `render(result, { as = 'table' } = {}, ports)`: dispatches `'table'` -> `renderText(result, ports)`, `'json'` -> `renderJson(result, ports)`, `'story-lines'` -> `storyLines(Array.isArray(result) ? result : result?.rows ?? [], ports)`, and `'summary'` -> `summaryLine(Array.isArray(result) ? result : result?.rows ?? [], Array.isArray(result) ? null : result?.story ?? null, ports)`, throwing `RangeError` for any other `as`.
- `version()`: returns `{ package: '@promptdriven/runtime-client', api_version: 1, formats: { scenario: TEST_SCHEMA, app_map: 'prompt-runtime.app-map.v1' }, limits: { ...LIMITS }, engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15' }` synchronously from local constants with zero submodule loads and zero network calls.

### Pure constants and scoped slice loaders

Expose these pure constants directly without loading any submodule (identical to their owner modules):

- `LIMITS`: frozen `{ bytes: 10_485_760, files: 10_000 }` (`runtime-preflight.mjs`).
- `TEST_SCHEMA`: `'prompt-runtime.program-scenario.v1'` (`runtime-preflight.mjs`).
- `DRAFT_SERVER_TEXT`: `'The server does not run draft prompts yet. Approve the prompt first, or wait for the server update.'` (`runtime-preflight.mjs`).
- `STALE_HINT`: `'the text changed after approval: set status to draft, run pdd test --fill-hash, ask the person'` (`runtime-preflight.mjs`), and `staleHint`: `` `pdd: ${STALE_HINT}.` ``.
- `PROVIDER_TEXT`: `'the AI provider failed during the run. It is not a failed check. Do not send it again yet.'` (`runtime-outcome.mjs`).
- `CHECK_STATES`: frozen `['waiting', 'sent', 'passed', 'failed', 'refused', 'partial', 'not run']` (`runtime-outcome.mjs`).
- `OPEN_STATES`: `new Set(['queued', 'running', 'sent'])` (`runtime-output.mjs`).

PDD file-name test selection (`isStoryPath`, `hasAcceptance`, `expectedTestPath`, `matchTests`, `orphanSummary`, `selectTests`, `whyNoTests`, `NO_TESTS`), PDD state-to-exit mapping (`STATE_EXIT_CODES`, `COMMAND_EXIT_CODE`, `exitFor`, `outcomeExitCode`, `exitCodeFor`), and PDD PR paste-line words (`PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`) live in the host caller outside `src/runtime/`; `src/runtime/` functions receive them as injected ports.

Expose these synchronous slice loaders (each loading and caching only its target owner module via `createRequire(import.meta.url)` on first call):

| Slice loader | Target owner module |
|---|---|
| `runtimeScenarioJsonSlice()` | `scenario-json.mjs` |
| `runtimeWorkspaceSlice()` | `runtime-workspace.mjs` |
| `runtimeOutcomeSlice()` | `runtime-outcome.mjs` |
| `runtimeOutputSlice()` | `runtime-output.mjs` |
| `runtimePreflightSlice()` | `runtime-preflight.mjs` |
| `runtimeAgentPacketSlice()` | `agent-packet.mjs` |
| `runtimeCheckPlanSlice()` | `runtime-check-plan.mjs` |
| `runtimeClientSlice()` | `runtime-client.mjs` |

### Leaf and command exports

Load each owner module only when the exported function (or its slice loader) is called, preserving argument forwarding, return values, thrown errors, and port behavior:

| Owner module | Exported bindings | Loading rule |
|---|---|---|
| `scenario-json.mjs` | `exactIntegerLeaves`, `exactValue`, `jsonSafe`, `parseScenarioJson`, `roundedNumberTokens`, `stringifyScenarioJson`, `withExactIntegers` | Load synchronously on first call via `runtimeScenarioJsonSlice()` |
| `runtime-workspace.mjs` | `allowsRuntimePath`, `loadRuntimeWorkspace`, `requireRuntimePath` | Load synchronously on first call via `runtimeWorkspaceSlice()` |
| `runtime-outcome.mjs` | `CHECK_STATES`, `PROVIDER_TEXT`, `hasProgress`, `outcomeDone`, `outcomeFor`, `outcomeOverall`, `outcomeText`, `progressText`, `resultOutcome`, `resultOverall` | Constants immediate; functions load synchronously on first call via `runtimeOutcomeSlice()` |
| `runtime-output.mjs` | `OPEN_STATES`, `PROVIDER_TEXT`, `causeText`, `cleanText`, `coverageText`, `jsonRow`, `progressTicker`, `projectAnswer`, `refusalView`, `renderJson`, `renderText`, `sinceText`, `stepTimeLimit`, `storyLines`, `summaryLine`, `tryUsage`, `tryUsageHeaders`, `tryUsageLine`, `validLink` | Constants immediate; functions load synchronously on first call via `runtimeOutputSlice()` |
| `runtime-preflight.mjs` | `DRAFT_SERVER_TEXT`, `LIMITS`, `PreflightError`, `STALE_HINT`, `TEST_SCHEMA`, `captureSource`, `checkInput`, `createStrictSourceAccess`, `defaultMaxCalls`, `discoveryRefusal`, `discoveryVisibleFiles`, `exactNumberSpelling`, `executableInterfaceText`, `fillHashes`, `findTests`, `formatSize`, `formatWarningLines`, `gitFiles`, `hasPromptInterface`, `interfaceBlocks`, `interfaceFormatWarnings`, `interfaceKindProblems`, `interfaceSchemaProblems`, `isSecretPath`, `numberWarnings`, `otherFiles`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `scenarioShapeRefusal`, `schemaKeywordWarningLines`, `sha256`, `sharedSourceFiles`, `sourceFilePort`, `staleHint`, `storyCriteria`, `tarFiles` | Constants immediate; `PreflightError` forwards constructor and `Symbol.hasInstance` lazily; functions load synchronously on first call via `runtimePreflightSlice()` |
| `agent-packet.mjs` | `buildAgentInput` | Load synchronously on first call via `runtimeAgentPacketSlice()` |
| `runtime-check-plan.mjs` | `baselineReport`, `buildCheckPlan`, `checkPlanResultLines`, `checkPlanResults`, `selectCheckTests` | Load synchronously on first call via `runtimeCheckPlanSlice()` |
| `product-composition.mjs` | `composeProductTry`, `productTapCallBound`, `selectJourneys` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `agent-guide.mjs` | `createTryGuide` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `agent-project.mjs` | `buildProjectCard`, `readAgentScenarios` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `contracts.mjs` | `runContracts` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `runtime-slots.mjs` | `runJobs` | `await import('./runtime-slots.mjs')` when called |
| `interface-draft.mjs` | `loadInterfaceDraft`, `runAutomaticApproval`, `runInterfaceDraft` | `await import('./interface-draft.mjs')` when called (`loadInterfaceDraft` resolves to `{ contractCoverage, coverageView, missingInterfaces }`) |
| `agent-chat.mjs` | `createAgentBridge` | `await import('./agent-chat.mjs')` when called |
| `agent-ask.mjs` | `askAgent` | `await import('./agent-ask.mjs')` when called |
| `runtime-workspace-migration.mjs` | `migrateRuntimeWorkspace` | `await import('./runtime-workspace-migration.mjs')` when called |
| `try-mcp.mjs` | `createTryTools`, `runMcp` | `createTryTools` loads synchronously on first call via `createRequire(import.meta.url)`; `runMcp` uses `await import('./try-mcp.mjs')` |
| `try-doors.mjs` | `openCli`, `runShim`, `saveLast` | `await import('./try-doors.mjs')` when called |
| `try-http.mjs` | `openServe` | `await import('./try-http.mjs')` when called |
| `runtime-client.mjs` | `acquireCaseWriteOwnership`, `acquireRuntimeBatchLock`, `applyPendingCase`, `applyPendingCaseWithHandoff`, `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `defaultLineReader`, `loadRuntimeClient`, `readContractHistory`, `readTryOwner`, `resendableStoryChecks`, `runCheck`, `runDoorCall`, `runTry`, `runtimeOrigin`, `runtimeWorkspaceMigrationStore`, `saveDoorCase`, `saveDoorCaseResult`, `savedStoryEvidence` | Synchronous helpers (`createSavedStoryEvidenceReader`, `defaultLineReader`, `readContractHistory`, `runtimeOrigin`, `runtimeWorkspaceMigrationStore`, `saveDoorCase`, `saveDoorCaseResult`) load on first call via `runtimeClientSlice()`; async entries use `await import('./runtime-client.mjs')` (`loadRuntimeClient` resolves to `{ DEFAULT_RUNTIME_URL, checkRuntimeHealth, runtimeOrigin }`, keeping `DEFAULT_RUNTIME_URL` defined in `runtime-client.mjs` alone) |

`runTry(input, ports)` forwards `ports.tryLauncherUrl` to `openCli` when supplied so the host CLI can pin a stable launcher module URL outside `src/runtime/`; when omitted, `openCli` falls back to `try-doors.mjs`.

## Dependencies

- [Exact scenario numbers](scenario-json.prompt.md): required generation context for `exactIntegerLeaves`, `exactValue`, `jsonSafe`, `parseScenarioJson`, `roundedNumberTokens`, `stringifyScenarioJson`, and `withExactIntegers`.
- [Runtime workspace boundary](runtime-workspace.prompt.md): required generation context for `allowsRuntimePath`, `loadRuntimeWorkspace`, and `requireRuntimePath`.
- [Runtime outcome](runtime-outcome.prompt.md): required generation context for `CHECK_STATES`, `PROVIDER_TEXT`, `hasProgress`, `outcomeDone`, `outcomeFor`, `outcomeOverall`, `outcomeText`, `progressText`, `resultOutcome`, and `resultOverall`.
- [Runtime output](runtime-output.prompt.md): required generation context for `OPEN_STATES`, `causeText`, `cleanText`, `coverageText`, `jsonRow`, `progressTicker`, `projectAnswer`, `refusalView`, `renderJson`, `renderText`, `sinceText`, `stepTimeLimit`, `storyLines`, `summaryLine`, `tryUsage`, `tryUsageHeaders`, `tryUsageLine`, and `validLink`.
- [Runtime preflight](runtime-preflight.prompt.md): required generation context for `DRAFT_SERVER_TEXT`, `LIMITS`, `PreflightError`, `STALE_HINT`, `TEST_SCHEMA`, `captureSource`, `checkInput`, `createStrictSourceAccess`, `defaultMaxCalls`, `discoveryRefusal`, `discoveryVisibleFiles`, `exactNumberSpelling`, `executableInterfaceText`, `fillHashes`, `findTests`, `formatSize`, `formatWarningLines`, `gitFiles`, `hasPromptInterface`, `interfaceBlocks`, `interfaceFormatWarnings`, `interfaceKindProblems`, `interfaceSchemaProblems`, `isSecretPath`, `numberWarnings`, `otherFiles`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `scenarioShapeRefusal`, `schemaKeywordWarningLines`, `sha256`, `sharedSourceFiles`, `sourceFilePort`, `staleHint`, `storyCriteria`, and `tarFiles`.
- [Agent packet](agent-packet.prompt.md): required generation context for `buildAgentInput`.
- [Runtime check plan](runtime-check-plan.prompt.md): required generation context for `baselineReport`, `buildCheckPlan`, `checkPlanResultLines`, `checkPlanResults`, and `selectCheckTests`.
- [Product Simulator composition](product-composition.prompt.md): required generation context for `composeProductTry`, `productTapCallBound`, and `selectJourneys`.
- [Runtime slots](runtime-slots.prompt.md): required generation context for `runJobs`.
- [Shared contracts](contracts.prompt.md): required generation context for `runContracts`.
- [Interface drafting](interface-draft.prompt.md): required generation context for `contractCoverage`, `coverageView`, `missingInterfaces`, `runAutomaticApproval`, and `runInterfaceDraft`.
- [Agent chat](agent-chat.prompt.md), [Simulator agent turn](agent-ask.prompt.md), [Try guide](agent-guide.prompt.md), and [Project facts](agent-project.prompt.md): required generation context for `askAgent`, `buildProjectCard`, `createAgentBridge`, `createTryGuide`, and `readAgentScenarios`.
- [Workspace migration](runtime-workspace-migration.prompt.md): required generation context for `migrateRuntimeWorkspace`.
- [Try MCP server](try-mcp.prompt.md): required generation context for `createTryTools` and `runMcp`.
- [Try doors](try-doors.prompt.md) and [Try HTTP server](try-http.prompt.md): required generation context for `openCli`, `openServe`, `runShim`, `saveLast`, and `tryLauncherUrl` forwarding.
- [Runtime client](runtime-client.prompt.md): required generation context for `DEFAULT_RUNTIME_URL`, `acquireCaseWriteOwnership`, `acquireRuntimeBatchLock`, `applyPendingCase`, `applyPendingCaseWithHandoff`, `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `defaultLineReader`, `readContractHistory`, `readTryOwner`, `resendableStoryChecks`, `runCheck`, `runDoorCall`, `runTry`, `runtimeOrigin`, `runtimeWorkspaceMigrationStore`, `saveDoorCase`, `saveDoorCaseResult`, and `savedStoryEvidence`.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"approved","prose_sha256": "777c3a9247d5359ff767eedf9ba0358f79064f8e1bac6d62a4404f64f5145771","reason":"Exposes live JavaScript ESM static and deferred dynamic-import bindings across src/runtime/ submodules, which bound Runtime ports cannot fake."}
```
</details>
