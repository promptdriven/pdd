# Runtime package entry

Own `src/runtime/index.mjs`. It is the single public entry of `src/runtime/`, exposing the Runtime commands, local format and workspace readers, check-plan, product-composition, and outcome helpers, agent bridge and workspace migration entries, constants, and agent packet builder consumed by pdd through [`src/runtime-seam.mjs`](runtime-seam.prompt.md).

No module under `src/runtime/` may import or address any relative path outside `src/runtime/`. Caller metadata (`client.version`, `client.commands`, `workflow.base_sha`) and host-owned capabilities (file-owner headers, approvals, local agent launchers, workflow evidence eligibility, native Story assessment, product Markdown document and world-writer parsers, SVG layout advisory, and screen comparison) arrive exclusively through request fields and `ports`.

## Public contract

Keep module loading faithful to callers: statically re-export only the pure leaf readers and constants that pdd startup modules load statically, and defer command and check-plan modules until first invocation so light CLI commands never load `runtime-client.mjs` or other heavy Runtime modules and command load failures surface inside their callers' `try/catch` guards.

### Static leaf exports

Re-export directly with identical binding identity, arity, errors, and port behavior:

| Owner module | Exported bindings |
|---|---|
| `src/runtime/scenario-json.mjs` | `exactIntegerLeaves`, `jsonSafe`, `parseScenarioJson`, `stringifyScenarioJson`, `withExactIntegers` |
| `src/runtime/runtime-workspace.mjs` | `allowsRuntimePath`, `loadRuntimeWorkspace`, `requireRuntimePath` |
| `src/runtime/runtime-outcome.mjs` | `outcomeText`, `resultOutcome` |
| `src/runtime/runtime-output.mjs` | `PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`, `causeText`, `cleanText`, `storyLines` |
| `src/runtime/runtime-preflight.mjs` | `LIMITS`, `captureSource`, `checkInput`, `findTests`, `gitFiles`, `interfaceBlocks`, `interfaceSchemaProblems`, `isSecretPath`, `isStoryPath`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `sha256`, `sourceFilePort` |
| `src/runtime/agent-packet.mjs` | `buildAgentInput` |

### Deferred exports

Load each owner module only when the exported function is called:

| Owner module | Exported bindings | Loading rule |
|---|---|---|
| `src/runtime/runtime-check-plan.mjs` | `buildCheckPlan`, `checkPlanResultLines`, `checkPlanResults` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `src/runtime/product-composition.mjs` | `composeProductTry`, `productTapCallBound`, `selectJourneys` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `src/runtime/agent-guide.mjs` | `createTryGuide` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `src/runtime/contracts.mjs` | `runContracts` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `src/runtime/runtime-slots.mjs` | `runJobs` | `await import('./runtime-slots.mjs')` when called |
| `src/runtime/interface-draft.mjs` | `loadInterfaceDraft`, `runAutomaticApproval`, `runInterfaceDraft` | `await import('./interface-draft.mjs')` when called (`loadInterfaceDraft` resolves to `{ contractCoverage, coverageView, missingInterfaces }`) |
| `src/runtime/agent-chat.mjs` | `createAgentBridge` | `await import('./agent-chat.mjs')` when called |
| `src/runtime/runtime-workspace-migration.mjs` | `migrateRuntimeWorkspace` | `await import('./runtime-workspace-migration.mjs')` when called |
| `src/runtime/try-mcp.mjs` | `runMcp` | `await import('./try-mcp.mjs')` when called |
| `src/runtime/try-doors.mjs` | `runShim` | `await import('./try-doors.mjs')` when called |
| `src/runtime/runtime-client.mjs` | `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `loadRuntimeClient`, `readTryOwner`, `runCheck`, `runTry` | `await import('./runtime-client.mjs')` when called (`createSavedStoryEvidenceReader(ports)` returns an async reader that loads `runtime-client.mjs` on first read and retains per-reader capture state; `loadRuntimeClient` resolves to `{ DEFAULT_RUNTIME_URL, checkRuntimeHealth, runtimeOrigin }`) |

`runTry(input, ports)` forwards `ports.tryLauncherUrl` to `openCli` when supplied so the host CLI can pin a stable launcher module URL outside `src/runtime/`; when omitted, `openCli` falls back to `src/runtime/try-doors.mjs`.

### Package API

Preserve every export above. Add thin command wrappers without changing the
owners' validation, defaults, side effects, returned exit codes or output through
`ports.stdout` and `ports.stderr`. Load command owners only on invocation, including
when an import fails. The wrappers do not manufacture a Result or collect streams.
All accept the existing input and ports. For command inputs, `root` aliases `cwd`
(explicit `cwd` wins), and `tests` aliases `words` as paths (strings or `{path}`);
explicit `words`, even an empty array, wins. Options keep their CLI flag keys.

| API | Delegate and input adaptation |
|---|---|
| `check(input, ports)` | `runCheck`; retain `cache`, `client`, `workflow` |
| `lint(input, ports)` | `runCheck` with `options['--lint'] = true` |
| `read(input, ports)` | `runCheck` with `--read = true`; `call_id`, then `batch`, supplies the sole operand when supplied, otherwise retain words (empty means latest) |
| `retry(input, ports)` | `runCheck`; supplied `batch` becomes `options['--retry']`, otherwise retain that option |
| `simulate(input, ports)` | `runTry`; supplied `test` supplies one operand; mode `open` keeps options, modes `cli`, `serve`, `save-last`, `stop` supply their same-named true CLI flag |
| `jobs(input, ports)` | `runJobs` unchanged, including input `env`, `client`, `commands` |
| `health(input, ports)` | `checkRuntimeHealth` unchanged |
| `mcp(input, ports)` | `runMcp`; supplied `story` supplies one operand; retain input `env` |
| `local(input, ports)` | `runCheck`; supplied `what` (`files`, `fill-hash`, `explain-bindings`) supplies its true flag; without `what`, require one of those existing mode flags or `--lint` with `--local`; retain existing option validation, no network in these modes |
| `draftInterfaces(input, ports)` | `runInterfaceDraft`; `paths` aliases `words`; retain `all`, `json`, `contract`, `extend`, `refresh` |
| `contracts(input, ports)` | synchronous `runContracts`; supplied `sync` chooses `['sync']` or `[]`; supplied true `write` supplies `--write = true` |

Expose reader groups without eagerly loading additional modules:

- `format.parseScenario`, `stringifyScenario`, `exactValue`, `interfaceBlocks`,
  `proseSha256`, `interfaceProblems`, `storyCriteria` retain the exact signatures
  and returns of `parseScenarioJson`, `stringifyScenarioJson`, `exactValue`,
  `interfaceBlocks`, `proseSha256`, `interfaceSchemaProblems`, `storyCriteria`.
  In particular blocks remain regex matches with indices; criteria remain strings.
- `format.isScenario(text)` checks the parsed document's `schema_version` against
  the preflight owner's `TEST_SCHEMA`; malformed JSON throws as in the workflow reader.
- `format.setInterfaceStatus(text, {status, prose_sha256})` is a pure text editor
  for PDD's approval caller, never an approval or file write. Accept `draft` or
  `approved` and a string digest. Return null for invalid metadata, malformed or
  multiple blocks, or missing/duplicate/non-string top-level metadata. Replace
  only the two top-level JSON string tokens, preserving all other bytes, nested
  metadata and exact numeric literals. Approval policy remains with PDD.
- `source.identity({root, ...selection})` calls `captureSource(root, selection)`
  and returns its full existing capture, including archive, files and hashes.
- `saved.results(input, ports)` lazily calls `savedStoryEvidence` with today's
  `{root, comparisonRoot}` input and returns `{stories, warnings}`. Keep the
  existing reusable `createSavedStoryEvidenceReader` export for shared capture state.
- `workspace.policy` and `workspace.allows` are the identical bindings of
  `loadRuntimeWorkspace` and `allowsRuntimePath`.
- `render(result, {as = 'table'})` forwards to `renderText(result)` for table,
  `renderJson(result)` for json, `storyLines(result.rows)` for story-lines, and
  `summaryLine(result.rows)` for summary. Retain their existing result types
  (JSON is an object; story-lines are `[story, text]` pairs) and input fields.
  Unknown render or simulation/local modes throw TypeError before delegation.

`version()` synchronously returns exactly `{package, api_version, formats,
limits, engine_sha}` using local leaf facts only: `formats` is
`{scenario: TEST_SCHEMA}`, `limits` is `LIMITS`; package, API version and running
engine SHA are unknown and null. Never infer the running engine from a copied
format build, read a parent package file, load the client, or use the network.

## Dependencies

- [Exact scenario numbers](scenario-json.prompt.md): required generation context for `exactIntegerLeaves`, `jsonSafe`, `parseScenarioJson`, `stringifyScenarioJson`, `exactValue`, `withExactIntegers`, and their `format` bindings.
- [Runtime workspace boundary](runtime-workspace.prompt.md): required generation context for `allowsRuntimePath`, `loadRuntimeWorkspace`, and `requireRuntimePath`.
- [Runtime outcome](runtime-outcome.prompt.md): required generation context for `outcomeText` and `resultOutcome`.
- [Runtime output](runtime-output.prompt.md): required generation context for `PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`, `causeText`, `cleanText`, `storyLines`, `renderText`, `renderJson`, `summaryLine`, and the `render` adapter.
- [Runtime preflight](runtime-preflight.prompt.md): required generation context for `LIMITS`, `TEST_SCHEMA`, `captureSource`, `checkInput`, `findTests`, `gitFiles`, `interfaceBlocks`, `interfaceSchemaProblems`, `isSecretPath`, `isStoryPath`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `sha256`, `sourceFilePort`, `storyCriteria`, and their `format`, `source`, and `version` uses.
- [Agent packet](agent-packet.prompt.md): required generation context for `buildAgentInput`.
- [Runtime check plan](runtime-check-plan.prompt.md): required generation context for `buildCheckPlan`, `checkPlanResultLines`, and `checkPlanResults`.
- [Product Simulator composition](product-composition.prompt.md): required generation context for `composeProductTry`, `productTapCallBound`, and `selectJourneys`.
- [Runtime slots](runtime-slots.prompt.md): required generation context for `runJobs`.
- [Shared contracts](contracts.prompt.md): required generation context for `runContracts`.
- [Interface drafting](interface-draft.prompt.md): required generation context for `contractCoverage`, `coverageView`, `missingInterfaces`, `runAutomaticApproval`, and `runInterfaceDraft`.
- [Agent chat](agent-chat.prompt.md) and [Try guide](agent-guide.prompt.md): required generation context for `createAgentBridge` and `createTryGuide`.
- [Workspace migration](runtime-workspace-migration.prompt.md): required generation context for `migrateRuntimeWorkspace`.
- [Try MCP server](try-mcp.prompt.md): required generation context for `runMcp`.
- [Try doors](try-doors.prompt.md): required generation context for `runShim` and `tryLauncherUrl` forwarding.
- [Runtime client](runtime-client.prompt.md): required generation context for `DEFAULT_RUNTIME_URL`, `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `savedStoryEvidence`, `readTryOwner`, `runCheck`, `runTry`, `runtimeOrigin`, and their command and `saved` adapters.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256": "5dec9577b304a1c9048a2d8a284ceb4ca346ee6d13b743a76d810ffdaa8eca01","reason":"Exposes live JavaScript ESM static and deferred dynamic-import bindings across src/runtime/ submodules, which bound Runtime ports cannot fake."}
```
</details>
