# Runtime package entry

Own `src/runtime/index.mjs`. It is the single public entry of `src/runtime/`, exposing the Runtime commands, local format and workspace readers, check-plan and outcome helpers, constants, and agent packet builder consumed by pdd through [`src/runtime-seam.mjs`](runtime-seam.prompt.md).

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
| `src/runtime/runtime-check-plan.mjs` | `checkPlanResultLines`, `checkPlanResults` | Load synchronously on first call via `createRequire(import.meta.url)` |
| `src/runtime/runtime-slots.mjs` | `runJobs` | `await import('./runtime-slots.mjs')` when called |
| `src/runtime/contracts.mjs` | `runContracts` | `await import('./contracts.mjs')` when called |
| `src/runtime/interface-draft.mjs` | `loadInterfaceDraft`, `runAutomaticApproval`, `runInterfaceDraft` | `await import('./interface-draft.mjs')` when called (`loadInterfaceDraft` resolves to `{ contractCoverage, coverageView, missingInterfaces }`) |
| `src/runtime/try-mcp.mjs` | `runMcp` | `await import('./try-mcp.mjs')` when called |
| `src/runtime/try-doors.mjs` | `runShim` | `await import('./try-doors.mjs')` when called |
| `src/runtime/runtime-client.mjs` | `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `loadRuntimeClient`, `runCheck`, `runTry` | `await import('./runtime-client.mjs')` when called (`createSavedStoryEvidenceReader(ports)` returns an async reader that loads `runtime-client.mjs` on first read and retains per-reader capture state; `loadRuntimeClient` resolves to `{ DEFAULT_RUNTIME_URL, checkRuntimeHealth, runtimeOrigin }`) |

`runTry(input, ports)` forwards `ports.tryLauncherUrl` to `openCli` when supplied so the host CLI can pin a stable launcher module URL outside `src/runtime/`; when omitted, `openCli` falls back to `src/runtime/try-doors.mjs`.

## Dependencies

- [Exact scenario numbers](scenario-json.prompt.md): required generation context for `exactIntegerLeaves`, `jsonSafe`, `parseScenarioJson`, `stringifyScenarioJson`, and `withExactIntegers`.
- [Runtime workspace boundary](runtime-workspace.prompt.md): required generation context for `allowsRuntimePath`, `loadRuntimeWorkspace`, and `requireRuntimePath`.
- [Runtime outcome](runtime-outcome.prompt.md): required generation context for `outcomeText` and `resultOutcome`.
- [Runtime output](runtime-output.prompt.md): required generation context for `PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`, `causeText`, `cleanText`, and `storyLines`.
- [Runtime preflight](runtime-preflight.prompt.md): required generation context for `LIMITS`, `captureSource`, `checkInput`, `findTests`, `gitFiles`, `interfaceBlocks`, `interfaceSchemaProblems`, `isSecretPath`, `isStoryPath`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `sha256`, and `sourceFilePort`.
- [Agent packet](agent-packet.prompt.md): required generation context for `buildAgentInput`.
- [Runtime check plan](runtime-check-plan.prompt.md): required generation context for `checkPlanResultLines` and `checkPlanResults`.
- [Runtime slots](runtime-slots.prompt.md): required generation context for `runJobs`.
- [Shared contracts](contracts.prompt.md): required generation context for `runContracts`.
- [Interface drafting](interface-draft.prompt.md): required generation context for `contractCoverage`, `coverageView`, `missingInterfaces`, `runAutomaticApproval`, and `runInterfaceDraft`.
- [Try MCP server](try-mcp.prompt.md): required generation context for `runMcp`.
- [Try doors](try-doors.prompt.md): required generation context for `runShim` and `tryLauncherUrl` forwarding.
- [Runtime client](runtime-client.prompt.md): required generation context for `DEFAULT_RUNTIME_URL`, `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `runCheck`, `runTry`, and `runtimeOrigin`.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256":"ac6a89af04eada57b7f060f9f6d20aa472c57bdf0d2974fe68c2e34c05e675a2","reason":"Exposes live JavaScript ESM static and deferred dynamic-import bindings across src/runtime/ submodules, which bound Runtime ports cannot fake."}
```
</details>
