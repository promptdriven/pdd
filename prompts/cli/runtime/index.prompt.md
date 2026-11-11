# Runtime package entry

Own `src/runtime/index.mjs`. It is the single public entry of `src/runtime/`, exposing the Runtime commands, local format and workspace readers, check-plan and outcome helpers, constants, and agent packet builder consumed by pdd through [`src/runtime-seam.mjs`](../runtime-seam.prompt.md).

## Public contract

Re-export each binding directly from its canonical module in `src/runtime/` with identical function or value identity, arity, errors, and port behavior. The module keeps no state, performs no I/O of its own, and adds no wrapper around any export.

| Owner module | Exported bindings |
|---|---|
| `src/runtime/scenario-json.mjs` | `exactIntegerLeaves`, `jsonSafe`, `parseScenarioJson`, `stringifyScenarioJson`, `withExactIntegers` |
| `src/runtime/runtime-workspace.mjs` | `allowsRuntimePath`, `loadRuntimeWorkspace`, `requireRuntimePath` |
| `src/runtime/runtime-outcome.mjs` | `outcomeText`, `resultOutcome` |
| `src/runtime/runtime-output.mjs` | `PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`, `causeText`, `cleanText`, `storyLines` |
| `src/runtime/runtime-preflight.mjs` | `LIMITS`, `captureSource`, `checkInput`, `findTests`, `gitFiles`, `interfaceBlocks`, `interfaceSchemaProblems`, `isSecretPath`, `isStoryPath`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `sha256`, `sourceFilePort` |
| `src/runtime/agent-packet.mjs` | `buildAgentInput` |
| `src/runtime/runtime-check-plan.mjs` | `checkPlanResultLines`, `checkPlanResults` |
| `src/runtime/runtime-slots.mjs` | `runJobs` |
| `src/runtime/contracts.mjs` | `runContracts` |
| `src/runtime/interface-draft.mjs` | `contractCoverage`, `coverageView`, `missingInterfaces`, `runAutomaticApproval`, `runInterfaceDraft` |
| `src/runtime/try-mcp.mjs` | `runMcp` |
| `src/runtime/runtime-client.mjs` | `DEFAULT_RUNTIME_URL`, `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `runCheck`, `runTry`, `runtimeOrigin` |

## Evaluation order

Re-export pure leaf readers and constants (`scenario-json.mjs`, `runtime-workspace.mjs`, `runtime-outcome.mjs`, `runtime-output.mjs`, `runtime-preflight.mjs`, `agent-packet.mjs`, `runtime-check-plan.mjs`) ahead of command modules (`runtime-slots.mjs`, `contracts.mjs`, `interface-draft.mjs`, `try-mcp.mjs`, `runtime-client.mjs`) so modules participating in cyclic ESM loading observe initialized constant bindings (`LIMITS`, `PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`).

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
- [Runtime client](runtime-client.prompt.md): required generation context for `DEFAULT_RUNTIME_URL`, `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `runCheck`, `runTry`, and `runtimeOrigin`.
