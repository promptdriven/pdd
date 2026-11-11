# PDD to Runtime seam

Own `src/runtime-seam.mjs`. It is the sole module in pdd outside `src/runtime/` permitted to import `src/runtime/`. Every pdd module in `src/`, `bin/`, and `scripts/` accesses Runtime commands, local format and workspace readers, check-plan and outcome helpers, and constants exclusively through `./runtime-seam.mjs`.

## Public contract

Re-export the public bindings of [`src/runtime/index.mjs`](runtime-entry.prompt.md) unchanged, preserving exact binding identity, parameter handling, return values, thrown errors, and port forwarding:

- `DEFAULT_RUNTIME_URL`, `checkRuntimeHealth`, `createSavedStoryEvidenceReader`, `runCheck`, `runTry`, `runtimeOrigin`
- `LIMITS`, `captureSource`, `checkInput`, `findTests`, `gitFiles`, `interfaceBlocks`, `interfaceSchemaProblems`, `isSecretPath`, `isStoryPath`, `preflight`, `promptRefusal`, `promptSchemaRefusals`, `proseSha256`, `readPrompt`, `sha256`, `sourceFilePort`
- `PROMPT_TESTS_LABEL`, `PROMPT_TESTS_WORDS`, `causeText`, `cleanText`, `storyLines`
- `outcomeText`, `resultOutcome`
- `checkPlanResultLines`, `checkPlanResults`
- `allowsRuntimePath`, `loadRuntimeWorkspace`, `requireRuntimePath`
- `exactIntegerLeaves`, `jsonSafe`, `parseScenarioJson`, `stringifyScenarioJson`, `withExactIntegers`
- `contractCoverage`, `coverageView`, `missingInterfaces`, `runAutomaticApproval`, `runInterfaceDraft`
- `runContracts`
- `runJobs`
- `runMcp`
- `buildAgentInput`

The seam holds no mutable state and performs no I/O at load time beyond loading `src/runtime/index.mjs`. Both static imports and dynamic `import('./runtime-seam.mjs')` callers receive the same namespace.

## Dependencies

- [Runtime package entry](runtime-entry.prompt.md): required generation context for the exported Runtime package bindings and their contracts.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256":"0b6ff8207420382995670f02eeeb4c5d4f87d4286bd60f56068a2940f1722ba5","reason":"Re-exports live JavaScript ESM module bindings from src/runtime/index.mjs as pdd's sole import seam, which bound Runtime ports cannot fake."}
```
</details>
