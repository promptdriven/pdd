# PDD to Runtime seam

Own `src/runtime-seam.mjs` and the stable launcher entry `src/try-doors.mjs`. `src/runtime-seam.mjs` is the sole module in pdd outside `src/runtime/` permitted to import `src/runtime/`. Every pdd module in `src/`, `bin/`, and `scripts/` accesses Runtime commands, local format and workspace readers, check-plan and outcome helpers, and constants exclusively through `./runtime-seam.mjs`.

The seam keeps stable pdd-owned file paths for anything pdd writes into a user's files or passes to a child process:

- `src/try-doors.mjs` re-exports `runShim` from `./runtime-seam.mjs` so `.pdd/try/bin/<program>` launchers keep a stable pdd-owned module path across upgrades and package extraction.
- `runTry(input, ports)` in `src/runtime-seam.mjs` defaults `ports.tryLauncherUrl` to the `file:` URL of `src/try-doors.mjs` before delegating to `src/runtime/index.mjs`, preserving an explicit `ports.tryLauncherUrl` when provided.

## Public contract

Re-export the public bindings of [`src/runtime/index.mjs`](runtime-entry.prompt.md), preserving parameter handling, return values, thrown errors, and port forwarding:

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
- `runShim`
- `buildAgentInput`

The seam holds no mutable state and performs no I/O at load time beyond loading `src/runtime/index.mjs`. Both static imports and dynamic `import('./runtime-seam.mjs')` callers receive the same namespace.

## Dependencies

- [Runtime package entry](runtime-entry.prompt.md): required generation context for the exported Runtime package bindings and their contracts.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256":"26203ff5659c5841c111ba1243117613467d98ede084be8286d0272ee78a3fb1","reason":"Re-exports live JavaScript ESM module bindings from src/runtime/index.mjs as pdd's sole import seam, which bound Runtime ports cannot fake."}
```
</details>
