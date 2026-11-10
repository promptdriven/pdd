# Check runtime client through declared ports

The [runtime client prompt](../prompts/cli/runtime-client.prompt.md) runs local and hosted checks, Try sessions, health checks, saved Story evidence and contract-history reads, batch locks, received-case imports, and door calls through declared Git, file, `gh`, HTTP, clock, output, and handle-collection ports.

```pdd-boundary
prompts/cli/runtime-client.prompt.md
```

## Acceptance criteria

1. `runCheck`, `runTry` and `checkRuntimeHealth` resolve the repository root and files through `git` and `files`, authenticate with `gh.exec`, call the PDD interpreter through `http.request`, emit CLI output through `output.stdout` and `output.stderr`, and return `{exitCode}` or `{state, detail, fix}`.
2. `readContractHistory`, `savedStoryEvidence`, `createSavedStoryEvidenceReader` (`readSavedStoryEvidence`) and `acquireRuntimeBatchLock` (`releaseBatchLock`) read saved batches and contract snapshots from `files` and manage `SavedStoryEvidenceReader` and `RuntimeBatchLock` handles.
3. `acquireCaseWriteOwnership` (`release`), `saveDoorCase`, `saveDoorCaseResult`, `applyPendingCase`, `applyPendingCaseWithHandoff`, `runDoorCall` and `readTryOwner` manage `CaseWriteOwnership` handles, record and apply received Try cases, execute authenticated door calls, and read Try owner metadata.
4. Invalid inputs, busy batch locks, unavailable write ownership, and refused door or owner calls raise the declared entry error (`invalid-runtime-input`, `invalid-health-input`, `invalid-history-input`, `invalid-evidence-input`, `invalid-reader-input`, `batch-lock-busy`, `batch-lock-invalid`, `ownership-unavailable`, `invalid-ownership-input`, `invalid-case-input`, `invalid-pending-input`, `door-call-refused`, `door-call-unknown`, `invalid-door-input`, `try-owner-unavailable`, or `invalid-owner-input`).
