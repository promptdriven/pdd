# Shared full-suite queue ports

As an operator, I want the shared full-suite queue to manage capacity snapshots, queue tickets, clean suite environments, and process execution through declared ports, so that the hosted Runtime can verify admission, progress, and cleanup rules.

```pdd-boundary
prompts/cli/test-suite-queue.prompt.md
```

## Acceptance criteria

1. `suiteQueueRoot` resolves `PDD_SUITE_QUEUE`, `PDD_VM_SUITE_LOCK.queue`, or `/tmp/pdd-full-suite-UID` from `process.current`, and throws `Error` when the resolved path is relative.
2. `suiteStatusWords` formats waiting, running, finished, failed, and unavailable status lines and throws `Error` when `suite` is invalid.
3. `calculateCheckCapacity`, `configureCheckCapacity`, `releaseCheckCapacity`, and `readCheckStatus` compute and persist `capacity.json` under `lock.acquire` and `lock.release`, count running and waiting tickets from `fs.readdir` and `files.read`, and throw `Error` on invalid observations or owners.
4. `readSuiteProgress` returns the latest ticket progress and paused duration for `cwd`, returns `{state: "unavailable", reason, pausedMs: 0}` when queue records are unreadable, and throws `Error` when `cwd` is invalid.
5. `executeSuite` and `runTestSuite` enforce command and timeout rules, allocate and clean up the isolated suite environment under the queue root, record ticket receipts and validation logs, and verify descendant process-group termination via `process.groupAlive`.

## Prompt tests

Scenario `test/runtime/test-suite-queue-ports.json` covers `suiteQueueRoot`, `suiteStatusWords`, `calculateCheckCapacity`, `configureCheckCapacity`, `releaseCheckCapacity`, `readCheckStatus`, `readSuiteProgress`, `executeSuite`, and `runTestSuite` with normal and error paths across all declared ports.
