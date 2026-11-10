# Machine interpreter queue ports

I can check `prompts/cli/interpreter-queue.prompt.md` with declared blob, directory, lock, process, clock and output ports.

```pdd-boundary
prompts/cli/interpreter-queue.prompt.md
```

## Acceptance criteria

1. `interpreterQueueEnvironment`, `acquireInterpreterSlot`, `markInterpreterDispatch` and `observeInterpreterRequest` resolve queue settings, allocate and mark running tickets, record terminal verdicts in `ticket-1.json` and `capacity.json`, and raise `local-state-unavailable` for relative paths, duplicate requests or repeated dispatch marks.
2. `readInterpreterProgress`, `interpreterStatusWords` and `configureInterpreterTestMode` report ticket progress and status lines, persist test-mode owner leases in `capacity.json`, and return empty progress or raise `local-state-unavailable` when no matching records exist or the owner is blank.
