# Manage added trusted people

As a repository maintainer, I can add and remove trusted names, so that I can maintain the explicit list.

## Acceptance criteria

1. Running `pdd autopilot trust Dana` adds Dana to the saved trust list.
2. Running `pdd autopilot untrust Dana` removes Dana from the saved trust list.

## Rules to check

- A failed file write reports a clear error, exits nonzero and leaves `pdd.json` unchanged. Native test: inject a failed write and inspect the original file.
- Setting a mode starts no run or interpreter. Native test: spy on workflow and interpreter dispatch.
- Native test: save with unrelated top-level and Autopilot keys; verify both remain unchanged.
- Native test: exercise CLI parsing, dispatch and help with injected ports.
