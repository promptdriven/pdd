# Change the Autopilot mode

As a repository maintainer, I can change the saved mode, so that later skills can read it.

## Acceptance criteria

1. Running `pdd autopilot auto` saves auto.
2. Running `pdd autopilot observe` saves observe.
3. Running `pdd autopilot off` saves off.

## Rules to check

- A failed file write reports a clear error, exits nonzero and leaves `pdd.json` unchanged. Native test: inject a failed write and inspect the original file.
- Setting a mode starts no run or interpreter. Native test: spy on workflow and interpreter dispatch.
- An invalid stored mode is treated as off with a one-line notice and is unchanged by setup; a mode command replaces it. Native test: use an invalid stored mode and inspect output and disk.
- Native test: save with unrelated top-level and Autopilot keys; verify both remain unchanged.
- Native test: exercise CLI parsing, dispatch and help with injected ports.
- Future native skill test: auto records the checker’s PASS with `--said`, marked as decided by the checker; off and observe require the person’s approval. Approval policy does not read Autopilot and strict approvals remain enforced.
