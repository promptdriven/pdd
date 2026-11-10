# Machine resource observation ports

I can check `prompts/cli/machine-resources.prompt.md` with declared filesystem and OS observation ports.

```pdd-boundary
prompts/cli/machine-resources.prompt.md
```

## Acceptance criteria

1. `readMachineResources` reads Linux memory (converting KiB to bytes), PSI pressure, volume space and check metadata (`cpuIds`, `platform`, `battery`, `virtualized`, `taskset`), and returns `null` for malformed or invalid metrics without hiding valid observations.
2. `machineCheckPorts` returns the evaluated check observations on Linux and falls back to non-Linux defaults (`battery: false`, `virtualized: false`, `taskset: null`, `memory: null`, `load: null`) when probes fail or metrics are unavailable.
