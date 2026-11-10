# Environment validation recovery ports

I can check `prompts/cli/autopilot-environment.prompt.md` with declared machine-resource, tool, queue-directory, blob and process-liveness ports.

```pdd-boundary
prompts/cli/autopilot-environment.prompt.md
```

## Acceptance criteria

1. `classifyStuckCause`, `environmentRecovery`, `environmentStatus` and `environmentWakeTag` classify environment versus work stops, validate saved retry records and format status and wake tags, returning `work` or `null` for test failures or ineligible runs.
2. `machineHealth` and `environmentHealthy` evaluate memory, disk, load, PSI, missing-tool presence and suite queue tickets through declared ports, returning `healthy: true` when thresholds and dead-runner ticket checks pass and `false` when memory/disk or tool checks fail.
