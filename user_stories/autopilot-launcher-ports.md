# Autopilot launcher ports

As an operator, I want the Autopilot launcher to compute coordinator launch fingerprints, guard mode changes under admission locks, reconcile completion and ticks, and execute start/stop/status/add controls through declared ports, so that the hosted Runtime can verify launcher behavior.

```pdd-boundary
prompts/cli/autopilot-launcher.prompt.md
```

## Acceptance criteria

1. `autopilotLaunchFingerprint` reads `package.json` via `files.read`, hashes the canonical launch payload via `compute.hash_utf8`, and throws `Error` when the coordinator state is invalid.
2. `withAutopilotModeLock` verifies the Git root via `exec.execFile`, claims admission via `lock.claimAdmission`, runs `modeAction.run`, updates `controlRevision` via `process.uuid` and `files.write` when the state file exists, and throws `Error` when `cwd` is empty.
3. `requestAutopilotCompletion` and `tickAutopilot` inspect saved launcher state via `files.read`, claim and release tick locks via `lock.claimTick` and `lock.releaseTick`, reconcile settings and issues when enabled, and throw `Error` on invalid paths.
4. `runAutopilotLauncher` executes `stop`, `add`, and `status --all` through `exec.execFile`, `files`, `fs`, `lock`, `timer`, and `herdr`, refuses invalid arguments with exitCode 2, and throws `Error` when `command` is empty.

## Prompt tests

Scenario `test/runtime/autopilot-launcher-ports.json` covers `autopilotLaunchFingerprint`, `withAutopilotModeLock`, `requestAutopilotCompletion`, `tickAutopilot`, and `runAutopilotLauncher` with normal and error paths across all declared ports.
