# PDD state-to-exit table

Own `src/runtime-exit.mjs`: the fixed PDD mapping from Runtime check and lint outcome states to process exit codes, plus PDD's command/selection error exit code `2`. Pure module: no I/O, clock, network, or mutable state.

## Exit code table

Runtime decides each row state and the group `overall` state; PDD maps `overall` to the process exit code with this fixed table:

| Outcome or public state | Verdict | Exit code |
|---|---|---|
| `passed` | PASS | `0` |
| `failed` | FAIL | `1` |
| `unknown`, `waiting`, `sent`, `partial`, `queued`, `running` | NO VERDICT | `3` |
| `refused` | REFUSED | `4` |
| `not_run`, `not run` | NOT RUN | `5` |
| PDD command or test-selection error | none | `2` (`COMMAND_EXIT_CODE`) |

## Public contract

- Export frozen `STATE_EXIT_CODES`: `{ passed: 0, failed: 1, unknown: 3, waiting: 3, sent: 3, partial: 3, queued: 3, running: 3, refused: 4, not_run: 5, 'not run': 5 }`.
- Export `COMMAND_EXIT_CODE = 2`.
- Export pure `exitFor(value)`: accepts either a state string or a result object `{ overall }` (falling back to `value?.state`), and returns its integer exit code from `STATE_EXIT_CODES`, defaulting unrecognized or missing open states to `3`.
- Export pure `outcomeExitCode(outcomes, options, ports = {})` and alias `exitCodeFor(outcomes, options, ports = {})`: require `ports.outcomeOverall` (throwing an unbound-port `Error` when omitted) and return `exitFor(ports.outcomeOverall(outcomes, options))`.

## Dependencies

None.

## Caller navigation

[`src/runtime-seam.mjs`](runtime-seam.prompt.md) binds [`outcomeOverall`](runtime-outcome.prompt.md#progress-and-exit) on exported `outcomeExitCode` and `exitCodeFor`, and injects `exitFor` and `exitCodeFor` into [`src/runtime/`](runtime-entry.prompt.md).

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256":"0f45b02c33667f3b2b76a7981a979c33d151c9b3e205d52319949ed4f80f7f06","reason":"Provides PDD CLI exit-code constants and synchronous callback wrappers over Runtime outcome aggregation."}
```
</details>
