# Ticket status label

Convert a supplied ticket status into a display label. This synthetic module owns label selection only; it does not render a UI, change tickets or fetch status data.

Preserve the existing JavaScript module function `statusLabel(status)` exported by `src/status.mjs`: one supplied value produces a string or throws `TypeError` as below. There are no external effects or runtime dependencies. Internal implementation choices may vary.

## Label rules

Matching is exact and case-sensitive. Do not trim, normalize or coerce an input: unknown spelling should remain visible as unknown rather than silently claim a known state.

| Supplied value | Result |
| --- | --- |
| Exact string `open` | `Open` |
| Exact string `blocked` | `Blocked` |
| Exact string `done` | `Done` |
| Any other string, including empty or whitespace-only text | `Unknown` |
| `null` | `Unknown` |
| Any other JavaScript value, including a missing argument (`undefined`) | Throw `TypeError` |

`null` explicitly represents an unknown status. Other non-string values are outside this function's input domain; never stringify them or call their conversion hooks. The error class is required; its message is not part of this contract.

## Dependencies

None. This module uses only JavaScript language facilities.
