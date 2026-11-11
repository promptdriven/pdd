# Read Codex account limits

Own `src/codex-limits.mjs`. It owns the one read-only `codex app-server`
transport for a rate-limit read, so that callers share it and do not copy it.
Export async `readCodexRateLimitsReply({command,cwd,env,clientInfo}, ports={})`
(the transport), async `readCodexLimits({command,cwd,env}, ports={})` (the
health state) and `parseCodexLimits(reply)`. Both async exports take `spawn`
injectable in ports.

## Transport

`readCodexRateLimitsReply` starts only command `app-server --listen stdio://`
with this exact environment and cwd (`command` defaults to `codex`, `env` to
`process.env`). Exchange newline-delimited JSON: initialize id 1 with
`clientInfo` (default name pdd_health, title PDD health, version 1); after its
successful reply send initialized and account/rateLimits/read id 2 with no
params. Send no other method, including model, thread, turn, auth, logout,
credit, purchase or reset methods.
Discard stderr. Stop this child after a response or failure; bound the exchange to
10 seconds and 1 MiB output. End its input and send SIGTERM, then wait for the
child's close before returning the selected result, with at most 1 second for
cleanup after selecting that result. After 500 milliseconds, send SIGKILL if
the direct child has not exited. If close still has not arrived after another
500 milliseconds, destroy this connection's stdin, stdout and stderr, unref the
child and return the selected result. A descendant holding an inherited pipe
must not prevent completion. An already closed child or a failed spawn needs no
stop. This allows ordinary shutdown effects to complete while keeping failed
health observations finite.
Each parsed protocol frame must be a non-null, non-array object. A JSON null,
array or scalar is a protocol error: stop the child without throwing from the
stream callback. The transport never throws or rejects.

It returns exactly one of these fresh objects; the first failure wins:

| Result | When |
|---|---|
| `{ok: true, reply}` | The id 2 response has no `error`. `reply` is its `result` value as parsed (undefined when absent). |
| `{ok: false, reason: 'spawn'}` | spawn throws, or the child emits `error`. |
| `{ok: false, reason: 'exit'}` | The child closes, or its input fails, before the id 2 response. |
| `{ok: false, reason: 'timeout'}` | No id 2 response within 10 seconds. |
| `{ok: false, reason: 'output'}` | stdout plus stderr pass 1 MiB. |
| `{ok: false, reason: 'protocol'}` | A frame is not JSON or not an object, or the initialize result is not an object. |
| `{ok: false, reason: 'error'}` | The initialize or the read response has `error`. |

The transport never logs anything and never returns stderr, raw messages or
error text. The caller owns what it keeps from `reply`; `reply` can hold account
identity and reset-credit metadata, so a caller must not log or save it raw.

## Health state

`readCodexLimits` calls the transport with only `{command,cwd,env}` (the default
clientInfo). It returns `parseCodexLimits(reply)` for `ok: true` and the unknown
state for every failure. Never log or return raw messages, errors, credentials,
account identity, credit balances or reset-credit metadata.

Return exactly `{state, resetAt, usedPercent}`. States are healthy, limited or
unknown; resetAt is epoch milliseconds or null; usedPercent is a number or null.
Use the codex bucket in rateLimitsByLimitId when present, else rateLimits.
A primary or secondary window at 100% or above blocks; a nonblank
rateLimitReachedType also blocks. Preserve a block with unknown reset time.
A window is valid only with finite usedPercent >=0; resetsAt may be null or a
finite nonnegative Unix seconds value within Date range. Missing windows with
no explicit reached type, malformed windows/bucket, protocol errors, missing
binary, timeout and early exit are unknown. Maximum used percent is returned.
For reached windows return the latest reset (both must clear); if any has unknown
reset return null. A past reset timestamp alone never proves recovery: read the
account again. Unknown returns null metrics. Ignore all unrelated fields.

## Dependencies

Node child_process supplies a bounded subprocess transport. Protocol authority:
[official App Server reference](https://developers.openai.com/codex/app-server).
Only the initialization and rate-limit read protocol is required; no model call.
The [login usage read](accounts-usage.prompt.md) uses the transport with its own
clientInfo.
