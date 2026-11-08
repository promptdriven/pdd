# Read Codex account limits

Own `src/codex-limits.mjs`. Export async `readCodexLimits({command,cwd,env}, ports={})`
with `spawn` injectable. Start only command `app-server --listen stdio://` with
this exact environment. Exchange newline-delimited JSON: initialize id 1 with
clientInfo name pdd_health, title PDD health, version 1; after its successful
reply send initialized and account/rateLimits/read id 2. Send no other method,
including model, thread, turn, auth, logout, credit, purchase or reset methods.
Discard stderr. Stop this child after a response or failure; bound it to 10 seconds
and 1 MiB output. Never log or return raw messages, errors, credentials, account
identity, credit balances or reset-credit metadata. Export `parseCodexLimits(reply)`
for the same response normalization.

Return exactly `{state, resetAt, usedPercent}`. States are healthy, limited or
unknown; resetAt is epoch milliseconds or null; usedPercent is a number or null.
Use the codex bucket in rateLimitsByLimitId when present, else rateLimits.
A primary or secondary window at 100% or above blocks; a nonblank
rateLimitReachedType also blocks. Preserve a block with unknown reset time.
A window is valid only with finite usedPercent >=0; resetsAt may be null or a
finite nonnegative Unix seconds value within Date range. Missing windows with
no explicit reached type, malformed windows/bucket, protocol errors, missing
binary, timeout and early exit are unknown. Maximum used percent is returned.
Each parsed protocol frame must be a non-null, non-array object. A JSON null,
array or scalar is a protocol error: return unknown and stop the child without
throwing from the stream callback.
For reached windows return the latest reset (both must clear); if any has unknown
reset return null. A past reset timestamp alone never proves recovery: read the
account again. Unknown returns null metrics. Ignore all unrelated fields.

## Dependencies

Node child_process supplies a bounded subprocess transport. Protocol authority:
[official App Server reference](https://developers.openai.com/codex/app-server).
Only the initialization and rate-limit read protocol is required; no model call.
