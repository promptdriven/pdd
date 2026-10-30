# Keep a truthful interruption message during recovery

I can stop or retry a check and trust both its message and its saved execution evidence.

## Acceptance criteria

1. If I stop a check after its request is recorded but before it is sent, I see "Stopped before sending." for that attempt; saved request recovery still prevents another send and keeps uncertain usage unknown until a matching result is available.
2. Two overlapping retries of the same saved batch send exactly one new check, keep its result and four AI calls, and refuse the competing command even when local bookkeeping creates extra IDs.
3. A confirmed busy check can try admission more than three times while my wait remains; a deadline or interruption ends waiting, and a lost answer or fresh refusal cannot reuse earlier busy/retry advice.

## Rules to check

The [client prompt](../prompts/cli/runtime-client.prompt.md#interruption-note-precedence) owns message precedence, same-ID recovery, accounting and retry authority. The [slots prompt](../prompts/cli/runtime-slots.prompt.md) continues to own reservation identity and release. Fresh knowledge about this invocation's unsent request preserves its note only. It cannot erase earlier submissions, make unknown usage zero or authorize replay. A saved note or phase alone proves none of those facts; a later verified matching receipt supplies the current result.

Synchronize interruption after durable claim/request recording and before the actual POST. Check the note together with claim adoption, no new POST, unchanged IDs/accounting and retained earlier uncertain leases. Older ambiguous saves must recover the same ID with no new send. A later matching terminal receipt with 17/17 checks, four passed criteria and four AI calls must replace uncertainty with those facts.

For overlapping retries, measure actual check POSTs and their paid request identity. Extra local IDs do not count as paid work; the losing live competitor still allocates no IDs and makes no GET, POST or save. Preserve the receipt and accounting in a later batch read.

Confirmed unstarted capacity may retry without an attempt ceiling inside the caller deadline. Cover more than three attempts, finite timeout and interruption without fixing a final attempt count. Lost or unverifiable execution permits only same-ID reads; fresh refusal keeps its own reason and exit. Neither may inherit busy/retry eligibility or stale advice. Preserve receipts, existing exit codes and secret redaction.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-interruption-recovery.json) keep each case's inputs and expected observations separate from code output. Replay through the public Check boundary with fake transport/clock and real temporary private state; synchronize native claim and interruption effects.

Runtime check: NOT REPLAYED (#2548). Check source capture, durable dispatch claims, batch ownership, slots and process interruption lack a complete bound Runtime interface. The companion is pdd.native-cases.v1, not an executable prompt-runtime scenario. No synthetic interface, Runtime call or pass is claimed; ordinary Node tests must establish these effects in the code step.
