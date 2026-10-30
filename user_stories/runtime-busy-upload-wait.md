# Wait before uploading a busy check again

I can leave my check waiting for room without repeatedly uploading the same files while the runtime is busy.

## Acceptance criteria

1. When the runtime confirms a busy check never started, I can keep waiting without a fixed attempt limit, with at least 10 seconds between busy uploads and any longer server delay respected.
2. When Check capacity is usable and full, my next upload waits for a free Check slot or 60 seconds from the busy answer, while still respecting the minimum delay.
3. If capacity information is unsupported, absent or unusable, my check can try again after the minimum delay without treating missing information as free capacity.
4. A deadline, Ctrl-C, maintenance or an access refusal prevents further uploads even when the capacity hold would otherwise end.
5. Reading or explicitly retrying my saved batch preserves the original retry times, selected files, request history and call limits.
6. A check that may have started is recovered by its original request ID and is never replayed as a busy check.

## Rules to check

The [client prompt](../prompts/cli/runtime-client.prompt.md#check-admission-and-confirmed-capacity-recovery) owns retry authority, timing and precedence; its [shared admission](../prompts/cli/runtime-client.prompt.md#shared-local-admission-and-maintenance) owns capacity reads/cache and maintenance. The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local exclusion and reservation cleanup. Apply this new timing only to Check uploads after authoritative confirmed-unstarted capacity evidence, including explicit batch retry.

With unsupported capacity and one-second server advice, a 90-second finite wait allows more than three uploads and at most ten, spaced at least ten seconds apart; this bound is a fixture consequence, never a global attempt limit. Longer advice remains binding even after the capacity hold ends. Waiting alone cannot create another check request or upload; capacity GETs cannot run under a local claim lock. Saved reads/retries cannot reset either absolute time or authorize replay from missing proof.

Preserve source identity, original call ceilings, receipt/accounting history, truthful interruption messages and existing exits/JSON. Lint/Try keep their existing waits. Assert public POSTs, their IDs and receipts rather than total bookkeeping UUIDs or an exact capacity GET count.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-busy-upload-wait.json) separate causal input from expected observations. Replay through public Check/read/retry with fake transport/clock and real temporary private state; native claim/process effects need ordinary code-step tests.

Runtime check: NOT REPLAYED (#2548). Source capture, saved batch ownership, durable claims and interruption lack a complete bound Runtime interface. The pdd.native-cases.v1 companion is not an executable prompt-runtime scenario; no Runtime call or pass is claimed.
