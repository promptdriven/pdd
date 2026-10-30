# Recover one runtime restart

I can recover a check interrupted by a confirmed runtime restart once while retaining its history.

## Acceptance criteria

1. Only a same-ID check ending unknown with service-restarted permits a replacement with a fresh attempt ID and the original source and call ceiling.
2. Each Story row gets at most one replacement across repeated or concurrent saved reads and retries.
3. Recovery preserves both attempts' request IDs, receipts and known or unknown usage.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local admission; the [client prompt](../prompts/cli/runtime-client.prompt.md) owns deadline, transport, restart and no-replay rules. Never turn missing evidence into permission to dispatch.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-restart-retry.json) cover the normal path, limits, interruption and missing evidence. Run them through the real public commands with fake transport/clock and real temporary local state; process races need separate child processes.

Runtime check: NOT REPLAYED (#2548). The companion native case file records requirement-derived inputs and observations for code-step tests; it is not a prompt-runtime scenario. Real runCheck/runTry depend on native Git/source capture, private state, dispatch claims and process lifecycle without a complete Runtime interface. Injected HTTP/clock replies alone cannot establish this Story. Local exclusion, crash/permission behavior and concurrency need ordinary Node tests and separate processes. No Runtime call or pass is claimed.
