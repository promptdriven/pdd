# Wait my turn locally

I can see my place while other local agents use the runtime.

## Acceptance criteria

1. The oldest live waiting job takes the next free local slot, and each waiting job keeps one ticket.
2. While I wait, pdd reports the local busy count, limit and number ahead of me.
3. Interruption or the caller deadline stops my waiting job without dispatching it or leaving a live waiting ticket.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local admission; the [client prompt](../prompts/cli/runtime-client.prompt.md) owns deadline, transport, restart and no-replay rules. Never turn missing evidence into permission to dispatch. Expected cases below come from DESIGN section 4 and E 1, before implementation.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-local-queue.json) cover the normal path, limits, interruption and missing evidence. Run them through the real public commands with fake transport/clock and real temporary local state; process races need separate child processes.

Runtime check: NOT REPLAYED (#2548). The companion native case file records requirement-derived inputs and observations for code-step tests; it is not a prompt-runtime scenario. Real runCheck/runTry depend on native Git/source capture, private state, dispatch claims and process lifecycle without a complete Runtime interface. Injected HTTP/clock replies alone cannot establish this Story. Local exclusion, crash/permission behavior and concurrency need ordinary Node tests and separate processes. No Runtime call or pass is claimed.
