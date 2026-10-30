# Wait my turn locally

I can see my place while other local agents use the runtime.

## Acceptance criteria

1. Each waiting job keeps one ticket in oldest-first order for the next free local slot.
2. While I wait, pdd reports the local busy count, limit and number ahead of me.
3. Interruption or the caller deadline removes my waiting ticket without submitting its job.
4. A waiting ticket or claim abandoned for 60 seconds cannot block my turn when its process ID has been reused.
5. Only the first waiting ticket competes for a free slot; twelve contenders with three slots make progress without a contention stall.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local admission; the [client prompt](../prompts/cli/runtime-client.prompt.md) owns deadline, transport, restart and no-replay rules. Never turn missing evidence into permission to dispatch.

A forward wall-clock jump of more than 60 seconds before my next heartbeat cannot erase my own waiting ticket or change its identity, original order or ability to take the next slot. Other abandoned owners remain reclaimable. Contention checks prove oldest-first progress, the active limit and eventual completion with a generous watchdog; a busy runner must not fail merely for exceeding a small elapsed-time target.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-local-queue.json) cover the normal path, limits, interruption and missing evidence. Run them through the real public commands with fake transport/clock and real temporary local state; process races need separate child processes.

Runtime check: NOT REPLAYED (#2548). The companion native case file records requirement-derived inputs and observations for code-step tests; it is not a prompt-runtime scenario. Real runCheck/runTry depend on native Git/source capture, private state, dispatch claims and process lifecycle without a complete Runtime interface. Injected HTTP/clock replies alone cannot establish this Story. Local exclusion, crash/permission behavior and concurrency need ordinary Node tests and separate processes. No Runtime call or pass is claimed.
