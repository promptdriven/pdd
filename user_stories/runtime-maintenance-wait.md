# Wait through runtime maintenance

I can leave a command waiting during announced maintenance and continue afterward.

## Acceptance criteria

1. Before submission, pdd reads authenticated runtime capacity; a maintenance window reports its end and reason, waits, then rechecks before sending.
2. A confirmed unstarted 503 maintenance response gets the same wait; capacity 404 permits compatibility through admission response codes.
3. Maintenance waiting shares the caller deadline and stops on interruption; authentication, access and unrelated service errors retain their existing handling.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local admission; the [client prompt](../prompts/cli/runtime-client.prompt.md) owns deadline, transport, restart and no-replay rules. Never turn missing evidence into permission to dispatch. Expected cases below come from DESIGN section 4 and E 1, before implementation.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-maintenance-wait.json) cover the normal path, limits, interruption and missing evidence. Run them through the real public commands with fake transport/clock and real temporary local state; process races need separate child processes.

Runtime check: NOT REPLAYED (#2548). The companion native case file records requirement-derived inputs and observations for code-step tests; it is not a prompt-runtime scenario. Real runCheck/runTry depend on native Git/source capture, private state, dispatch claims and process lifecycle without a complete Runtime interface. Injected HTTP/clock replies alone cannot establish this Story. Local exclusion, crash/permission behavior and concurrency need ordinary Node tests and separate processes. No Runtime call or pass is claimed.
