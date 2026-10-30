# Wait through runtime maintenance

I can leave a command waiting during announced maintenance and continue afterward.

## Acceptance criteria

1. Before submission, pdd reads authenticated runtime capacity and waits through announced maintenance, showing its local end time with the zone and its reason before rechecking.
2. When the server confirms that maintenance prevented a job from starting, pdd uses the same maintenance wait and notice.
3. A runtime without the capacity endpoint can still accept work under its ordinary submission rules.
4. Maintenance waiting obeys the caller deadline and interruption.
5. Authentication, access and unrelated service errors retain their existing handling.
6. Even when maintenance ends more than 24.8 days away, pdd waits at most 60 seconds at a time and stays responsive without rapid polling or repeated unchanged notices.
7. An unrecognized capacity response or read failure prints one warning and continues with ordinary admission rules; only clear future maintenance creates a maintenance wait.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local admission; the [client prompt](../prompts/cli/runtime-client.prompt.md) owns deadline, transport, restart and no-replay rules. Never turn missing evidence into permission to dispatch.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-maintenance-wait.json) cover the normal path, limits, interruption and missing evidence. Run them through the real public commands with fake transport/clock and real temporary local state; process races need separate child processes.

Runtime check: NOT REPLAYED (#2548). The companion native case file records requirement-derived inputs and observations for code-step tests; it is not a prompt-runtime scenario. Real runCheck/runTry depend on native Git/source capture, private state, dispatch claims and process lifecycle without a complete Runtime interface. Injected HTTP/clock replies alone cannot establish this Story. Local exclusion, crash/permission behavior and concurrency need ordinary Node tests and separate processes. No Runtime call or pass is claimed.
