# Wait through runtime congestion

I can leave my command waiting for runtime capacity within its existing wait.

## Acceptance criteria

1. After more than 3 confirmed unstarted capacity refusals, Check, remote lint and Try setup can still finish within their caller wait.
2. pdd spaces capacity retries by Retry-After within the caller deadline and interruption rules.
3. An accepted queued job is read by its original request ID, with its supplied queue place and busy slots shown as progress.
4. pdd never resends a check for capacity when it may have started.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local admission; the [client prompt](../prompts/cli/runtime-client.prompt.md) owns deadline, transport, restart and no-replay rules. Never turn missing evidence into permission to dispatch.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-capacity-wait.json) cover the normal path, limits, interruption and missing evidence. Run them through the real public commands with fake transport/clock and real temporary local state; process races need separate child processes.

Runtime check: NOT REPLAYED (#2548). The companion native case file records requirement-derived inputs and observations for code-step tests; it is not a prompt-runtime scenario. Real runCheck/runTry depend on native Git/source capture, private state, dispatch claims and process lifecycle without a complete Runtime interface. Injected HTTP/clock replies alone cannot establish this Story. Local exclusion, crash/permission behavior and concurrency need ordinary Node tests and separate processes. No Runtime call or pass is claimed.
