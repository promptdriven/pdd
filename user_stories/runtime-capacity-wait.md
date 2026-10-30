# Wait through runtime congestion

I can leave my command waiting for runtime capacity within its existing wait.

## Acceptance criteria

1. After more than 3 confirmed unstarted capacity refusals, Check, remote lint and Try setup can still finish within their caller wait.
2. pdd honors Retry-After between confirmed capacity attempts and stops sending at the caller deadline or interruption.
3. An accepted queued job keeps its request ID; pdd reports its supplied queue place and busy slots without resubmitting it.
4. Lost replies, mismatched receipts, evaluated checks, positive or unknown calls and incomplete accounting never authorize a capacity retry.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local admission; the [client prompt](../prompts/cli/runtime-client.prompt.md) owns deadline, transport, restart and no-replay rules. Never turn missing evidence into permission to dispatch. Expected cases below come from DESIGN section 4 and E 1, before implementation.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-capacity-wait.json) cover the normal path, limits, interruption and missing evidence. Run them through the real public commands with fake transport/clock and real temporary local state; process races need separate child processes.

Runtime check: NOT REPLAYED (#2548). The companion native case file records requirement-derived inputs and observations for code-step tests; it is not a prompt-runtime scenario. Real runCheck/runTry depend on native Git/source capture, private state, dispatch claims and process lifecycle without a complete Runtime interface. Injected HTTP/clock replies alone cannot establish this Story. Local exclusion, crash/permission behavior and concurrency need ordinary Node tests and separate processes. No Runtime call or pass is claimed.
