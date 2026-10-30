# Wait through runtime congestion

I can leave my command waiting for runtime capacity within its existing wait.

## Acceptance criteria

1. After more than 3 confirmed unstarted capacity refusals, Check, remote lint and Try setup can still finish within their caller wait.
2. pdd spaces capacity retries by Retry-After within the caller deadline and interruption rules.
3. An accepted queued job is read by its original request ID, with its supplied queue place and busy slots shown as progress.
4. pdd never resends a check for capacity when it may have started.
5. The lint wait limit also bounds dead-owner reads and saving a request ID before submission, including the 90-second agent lint wait during Try setup.
6. When my lint wait ends for a local slot or maintenance, pdd names that wait and does not claim that the server stayed busy after 0 lint attempts.
7. Submissions by the same authenticated owner at the same runtime reuse a clear capacity observation for about 10 seconds.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local admission; the [client prompt](../prompts/cli/runtime-client.prompt.md) owns deadline, transport, restart and no-replay rules. Never turn missing evidence into permission to dispatch.

After admission and before submission, interruption says "Stopped before sending." and sends no new request; uncertain earlier dispatches keep their leases. A capacity observer with a timeout beyond the native timer range retains its own deadline and interruption while the shared read remains usable by other callers; timer overflow, rapid polling and a false unclear-capacity warning are forbidden. Check causal order, no resend and termination with controlled boundaries and generous watchdogs, rather than small elapsed-time limits.

Unclear capacity responses and read failures reuse an explicitly unclear outcome for about 10 seconds, coalesced and isolated by authenticated owner and exact runtime origin. Each command warns once and follows ordinary admission; expiry permits a fresh read to announce maintenance. Cache reuse never establishes clear capacity or authorizes replay of an uncertain job.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-capacity-wait.json) cover the normal path, limits, interruption and missing evidence. Run them through the real public commands with fake transport/clock and real temporary local state; process races need separate child processes.

Runtime check: NOT REPLAYED (#2548). The companion native case file records requirement-derived inputs and observations for code-step tests; it is not a prompt-runtime scenario. Real runCheck/runTry depend on native Git/source capture, private state, dispatch claims and process lifecycle without a complete Runtime interface. Injected HTTP/clock replies alone cannot establish this Story. Local exclusion, crash/permission behavior and concurrency need ordinary Node tests and separate processes. No Runtime call or pass is claimed.
