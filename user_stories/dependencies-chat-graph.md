# Read the graph from chat

I can ask to see the graph, why an issue waits, or what has no recorded blocker.

## Acceptance criteria

1. A cached graph is returned before the GitHub refresh finishes; reading it schedules only a read refresh and makes no AI or GitHub mutation call.
2. The text summary and selected issue explanation use the same saved graph and preserve current, stale, offline and unknown facts.
3. A headless open request gives the exact laptop command for the selected repository and issue, and invokes no VM opener.
4. A local open request invokes the bundled viewer. No cache gives an honest empty state, and an offline or partial refresh preserves the last successful graph and sync time.

## Rules to check

Read/open/detail/background refresh must use no AI or GitHub mutation. The cache cannot confer authority or prove scheduling room. A VM opener cannot establish laptop opening. Native wiring, opener invocation and real browser rendering remain separate checks.
