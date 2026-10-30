# Send selected jobs without a default limit

I can send all my selected checks and let the server decide capacity, while choosing a shared local cap when I need one.

## Acceptance criteria

1. With PDD_MAX_JOBS unset, all 7 selected checks reach the server before any check finishes, without a local-slot wait.
2. With PDD_MAX_JOBS=2, at most 2 jobs run at once, including jobs from two local processes sharing the same state folder and runtime host.
3. An invalid PDD_MAX_JOBS value prints one warning line per command and imposes no cap.
4. A confirmed busy refusal honors Retry-After and existing minimum waits, retries only the unstarted check with a new request ID, reduces the check dispatch window to 1 and never replays accepted work.
5. With no cap, remote lint and Try setup proceed past existing active leases and older waiting tickets without a local-slot wait; request records, ownership and uncertain-job evidence remain intact.

## Rules to check

No environment value means no fixed default cap. Positive safe decimal integers select a cap; zero, negatives, fractions, whitespace, leading zeros, text and unsafe integers warn once and select no cap. The forbidden result is local capacity or FIFO waiting without an explicit cap. No cap must preserve durable reservation registration, heartbeat ownership and the existing ended/uncertain lease rules. Server maintenance, refusal evidence, busy waits and duplicate-dispatch protection remain authoritative.

## Native cases for the code step

[Native cases](../test/runtime-admission/runtime-no-default-limit.json) describe fake-runtime barriers, shared-process cap preservation and refusal recovery.

Runtime check: NOT REPLAYED; native Git capture, shared filesystem ownership, process concurrency and dispatch timing lack a complete Runtime interface. Ordinary Node tests use a fake runtime; no Runtime call or AI pass is claimed.
