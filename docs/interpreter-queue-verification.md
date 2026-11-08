# Verify machine interpreter admission

Use Node.js 22.16.0 or newer in a local checkout. No install step, hosted runtime,
GitHub credential, agent chat or model call is needed. Tests create temporary
repositories, profile folders and queue directories. Cleanup removes them.

Run:

```sh
node --test test/interpreter-queue.test.mjs test/interpreter-queue-runtime.test.mjs test/interpreter-queue-repair.test.mjs
node --test test/workflow-chat-queue.test.mjs
node --test --test-name-pattern='interpreter queue|interpreter waiting' test/autopilot-launcher.test.mjs test/workflow-runner.test.mjs
```

The runtime test calls the public `runCheck` boundary with the Harbor repository
fixture and the loopback fake runtime. Three distinct profile/state folders share
one queue. Hold two checks running. The third request waits at position 1 and sends
no POST. Release the fake results. All three checks finish; six request ledger rows
record the lint and check outcomes, timestamps and active counts of at most 2.

Other cases cover shared lint/check admission across origins, FIFO ordering,
interruption, dead waiting owners, unknown paid work, same-ID recovery, unreadable
ownership, busy back-off and recovery to the configured limit. Queue waits pause
the stuck clock without counting request execution time. Workflow text and JSON
show the waiting position without changing workflow progress.

Recovery cases expire or interrupt a locally waiting check, then retry its saved
batch from a new caller. Another case kills a native caller while a check waits
and recovers the batch in a new process. Unsent IDs receive no GET or POST.
A matching terminal `--request ID` read frees a retained slot; the next public
check can proceed. Invalid locks fail closed. Live lock contention stops ledger
mutations on interruption or within five seconds and keeps dispatch evidence.
Workflow tests execute generated start, resume and replacement shell commands
with stand-in agents under a missing or stale daemon environment. Queue settings
also reach Codex command environments, and workflow status reads the same queue.

Each machine queue ticket is also its request ledger row. Read
`readInterpreterProgress({cwd,env})` to obtain the ordered `requests` inventory.
An unknown observation can have an end time while its slot is still running;
that time marks when observation stopped, not proof that remote work ended.
Ledger rows contain no request body, credentials or response text. This native
verification uses controlled runtime replies. It does not prove hosted capacity
or prompt-interpreter behavior.
