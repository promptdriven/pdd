# Shared full-suite queue

Own `src/test-suite-queue.mjs` and the compatibility entrypoint
`scripts/vm-suite-lock.sh` and `src/test-suite-entry.mjs`. This queue bounds full-suite resource use for all
repositories and parallel workflow runs on one machine. It runs only an explicit
operator or worker command; it does not schedule tests or approve publication.

## Queue and execution

Export `suiteQueueRoot(env = process.env)`, returning the shared absolute queue
path selected below, or throwing for a relative path. Export
`suiteStatusWords(suite)`, returning one status line for the public status shape:
waiting with position, running, failure with reason, successful completion, or
queue unavailable with its cause.

Export native port adapter `executeSuite(command, {cwd, env, timeoutMs, onChild})`,
which resolves `{exitCode, reason}` after child cleanup.

Export `runTestSuite({cwd, command, timeout = 30, env}, ports = {})`, returning
`{exitCode, message}`, and synchronous `readSuiteProgress({cwd, since = 0, env},
ports = {})`. The latter returns null without records, else `{ticket, state, position,
queuedAt, startedAt, finishedAt, reason, pausedMs}`. `ticket` is the positive submission sequence number. Times are epoch milliseconds;
absent start/end times are null, position is a positive integer only while
waiting (otherwise null), reason is null unless a failed or interrupted suite.
`pausedMs` is the union of suite intervals after `since` and before now.
If queue selection, directory reading or any ownership record cannot be read,
return `{state: "unavailable", reason, pausedMs: 0}` instead of throwing or
returning null. `reason` retains the read error message. This state means unknown
queue activity, never a failed suite or evidence of inactivity. Do not mutate
records during observation; retry on the next read. Admission still fails closed.

Use one shared local queue independent of repository, worktree, HOME and agent
profile. Default to `/tmp/pdd-full-suite-UID`, with the operating system user ID.
An explicit absolute `PDD_SUITE_QUEUE` selects a shared directory; the compatibility
`PDD_VM_SUITE_LOCK` selects `VALUE.queue` when the first variable is absent.
Reject relative paths, blank commands and invalid timeouts before execution.
Timeout is an integer of 1 to 120 minutes, default 30, measured only after admission.
The compatibility script accepts `--check` without executing, uses `SUITE` when
nonblank, otherwise `POCKET_BROWSER_BIN=/usr/bin/google-chrome npm test`, and
returns the child's status. Preserve the compatibility queued/started/finished
log lines and history file at `PDD_VM_SUITE_LOCK.history`, else
`HOME/.local/state/pdd/vm-suite/fullsuite.lock.history`. An explicit legacy lock
path still needs an existing writable parent; the default log parent is created. No GitHub writes, private paths or live agent calls.

Admit at most three running suites. Serialize ticket creation and admission with
the existing PID/token lock semantics. Preserve submission order among waiting
tickets, including equal clock times; every waiter ahead contributes to position.
Do not hold admission ownership during a suite or a wait. All test commands,
including custom full suites, run in the supplied cwd with the supplied env and
closed stdin. Preserve child stdout, stderr and nonzero status. A running suite
has a bounded timeout; terminate its process group before releasing its slot.
Timeout returns 124 with a suite-specific reason. On SIGINT/SIGTERM, terminate
running descendants and release only after termination. Dead waiters do not block
the queue. A dead runner with a live or uncertain suite keeps its slot and reports the
interrupted runner with uncertain descendant ownership as its reason. Never kill
an unrelated process or reclaim a live or uncertain owner. Unknown or unreadable
queue ownership fails closed; it cannot admit extra suites.

Persist waiting, running and completed records atomically outside the checkout.
Record only ticket, owner PID, child PID when known, cwd, state, timestamps and
failure reason, never the command, environment or output. Report changed queue
positions as `waiting for a test slot (position N)`. Retain completed intervals
so the stuck clock excludes queue wait and suite execution after restart. Status
is read-only and must not mutate workflow state or touch a live chat. A successful
suite resumes the prior stuck clock, rather than consuming it. A suite failure,
timeout or interrupted runner has its own reason; it is not a stuck issue.

## Dependencies

- [Native admission lock](workflow-runner.prompt.md#native-admission-lock): only this
  independent interface selection is required context, supplying
  `acquireRunLock` for PID/token admission ownership. No runner execution policy
  is loaded by this selection.
- Native Node filesystem, OS, child process and clock facilities implement ports.
- Inject `fs`, `now`, `sleep`, `alive(pid)`, `acquireLock(directory)`,
  `execute(command, {cwd, env, timeoutMs, onChild})`, `pid`, `uuid()` (temporary-file identity), `queueRoot`, and
  `say(text)` to fake outside effects. Execute resolves `{exitCode, reason}` and
  calls `onChild(pid)` before awaiting the suite. Native defaults handle signals
  and process-group termination. Status uses the same filesystem, clock and PID
  liveness ports; an unavailable queue read is explicit, never idle evidence.
