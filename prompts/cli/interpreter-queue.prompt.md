# Machine interpreter queue

Own `src/interpreter-queue.mjs`. Bound simultaneous lint and check requests across
repositories, worktrees, runtime hosts and agent profiles of one OS user. This
queue owns machine capacity and request measurements. Existing runtime slots own
profile leases; the runtime client alone owns dispatch and safe retry authority.

Use the shared full-suite queue design: ordered persistent tickets, atomic record
replacement and the native PID/token admission lock. Never hold the lock across
network work or sleep. Default directory is `/tmp/pdd-interpreter-UID`; an absolute
`PDD_INTERPRETER_QUEUE` overrides it. `PDD_INTERPRETER_CONCURRENCY` is a positive safe
integer, default 2. Invalid capacity uses 2 with a warning. A relative directory
or unreadable queue fails closed before POST. An admission lock with malformed,
non-regular, unreadable or unverifiable PID/token ownership fails immediately with
`local-state-unavailable`; never steal it. Only verified live contention may wait.
Lock creation or storage failure fails promptly with `local-state-unavailable`.
An absent lock after contention can mean that its holder released it: retry only
while the root is still a regular directory. Every lock retry yields and checks
interruption and the caller deadline; each admission-lock wait is bounded by five
seconds, including repeated release races. Capacity waiting keeps its own caller
deadline and is not limited to five seconds.
Dispatch marking and observation try an uncontended update even during cleanup,
but stop waiting on interruption or deadline, and within five seconds otherwise.
A cancelled dispatch mark forbids POST. A failed observation keeps the prior
dispatch evidence and capacity for later same-ID recovery. Keep state outside
the checkout,
private to the OS user; never save credentials, request bodies or response prose.

Export `interpreterQueueEnvironment(env)` returning the effective
`PDD_INTERPRETER_QUEUE` and `PDD_INTERPRETER_CONCURRENCY` as strings under the
settings above, so workflow launch and status use the same queue.

Export `acquireInterpreterSlot({cwd, origin, requestId, kind, env, deadline}, ports)`
for lint/check only. Return `{root,ticket}` after admission, or null at deadline or
interruption. `deadline` is absolute epoch milliseconds, Infinity by default.
Register a waiting ticket, then admit the oldest live waiter when active count is
below capacity and the shared busy pause has ended. Position counts waiting tickets
including this one, from 1. Report changed positions as
`waiting for an interpreter slot (position N)`. End and retain unsent waiters on
cancellation. At every admission attempt, under the admission lock, check PID
liveness for all waiting and running tickets. Finish and persist tickets with a
confirmed dead owner, including dispatched holders, before counting capacity or
FIFO position. Set `releaseReason: "owner-dead"`, `endedAt` to the cleanup time,
and `activeAtEnd` to the running count before that release. Keep ticket identity,
dispatch evidence, start measurements and any observed outcome. Without an
observed outcome, use `unknown` for dispatched tickets and `not_sent` for unsent
tickets. PID permission errors or uncertain liveness do not prove death.
A live dispatched request without a terminal receipt retains capacity after
interruption. Releasing a dead owner's local capacity never authorizes a resend
or infers a verdict. Duplicate request identities remain refused. Later terminal
same-ID evidence may replace a reclaimed dispatched ticket's unknown outcome once, without releasing
capacity again or replacing its release reason and measurements.

Export `observeInterpreterRequest({env,origin,requestId,outcome,terminal,busy,waitMs}, ports)`.
Outcomes are `verdict`, `unknown`, `refused`, `busy`, or `not_sent`. Record each
observation for that exact request only. Terminal evidence releases its machine
slot; lost responses and stopped polling record unknown and retain it. Recovery
by the same saved ID can finish a retained ticket. Repeated terminal observations
are idempotent. Busy feedback (`busy:true`, including uncertain capacity replies) halves the
shared effective cap, minimum 1, for 60 seconds and pauses new admissions for the
server wait clamped to 1 through 60 seconds (default 5 seconds). Uncertain feedback
never authorizes replay or releases capacity. After the 60-second window, each
successful verdict increases capacity by one up to the configured limit. A refusal
or unknown never increases it. Each caller's configured limit is also a hard cap.

Persist one request ledger row per ticket. Fields are `ticket` (positive sequence),
`pid`, `cwd` (absolute worktree), `origin`, `requestId`, `kind` (lint/check), `state`
(waiting/running/finished), `queuedAt`, `startedAt`, `endedAt` (epoch milliseconds;
start/end null until observed), `outcome` (above or null), `activeAtStart`,
`activeAtEnd` (nonnegative request counts, start includes this request; end counts
before releasing it), and `dispatched` (whether POST may have started). An optional `releaseReason`
is `owner-dead` only when admission reclaimed a dead owner; older rows omit it. Expose
`markInterpreterDispatch({root,ticket}, ports)` before POST. A failed mark forbids
POST. Preserve unknown observations and permit later confirmed completion to
replace them. Admission and all terminal ledger writes are serialized. An error
before dispatch finishes an unsent ticket. No durable dispatch record is retried.

Export `readInterpreterProgress({cwd,since=0,env}, ports)` returning null without
records, else `{state,position,pausedMs,requests}`. `requests` are ledger rows for
that cwd in ticket order. `state` and `position` describe the earliest waiting ticket, otherwise the earliest unfinished
ticket (position null unless waiting), else finished. `pausedMs` is the union of
waiting intervals clipped to since/now; running time is excluded. A dead waiter
ends at its record mtime. Observation is read-only. Unreadable state returns
`{state:"unavailable",reason,pausedMs:0,requests:[]}`. Unknown state never proves
inactivity. Export `interpreterStatusWords(progress)` for waiting, running,
finished or unavailable status. Stuck detection excludes saved wait intervals and
never declares an actively waiting or unreadable queue stuck. Workflow status
shows the waiting words in text and its `words` JSON field without waking a chat.

## Autopilot test mode

Export configureInterpreterTestMode({env,owner,enabled},ports). Use the same queue admission lock and capacity file. Keep a map testOwners of owner paths to lease expiry timestamps; enabling renews a one-hour lease and disabling removes only this owner. Admission has limit one while any lease is current. A terminal verdict clears the leases so ordinary interpreter capacity returns immediately. Preserve the busy cooldown and unknown-result ownership. The tick calls this only after its three-no-verdict pattern, never after one failure. Reuse injected filesystem, clock, PID and lock ports. No second queue.

## Dependencies

- [Native admission lock](workflow-runner.prompt.md#native-admission-lock): required
  independent binding for `acquireRunLock(directory, filename)`; no workflow
  execution policy is required.
- Native Node filesystem, path, PID liveness, clock and UUID facilities supply
  defaults. Inject `fs`, `now`, `sleep`, `alive`, `pid`, `uuid`, `acquireLock`,
  `interrupted` and `say` for controlled local behavior. Admission checks the
  deadline and interruption before each update and after lock acquisition.
