# Shared full-suite queue

Own `src/test-suite-queue.mjs` and the compatibility entrypoint
`scripts/vm-suite-lock.sh`, `src/test-suite-entry.mjs` and the detached native
recorder `src/test-suite-recorder.mjs`, validation state selection in
`scripts/vm-suite.sh`, and evidence adapter
`src/validation-evidence.mjs`. This queue bounds full-suite resource use for all
repositories and parallel workflow runs on one machine. It runs only an explicit
operator or worker command; it does not schedule tests or approve publication.

## Queue and execution

Export `suiteQueueRoot(env = process.env)`, returning the shared absolute queue
path selected below, or throwing for a relative path. Export
`suiteStatusWords(suite)`, returning one status line for the public status shape:
waiting with position, running, failure with reason, successful completion, or
queue unavailable with its cause.

Export native port adapter `executeSuite(command, {cwd, env, timeoutMs, onChild, onOutput, startGate = false, cpuIds, taskset}, ports = {})`,
which resolves `{exitCode, reason, signal, ownershipConfirmed}` after child cleanup.
`ownershipConfirmed` is Boolean: false if a bounded cleanup cannot establish that
all owned group members have stopped. Such a receipt retains state running,
outcome unknown, null exit/counts and its environment; it keeps its reservation.
Native cleanup probes its own process group for up to two seconds after SIGKILL.
Linux zombie members are stopped; unreadable observations are uncertain. Inject
`groupAlive(pgid)` (Boolean or null for uncertain), `kill(pid, signal)`
(negative owned process group), and `sleep(ms)` for this check. `signal` is null
or the termination signal on a closed child, and absent on a spawn error.
Optional `onOutput(stream, bytes)` receives raw stdout/stderr buffers; without it,
output inherits the caller streams. `startGate` blocks command execution until
`onChild(pid)` succeeds, then supplies EOF on command stdin.

Export `runTestSuite({cwd, command, timeout, env}, ports = {})`, returning
`{exitCode, message}`, and synchronous `readSuiteProgress({cwd, since = 0, env},
ports = {})`. The latter returns null without records, else `{ticket, state, position,
queuedAt, startedAt, finishedAt, reason, pausedMs}`. `ticket` is the positive submission sequence number. Times are epoch milliseconds;
absent start/end times are null, position is a positive integer only while
waiting (otherwise null), reason is null unless a failed or interrupted suite.
`pausedMs` is the union of suite intervals after `since` and before now.
If queue selection, directory reading or any ownership record cannot be read,
return `{state: "unavailable", reason, pausedMs: 0}` instead of throwing or
returning null. `reason` retains the secret-safe, byte-bounded read error message. This state means unknown
queue activity, never a failed suite or evidence of inactivity. Do not mutate
records during observation; retry on the next read. Admission still fails closed.

Use one shared local queue independent of repository, worktree, HOME and agent
profile. Default to `/tmp/pdd-full-suite-UID`, with the operating system user ID.
An explicit absolute `PDD_SUITE_QUEUE` selects a shared directory; the compatibility
`PDD_VM_SUITE_LOCK` selects `VALUE.queue` when the first variable is absent.
Reject relative paths, blank commands and invalid timeouts before execution.
Explicit `timeout` is an integer of 1 to 120 minutes, measured only after admission.
When `timeout` is omitted, learn the limit from this machine's recent successful
suite durations for the repository in the [cost ledger](cost-ledger.prompt.md)
(`2x` the median of the last 5 successful suite durations, rounded up to whole
minutes, with a floor of 5 minutes, a ceiling of 120 minutes, and a 30-minute
fallback when no successful suite duration is recorded). Store `timeoutMinutes`
on the ticket and record each completed suite's elapsed wall time and pass/fail
outcome in the cost ledger.
The compatibility script accepts `--check` without executing, uses `SUITE` when
nonblank, otherwise `POCKET_BROWSER_BIN=/usr/bin/google-chrome npm test`, and
returns the child's status. Preserve the compatibility queued/started/finished
log lines and history file at `PDD_VM_SUITE_LOCK.history`, else
`HOME/.local/state/pdd/vm-suite/fullsuite.lock.history`. An explicit legacy lock
path still needs an existing writable parent; the default log parent is created. No GitHub writes, private paths or live agent calls.

Both VM scripts preserve a nonempty caller `PDD_STATE_DIR`. Otherwise they set
it to `PDD_SUITE_QUEUE.state` when a nonempty queue selector is supplied, or
`LOCK.queue.state` beside the resolved compatibility lock (including its default).
This is the caller state for durable validation logs, separate from the temporary
child state below. Retain these logs after suite cleanup, including nonzero exits.
Without a caller state override, an external lock and queue keep both scripts
from writing into the caller HOME; legacy history remains beside the selected lock. `--check` creates no validation
logs. Factory and test callers must keep their state inside their disposable
fixture; tests of the HOME state fallback may use their private HOME explicitly.

## Clean suite environment

Admission uses the caller's queue selectors and machine ports. Execution must
not inherit the agent session or its configuration. After admission, allocate
one private temporary directory under the queue root, with separate empty
`home`, `state`, `config`, `tmp` and `interpreter-queue` directories. Set `HOME` and `USERPROFILE` to
home, `PDD_STATE_DIR` to state, `XDG_CONFIG_HOME` to config and `TMPDIR`, `TMP`
and `TEMP` to tmp. Set `PDD_INTERPRETER_QUEUE` to interpreter-queue. Remove this directory after execution settles, including a
nonzero exit, timeout or execution error. Native execution settles only after
its child group is stopped. Never remove the caller's folders.

If setup fails before calling the execution port, no child can own the admitted
slot. Mark that ticket finished with `finishedAt` and a failure `reason`, return
exit code 1, release its capacity and remove any allocated private directories.
This includes failure to create the temporary root or any private subdirectory.
Once execution has been called, a rejection releases the slot only when a
reported child group is confirmed dead. A missing child PID after that call is
uncertain ownership and must retain the reservation.

Build the child environment from an allowlist: caller `PATH` (fallback
`/usr/bin:/bin`), `LANG`, `LANGUAGE`, `LC_*`, `TZ`, `TERM`, `CI`, `SystemRoot`
and `WINDIR` when supplied. Set `POCKET_BROWSER_BIN` to the caller's value or
`/usr/bin/google-chrome`, as for the VM suite. Include the assigned
`PDD_CHECK_CPUS`. All other inherited variables are absent, including
`CODEX_HOME`, `PDD_AUTOPILOT_CONTEXT`, `HERDR_*`, agent credentials, session and
config variables, caller interpreter queue overrides, `NODE_OPTIONS`, `BASH_ENV` and
npm configuration. A command can explicitly set its own needed variables.
Execute the supplied command unchanged. Preserve cwd, status, timeout and CPU affinity;
saved and forwarded evidence follows Durable validation evidence below.
Do not change the parent environment.

Store `environmentPolicy: "clean-v1"` on each new ticket, including its finished
receipt. This identifies this rule without recording environment values, private
directory names or secrets. Older tickets without the field remain readable.
The compatibility entrypoint uses the same policy, so the same synthetic suite
has the same result from a clean caller and an agent caller. Offline proof uses
real CLI children, a controlled suite and fake machine capacity; no live agents.

## Durable validation evidence

Before native validation starts, save `command`, `commandFingerprint`, `cwd`, `source`,
`logPath`, `receiptPath` and recorder ownership on the ticket. `source` has
`head` (Git commit or null), `fingerprint` (SHA-256 of Git-visible tracked changes and
untracked file contents across the whole checkout, even from a nested cwd, or null), `runId` (matching workflow run identity or
null), `issue` (matching issue number or null), and `error` (unavailable source
reason or null). Source identity describes the start; it does not authorize a
merge or prove the checkout stayed unchanged. Keep each attempt separately.
Store receipts with mode 0600 in the private queue directory. Store bounded logs
with mode 0600 under the caller's user state folder (PDD_STATE_DIR, otherwise
HOME/.local/state/pdd), in a validation subfolder unique to the queue.
Each log name combines the queue-path hash, ticket and a random attempt ID.
Keep exclusive creation and retry with a fresh attempt ID if a file exists.
Queue resets and reboots must not reuse or overwrite retained logs or block a
new attempt on an existing file.
Commands can contain unrecognizable positional secrets. Save `command` as
`[redacted]` and `commandFingerprint` as the SHA-256 hex digest of the original
UTF-8 command; execute the original only in memory. The fingerprint identifies
an attempt without storing command values. Use the one-shot SHA-256 content
digest API for this command fingerprint; it is an attempt identifier, not a
password verifier or a password storage scheme. Preserve its lowercase hex
representation and original UTF-8 input bytes. Do not reconstruct the command.

Before any durable write, redact every receipt string and stdout/stderr using
[shared secret redaction](secret-redaction.prompt.md). Its exact-value guarantee
covers the child-visible credentials defined by that shared threat model.
Transfer the known inventory to the detached recorder only in memory over IPC;
do not pass it into the clean suite environment. Apply exact-value stream
redaction before line handling, pattern matching or clipping. Use separate
bounded overlap windows for stdout and stderr, including values containing LF
and values spanning transport, line and overflow boundaries.

Pattern-based redaction is a best-effort extra layer. It cannot guarantee removal
of unknown formats, encodings or positional secrets. Buffer sanitized streams
until a complete line or EOF. `MAX_EVIDENCE_LINE_BYTES = 262144` bounds each
pending line. Suppress an oversized line in full, including its continuation,
and emit a marker with its exact raw byte count at its newline or EOF. Scan raw
bytes too: discarding them must not discard bounded pattern recognition state.
Keep pending assignment fields and Basic/Bearer schemes across whitespace,
including LF and omitted lines. Suppress their following value before storage
or forwarding. While a quoted secret or private key remains open, suppress
continuation lines through the closing delimiter (or EOF). Escaped quotes do
not close a value. Continue recognizing later openers after a delimiter,
including on discarded lines. Resume ordinary output on the next safe line.
Neither a long line nor pattern value may require unbounded retained raw text.
The exact-value overlap bound depends on the longest known secret. Forward
only sanitized output, after saving it. Redact setup, source, custody and
output-save errors too. Preserve raw byte counts independently of redaction.

`MAX_VALIDATION_LOG_BYTES = 1048576` bounds each saved log, including markers.
Keep full sanitized output within that limit. On overflow retain the first and
last `(MAX_VALIDATION_LOG_BYTES - 128) / 2` bytes of sanitized output and a clear
`N bytes omitted` marker. Never append beyond the budget, even temporarily.
The receipt's `evidence` is `{outputBytes, logBytes, omittedBytes, truncated}`:
`outputBytes` counts all raw stdout/stderr bytes; `logBytes` is the saved file
size; `omittedBytes` counts bytes removed by oversized-line suppression plus
sanitized bytes removed by log overflow (ordinary secret replacement is not
counted); `truncated` is true if either omission occurred. Byte slicing may use
UTF-8 replacement characters only if the final encoded log still fits its bound.
Parse counts from the original complete stream independently of retention.

`MAX_VALIDATION_RECEIPT_BYTES = 65536` bounds every serialized ticket, including
intermediate and temporary writes. `MAX_RECEIPT_TEXT_BYTES = 4096` bounds each
free-text `reason` and source `error`, `runId` and string `issue`, with an explicit
omission marker. Preserve fixed source hashes, ownership, paths, counts and
result fields. If required metadata alone cannot fit, fail closed before a
command starts; never truncate ownership or source hashes or delete earlier
attempts to make room. After admission, an evidence-save failure retains the
last saved custody and reports failure or unknown, never a fabricated success.
Keep earlier tickets and their individually bounded logs. This is a per-attempt
budget, not an aggregate history-retention quota.

The detached recorder is the execution custodian. Save `recorderPid` and
`recorderIdentity` (Linux process start ticks, or null when unavailable) before
it receives permission to start. The recorder saves `childPid` before releasing
the child command's start gate. No validation command may run if this save fails.
Save bounded, sanitized stdout/stderr evidence at `logPath` before forwarding it to the caller.
A closed caller must not stop recording or cause a resend. On completion, stop
owned descendants, drain output, remove the owned temporary environment, and
atomically save the terminal receipt before returning or forwarding completion.

Receipts and `readSuiteProgress` expose the added fields above plus `exitCode`
(integer or null), `signal` (termination signal or null), `outcome` (`running`,
`completed`, or `unknown`), and `counts` (null without a complete TAP summary,
else `{tests, suites, pass, fail, cancelled, skipped, todo}`, each a nonnegative
integer). Parse only a complete final top-level stdout TAP summary after a TAP 13 header
and a top-level plan. Later non-summary output or an unfinished final line
invalidates that count receipt; a duration line and blank lines may follow. Missing or
incomplete counts stay null; exit zero alone is not a test-count receipt.
Preserve nonzero status and the same bounded evidence policy for nonzero output too. The native CLI announces receipt/log locations after registration and before
completion, so terminal truncation cannot hide them. The compatibility entrypoint
sets the `announceReceipt: false` port to preserve its lifecycle-only stdout; its
receipts and logs remain available through the queue. Default this port to true.
Older records without evidence fields remain readable and provide null values.

A later process observes the same ticket and recorder through the shared queue.
A live recorder keeps custody even after its original caller dies. An identity
mismatch is not proof that the recorder still owns that PID. If neither recorder
nor suite group is live, report `outcome: unknown`, `exitCode: null` and unknown
counts unless a terminal receipt exists. Do not invent an exit, infer failure
causes from output tails, repeat an uncertain command, or signal a recovered PID.
Live or uncertain descendants retain their slot. Status remains read-only.
Native timeout and explicit caller SIGINT/SIGTERM cancel through the recorder;
unexpected caller loss leaves the recorder working to its original timeout.
All process and source observations have injectable ports. Native process-group
signaling applies only to a child started by that executor.

## Machine capacity

Own the capacity rule for full suites and full builds. Preserve queue ordering,
ownership, cleanup and paused intervals. Inject `cores()` (ordered usable CPU ID
array), `memory()` (free bytes), `load()` (one-minute load), `platform` (OS name),
`battery()` and `virtualized()` (Booleans), and `taskset()` (absolute executable path or null).
Native Linux cores come from the current affinity list, with available parallelism
as fallback. Native battery detection reads power-supply types; taskset discovery
searches PATH for an executable. Native Linux virtualization detection runs
`systemd-detect-virt --quiet` with a one-second timeout through an injectable
`spawnSync` port. Only exit zero establishes a VM or container. Missing detection,
timeout or any other result conservatively reserves personal-machine capacity.
These adapters make no AI calls.

`calculateCheckCapacity({checks, runs, autopilotLoad}, ports)` returns
`{cores, usableCores, cpuIds, freeMemory, load, autopilotLoad, outsideLoad,
personal, affinity, taskset, calculatedChecks, checks, calculatedRuns, runs,
coresPerCheck, busy}`. Counts are positive integers; memory
is bytes, load is a nonnegative number, CPU IDs are unique nonnegative integers,
personal/affinity/busy are Booleans, taskset is a path or null. Invalid observations
fail closed before admission. Overrides are positive safe integers when supplied.

Personal means macOS, or Linux with a battery or without established virtualization.
This includes Linux desktops without batteries; detected Linux VMs and containers
without batteries retain the full machine budget. Use the first max(1, floor(cores/2))
CPU IDs on a personal machine, else all IDs. Let U be this usable count and M be
free bytes. Machine observations affect check concurrency and each check's CPU
share; they do not change issue eligibility. `autopilotLoad` is the explicitly supplied count of CPU cores reserved by
verified Autopilot-owned running suites, from the input, shared resources or
injected port; its default is zero. Do not infer it from all running queue
tickets. The queue includes operator and worker suites that do not carry trusted
Autopilot provenance. Let `outsideLoad = max(0, load - autopilotLoad)` be
measured machine load not already represented by those verified reservations. Let `A = max(0, U - outsideLoad)` be the usable
cores remaining after outside work. Calculated slots are
`max(1, min(floor(A/12), floor(M/4294967296)))`, so high outside load reduces
Autopilot's check slots for that tick instead of overloading the machine.
Without Linux taskset, cap calculated slots at one, since an env hint cannot
constrain tools which ignore it. Explicit checks replaces calculated slots.
Calculated open runs are twice the chosen slots, capped at the largest safe integer; explicit runs replaces this.
Each check gets max(1, floor(U/chosen slots)) CPUs. Busy means load > U; equality
admits. A busy machine admits no new heavy work. Running checks are not killed
when capacity falls. The next tick refreshes observations and shared capacity.

`configureCheckCapacity({env, checks, runs, owner}, ports)` computes and atomically saves
this snapshot as `capacity.json` under the shared queue admission lock and returns
it with `owner` (the launcher state-file identity, or null), `observedAt` and
`expiresAt` (epoch milliseconds). Snapshots expire 31 minutes after observation,
so a stopped or lost timer cannot hold busy state or an override forever.
Admission ignores an expired snapshot and probes the machine with default limits.
`releaseCheckCapacity({env, owner}, ports)` removes only the matching owner's
snapshot under the admission lock and returns whether it removed one. Missing
snapshots are harmless; another active repository's snapshot remains. Running
tickets are never removed. `readCheckStatus({env, checks, runs}, ports)` reads the
same capacity used by admission without writing and adds machine-wide
`busyChecks` and `waitingChecks` ticket counts. The optional checks/runs arguments
are accepted for compatibility but do not override the active shared limits.
A valid unexpired snapshot wins even after a resize or from a different repository;
absent or expired snapshots use current machine observations with default limits.
Status retains the snapshot's original core count and personal classification.
An unavailable observation or record read throws for the caller to report.
Queue admission uses the saved snapshot when present, otherwise computes from
ports. A malformed snapshot fails closed. This machine-wide snapshot is shared
across repositories; the most recent active tick supplies its selected override.

`readAutopilotSuiteLoad({env, coordinatorId, machine}, ports)` is the native observation for the current launcher. It reads the same shared queue records and considers only running tickets. For each candidate, read the saved workflow status for the ticket cwd. Count its `coresPerCheck` only when that status proves an automatic origin with this exact coordinator ID and machine. Sum these recorded CPU reservations; do not estimate CPU load from a ticket count or process count. A missing, malformed, ambiguous, manual, operator, worker, transferred, or different-coordinator status proves no owned reservation, so it remains measured outside load. An unavailable queue or run-status read returns zero owned load, which keeps all observed load outside. The reader is read-only and does not change ticket, run, queue, or process state.

On Linux with taskset, allocate a free, disjoint list from the current usable CPU
IDs for each slot; store it as `cpuIds` on the running ticket. Existing tickets
without this field keep their slot; new affinity admissions wait until those
unknown CPU allocations finish. Capacity shrink waits for disjoint IDs without
changing existing checks. If an override exceeds usable cores, extra slots wait
for CPUs rather than share a CPU list. Always replace child `PDD_CHECK_CPUS` with
the share. Native execution uses taskset `--cpu-list LIST /bin/bash -c COMMAND`
when available, else bash with the hint only. Inject the process `spawn` port into
native execution; the timeout and signal cleanup still own its process group.
Offline regressions provide every machine port and inject the native execution
spawner. They must verify the reserved CPU share, taskset arguments, child
environment and finished ticket without reading host CPU IDs, discovering native
tools or skipping for host capacity. A separate boundary check refuses native
machine observations while executing the public affinity regression.

Serialize ticket creation and admission with
the existing PID/token lock semantics. Preserve submission order among waiting
tickets, including equal clock times; every waiter ahead contributes to position.
Do not hold admission ownership during a suite or a wait. All test commands,
including custom full suites, run in the supplied cwd with closed stdin and the
clean environment below. Preserve child stdout/stderr under the evidence policy and preserve nonzero status. A running suite
has a bounded timeout; terminate its process group before releasing its slot.
Timeout returns 124 with a suite-specific reason. On SIGINT/SIGTERM, terminate
running descendants and release only after termination. Dead waiters do not block
the queue. A dead runner with a live or uncertain suite keeps its slot and reports the
interrupted runner with uncertain descendant ownership as its reason. Never kill
an unrelated process or reclaim a live or uncertain owner. Unknown or unreadable
queue ownership fails closed; it cannot admit extra suites.

Persist waiting, running and completed records atomically outside the checkout.
Retain the evidence fields owned by Durable validation evidence and the lifecycle
fields: ticket, owner PID, child PID when known, cwd, state, timestamps,
failure reason, assigned CPU IDs (`cpuIds`), share (`coresPerCheck`), taskset path and `environmentPolicy`. Never record inherited environment values. Report changed queue
positions as `waiting for a check slot (position N)`, including full builds
and waits on a busy machine. Autopilot reports the shared
work as check slots. Retain completed intervals
so the stuck clock excludes queue wait and suite execution after restart. Status
is read-only and must not mutate workflow state or touch a live chat. A successful
suite resumes the prior stuck clock, rather than consuming it. A suite failure,
timeout or interrupted runner has its own reason; it is not a stuck issue.

`configureCheckCapacity` accepts optional input `resources`, the current shared
machine observation. Use its load and available memory with its check profile
and verified `autopilotLoad` for capacity; do not read the host again. Legacy
observations without check metadata retain injected check adapters for affinity.
come from the machine resource owner.

## Dependencies

- [Secret redaction](secret-redaction.prompt.md): required shared rules for every
  persisted receipt string and captured output, also used by agent guide.

- [Cost ledger](cost-ledger.prompt.md): required shared rules for recording
  completed suite durations and reading the repository's learned suite time limit.

- [Machine observations](machine-resources.prompt.md): required shared native readers
  and tick observation shape for machine-sized checks.

- [Native admission lock](workflow-runner.prompt.md#native-admission-lock): only this
  independent interface selection is required context, supplying
  `acquireRunLock` for PID/token admission ownership. No runner execution policy
  is loaded by this selection.
- Native Node filesystem, OS, child process and clock facilities implement ports.
- Inject `fs`, `now`, `sleep`, `alive(pid)`, `acquireLock(directory)`,
  `execute(command, {cwd, env, timeoutMs, onChild})`, `pid`, `uuid()` (temporary-file identity), `queueRoot`, and
  `say(text)`, `source(cwd)` (the source shape above), `git(args, cwd)` (a
spawnSync-shaped local Git result), `processIdentity(pid)` (start ticks or null),
and `stdout`/`stderr` write ports to fake outside effects. Execute resolves `{exitCode, reason}` and
  calls `onChild(pid)` before awaiting the suite. Native defaults handle signals
  and process-group termination. Status uses the same filesystem, clock and PID
  liveness ports; an unavailable queue read is explicit, never idle evidence.
