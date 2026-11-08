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

Export native port adapter `executeSuite(command, {cwd, env, timeoutMs, onChild, cpuIds, taskset}, ports = {})`,
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

`calculateCheckCapacity({checks, runs}, ports)` returns `{cores, usableCores,
cpuIds, freeMemory, load, personal, affinity, taskset, calculatedChecks, checks,
calculatedRuns, runs, coresPerCheck, busy}`. Counts are positive integers; memory
is bytes, load is a nonnegative number, CPU IDs are unique nonnegative integers,
personal/affinity/busy are Booleans, taskset is a path or null. Invalid observations
fail closed before admission. Overrides are positive safe integers when supplied.

Personal means macOS, or Linux with a battery or without established virtualization.
This includes Linux desktops without batteries; detected Linux VMs and containers
without batteries retain the full machine budget. Use the first max(1, floor(cores/2))
CPU IDs on a personal machine, else all IDs. Let U be this usable count and M be
free bytes. Calculated slots are max(1, min(floor(U/12), floor(M/4294967296))).
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
Record only ticket, owner PID, child PID when known, cwd, state, timestamps,
failure reason, assigned CPU IDs (`cpuIds`), share (`coresPerCheck`) and taskset path, never the command, environment or output. Report changed queue
positions as `waiting for a check slot (position N)`, including full builds
and waits on a busy machine. Autopilot reports the shared
work as check slots. Retain completed intervals
so the stuck clock excludes queue wait and suite execution after restart. Status
is read-only and must not mutate workflow state or touch a live chat. A successful
suite resumes the prior stuck clock, rather than consuming it. A suite failure,
timeout or interrupted runner has its own reason; it is not a stuck issue.

`configureCheckCapacity` accepts optional input `resources`, the current shared
machine observation. Use its load and available memory with its check profile
for capacity; do not read the host again. Legacy observations without check metadata
retain injected check adapters for affinity. Native synchronous fallback adapters
come from the machine resource owner.

## Dependencies

- [Machine observations](machine-resources.prompt.md): required shared native readers
  and tick observation shape for machine-sized checks.

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
