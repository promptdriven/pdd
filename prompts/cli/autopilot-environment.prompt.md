# Environment validation recovery

Own `src/autopilot-environment.mjs`. Preserve work and interpreter decisions. This
module classifies stops and supplies read-only host admission for validation
retries. It never runs tests, writes queue records, approves work or sends checks.

Export `classifyStuckCause(reason, runtime = false)`, returning `environment`,
`interpreter` or `work`. An explicit runtime wait wins. Unknown/no-verdict
interpreter outcomes and saved-batch reconciliation stay interpreter work. Real
failing tests or assertions (including plural, past-tense and failure-count
reports), must-fix reviews, unresolved assertions or decisions win over
resource words in a mixed reason. Explicit native infrastructure stalls/timeouts,
filesystem journal I/O, disk or memory pressure, killed/cancelled/incomplete native
test processes, full suite queues and missing tools are environment causes.
Other causes are work. Do not infer infrastructure from a failing test alone.
Treat failure wording associated with tests, checks, suites, validations or
expectations as work regardless of word order; ambiguous failures fail closed.

Export frozen `ENVIRONMENT_BACKOFF`: delays in milliseconds of 15 minutes,
1 hour and 4 hours. Export `environmentRecovery(run)`: null unless an automatic
run is stuck for an environment cause without a saved `repairLimit` or
`integrationLimit` under the [runner's budget policy](workflow-runner.prompt.md#autopilot-repair-ceiling). Require its saved
`environmentRetry` with an explicit validation target, valid current area, finite
failure time, integer attempts 0..3 and a finite nextAt below the limit (null at
the limit). Never guess a failed step from unfinished steps in legacy records.
Absent or malformed retry evidence means no automatic retry.
The recovery shape is `{at, reason, step, area, attempts, nextAt}`: epoch millisecond
times, original cause, validation step name, area index, delivered attempt count
0..3, and next retry time (null at the limit). Retain attempts when the same area
and step fails again, even if the cause text changes. A new validation target has
its own budget. Export `environmentStatus(run)`: null outside this recovery;
otherwise a single line with cause class, cause and `retrying after environment
failure (attempt N of 3, next at ISO)` or exhaustion. N is the next attempt while
waiting; after delivery the run is running and has no retry-wait status.
Export `environmentWakeTag(retry)`: `Environment validation wake for AREA:STEP at ISO attempt N.`
with the failure time and next attempt. This is a per-failure delivery identity.

Export async `environmentHealthy({env, reason, cwd}, ports = {})`, returning boolean.
Machine reads use the shared `machineResources({cwd})` port from the dependency
below. Use the supplied checkout cwd, falling back to `ports.cwd` then the process
cwd for standalone callers. A caller may supply its current observation through
that port; apply retry policy to it without another machine read.
Legacy injectable `readFile`, `readDir`, `load`, `cpuCount`, `memory`,
`toolPresent`, `alive` and `suiteAvailable` ports remain supported for retries.
Fail closed on malformed or unavailable observations. Healthy means one-minute
load per CPU below 1, available memory at least 10%, Linux I/O and memory PSI
`some avg10` below 10%, and suite capacity available. Read `/proc/meminfo` for
available memory; on systems without proc use OS free memory and no PSI. An absent
Linux PSI file is unknown. A missing-tool stop also requires that exact tool now
be executable on PATH; an unidentified missing tool cannot retry.

Optional shared suite queue integration is read-only and does not require #3056.
Observe its `ticket-*.json` records at absolute PDD_SUITE_QUEUE, else
PDD_VM_SUITE_LOCK plus `.queue`, else `/tmp/pdd-full-suite-UID`. No directory means
no queue restriction; unreadable or malformed records block. A waiting ticket
or enough effectively running tickets to fill the current shared check capacity
blocks admission. Use optional `suiteLimit` from the current tick, else the queue
status reader. Legacy custom queue-file ports without a supplied limit retain
the three-slot fallback. Invalid or unavailable capacity blocks admission. Use the queue's
read-only effective ownership rule: a waiting ticket with a confirmed-dead runner
is finished for capacity; a running ticket is finished only when both its runner
and its saved descendant process group are confirmed dead. Probe the runner with
its positive PID and the group with negative childPid through `alive(pid)`. The
native probe uses signal zero: only ESRCH means dead; all other errors mean
unknown and block. A missing or invalid childPid cannot prove a running ticket
finished. Live or unknown descendants retain their slot. Do not write, delete or
reclaim records, including records treated as effectively finished. This
is a preflight only: the actual suite command must still use its normal queue
admission, since another process can take the slot after this read.

Native tests using synthetic queue tickets must supply `alive` observations.
Capacity and malformed/unreadable queue cases must not depend on whether their
synthetic PIDs exist on the host or whether the host permits probing them.

Export async `machineHealth({cwd}, ports={})` for the no-AI tick, returning
`{healthy, causes, resources}`. `resources` is the shared machine observation;
`causes` is an ordered string array: memory then disk. Require valid available
memory >=10% of total and valid available disk >=1 GiB AND >=5% of total.
Equality passes. Unknown or malformed values block with a fixed safe cause.
No suite queue, load or PSI restriction applies to ordinary admission; those
restrictions remain validation-retry policy. `environmentHealthy` uses the same
machine admission decision (including disk) and shared machine reader before
applying retry-only load, pressure, tool and queue restrictions.

## Dependencies

- [Shared suite queue](test-suite-queue.prompt.md): required native capacity
  observation for retry preflight. Reads never grant suite execution admission.

- [Machine observations](machine-resources.prompt.md): required native generation
  and verification context for CPU, memory, pressure and disk reads.

Node filesystem and OS adapters supply bounded local host observations. No hosted
interpreter binding is declared; native tests cover the public module boundary.
