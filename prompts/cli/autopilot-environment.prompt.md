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
run is stuck for an environment cause without a repair ceiling. Require its saved
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

Export async `environmentHealthy({env, reason}, ports = {})`, returning boolean.
All host observations are behind `readFile`, `readDir`, `load`, `cpuCount`,
`memory`, `toolPresent` and `suiteAvailable` injectable ports, with native defaults.
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
or three running tickets blocks admission. Never reclaim stale ownership. This
is a preflight only: the actual suite command must still use its normal queue
admission, since another process can take the slot after this read.

## Dependencies

Node filesystem and OS adapters supply bounded local host observations. No hosted
interpreter binding is declared; native tests cover the public module boundary.
