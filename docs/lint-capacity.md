# Waiting for runtime capacity

`pdd check`, `pdd check --lint` and `pdd try` wait and retry when the server confirms that
lint did not start and marks the capacity refusal retryable. The message is:

> The server is busy. Waiting for a lint slot…

Pdd waits through confirmed capacity refusals until the caller deadline, without an attempt-count ceiling. It keeps every request ID and the same selected files.
It honors Retry-After first, then the server retry delay (1 through 300 seconds, default five), between attempts. Lint shares the caller's wait: Check and remote lint honor `--timeout`, otherwise an agent waits 90 seconds and a terminal Check has no limit. Try keeps its existing five-minute setup allowance and 90-second agent default.

If capacity stays unavailable, pdd says that the server stayed busy, no checks ran, and to run
the same command again later. Check and lint return exit 5; Try doors use their wrapper exit 125.
No AI check or Try is submitted before lint succeeds. Lint uses zero AI calls.

A lost answer is different: pdd reads the original ID and never sends it again while its outcome
is uncertain. A new attempt needs a confirmed retryable capacity refusal. Input/schema refusals
need a correction, and unknown results keep their read-only recovery. Ctrl-C stops further sends.

If an accepted lint is still queued or running when the wait ends, pdd says so and exits 3.
No check or Try was sent, and check calls are zero. Queue time, backoff and lint work share
the same wait budget. Check and explicit lint print a saved batch to read with
`pdd check --read BATCH`; this reads the original lint without repeating lint; a saved normal Check may continue its original held checks after lint passes, with identical source, owner and call ceilings. Standalone lint reads send no checks.

A later read replaces pending or unknown wording with the saved lint result. It
shows a reached prompt refusal when one exists. After lint passes, a saved normal Check may continue only its proven never-posted held rows. Recovery authenticates the saved owner, recaptures the original selected source, preserves call ceilings and the saved runtime origin, and uses a fresh finite wait (`--timeout`, otherwise 90 seconds). A permanent exclusive dispatch claim preserves each check ID across concurrent or interrupted recovery. Standalone lint, ambiguous legacy intent and posted or uncertain jobs never authorize another check. A global lint refusal still names its diagnostics. Lost or mismatched
replies remain unknown; pdd never treats them as a pass.

Checks, remote lint and new Try setup first share local slots across pdd processes, repositories and worktrees. `PDD_MAX_JOBS` defaults to 4; invalid values warn and use 4. One ticket per waiting job preserves oldest-first order. Progress shows busy slots and jobs ahead. `pdd jobs` reads active and waiting local records without contacting the runtime or signing in.

Reservations live under `$PDD_STATE_DIR/slots/<runtime host>/` (default state directory `~/.pdd/runtime`), with the host and optional port safely encoded as a path component. A pending or uncertain dispatched job retains its reservation after a command stops waiting. A dead owner's slot is reusable only after all recorded jobs are confirmed ended, or after 30 minutes. Process death alone does not mean the runtime job ended.

Before submission, pdd reads authenticated runtime capacity. A future maintenance window prints its end and reason, waits and rechecks; a confirmed not-started `503 maintenance` is handled the same way. A capacity endpoint returning 404 uses admission response codes for compatibility. Other authentication, access and service errors keep their existing behavior. Accepted queued jobs keep their IDs; progress uses the runtime's supplied queue place and slot counts.

Only a confirmed same-ID terminal check ending `unknown` with `service-restarted` authorizes one replacement attempt for that original Story row. The allowance persists across reads/retries, with an exclusive claim preventing concurrent replacements. Both IDs, receipts and usage remain saved. Other unknowns and paid Try actions never get an automatic replay.
