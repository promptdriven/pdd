# Waiting for a lint slot

`pdd check`, `pdd check --lint` and `pdd try` wait and retry when the server confirms that
lint did not start and marks the capacity refusal retryable. The message is:

> The server is busy. Waiting for a lint slot…

Pdd makes at most three lint attempts. It keeps each request ID and the same selected files.
It waits for the server's retry delay, usually five seconds, between attempts. Lint shares the caller's wait: Check and remote lint honor `--timeout`, otherwise an agent waits 90 seconds and a terminal Check has no limit. Try keeps its existing five-minute setup allowance and 90-second agent default.

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
