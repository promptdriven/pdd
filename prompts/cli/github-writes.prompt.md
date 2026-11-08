# Shared GitHub write budget

Own `src/github-writes.mjs`. Count and admit Autopilot content writes across
repositories and processes on one machine, per GitHub host and authenticated
identity. Preserve the existing read budget and workflow authority. This is a
local guard, not a distributed lock or permission to write.

## Public boundary

- `githubWriteCost(args, options={})` returns a conservative integer count of
  content requests. REST GET/HEAD/OPTIONS and GraphQL queries cost zero. REST
  mutations cost one. GraphQL documents containing any mutation reserve conservatively for all
  mutation fields, even when the document starts with a query. Ambiguous
  documents are never classified as free reads. Unparseable input costs one.
  Accept gh compact and equals method/field option spellings. Known gh read commands
  cost zero. High-level gh writes reserve conservative request counts, including
  each label operation; unknown commands reserve one. Never use the purpose tag
  to decide whether an operation writes. A POST GraphQL query is a read.
- `githubWriteBudget({root, identity, host='github.com', fs, now, machine})`
  returns `{reserve(count), observe(outcome), observeClaims(repository,claims),
  usage()}`. `fs` is the synchronous file port, `now` a millisecond clock;
  native defaults use node:fs, Date.now and hostname. Identity is a login or App
  identity supplied by the caller; case is ignored. Unknown identities use one
  shared conservative bucket. No token is stored or printed.
- `githubWriteThrottle(outcome)` returns `{retryAfter}` for a secondary throttle,
  else `null`. `retryAfter` is the Retry-After header text, or `undefined`.
  An HTTP status line at the start of stdout selects the actual response status;
  only 403/429 with a Retry-After header or a secondary/abuse limit report qualify.
  Read Retry-After only from that response's headers. Without response headers,
  require an HTTP 403/429 gh diagnostic in stderr and secondary/abuse wording
  or Retry-After guidance there. An explicit successful exit never qualifies.
  Successful REST and GraphQL payloads, including
  issue and comment text about limits, never establish a throttle. This one
  classification governs both budget observation and the counter's lazy resolver.
- `reserve(count)` returns the current usage after reserving before dispatch.
  Zero makes no reservation. Failed and uncertain attempts consume their full
  reservation. Concurrent processes serialize read/check/save with an atomic
  host-wide PID lock. An unknown identity counts reservations from every
known identity on that host; a known identity also counts unknown reservations.
Both admission paths use the same lock so an identity lookup failure cannot
create a fresh allowance. A dead owner is reclaimable; a live or unreadable lock defers.
  Recovery must itself survive process death, including death before an owner
  record is complete. Competing recoverers must not remove a live replacement
  lock. Recovery records belong to unique attempts; discard only records whose
  process is dead. No unowned recovery sentinel may block later admission.
  Unreadable state and save failures stop writes. Never drop events on a race.
- `usage()` returns `{identity,host,minute,hour,minuteLimit,hourLimit,machines,
  retryAt,state}`, plus `unavailable:true` when state cannot be read. That
  status reports usage as unavailable rather than claiming zero use. An existing
  host lock also reports unavailable and deferred until admission recovers it
  or its owner releases it. Counts use rolling windows `now-window < at <= now`.
  Defaults are 60/minute and 350/hour, leaving 20/minute and 150/hour for people
  against the stated 80/500 limits. Divide both defaults by the active machine
  count, rounding down, with a minimum of one. Each distinct active machine in
  observed claims counts, plus this machine. Keep observations from all local
  repositories. A claim must be active with a server-derived lastSeen less
  than four hours old. Expired observations leave the divisor. Count all seen
  machines conservatively when their GitHub identity is unknown. These are
  observations, not knowledge of machines on unseen repositories.
- At a full window or a shared cooldown, `reserve` throws an Error with
  `code='github_write_budget'`, millisecond `retryAt`, and `usage`. No request
  runs. `retryAt` is the first expiry that admits the whole reservation, or the
  shared cooldown if later. Requests larger than a window cannot run. A live
  lock or storage fault also defers safely with this code. Do not sleep inside
  admission. The caller keeps progress and retries later.
- `observe(outcome)` shares a 403/429 cooldown when Retry-After is present, or a
  secondary/abuse limit is reported. Use Retry-After seconds or HTTP date; absent
  valid guidance, wait at least one minute. Preserve the original outcome and
  never retry an uncertain write automatically. Persist throttle observations
  independently of the reservation lock, so ordinary lock contention cannot
  lose a deadline. Admission takes the latest applicable deadline, including
  concurrent observations, with the same known/unknown identity sharing as
  reservations. Expired observations may be removed; an incomplete save must
  never replace a complete observation. Status includes identities known only
  through throttle observations.
- `githubWriteStatus(usage)` returns one plain status line with identity, rolling
  minute/hour counts, limits, machine count, state, and retry time when deferred.
- `githubWriteLock({directory,fs})` acquires a local process lock for a caller's
  named directory. Return a release function that removes only this attempt's
  record. Concurrent live owners exclude each other. A busy lock throws with
  `code='github_write_lock_busy'`; file faults propagate. Dead attempts cannot
  block acquisition or remove live attempts. No elapsed-time lease can evict a
  live owner. Use the injected file port and native process-liveness checks.

## Dependencies

The injected file port owns local persistence and locking. The process adapter
supplies identity and actual GitHub outcomes. The clock supplies milliseconds.
The call counter is a consumer, not required context. No network or model call is made by this module.
